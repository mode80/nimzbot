import macros
import options
import tables
import sequtils
import math

# {.experimental: "codeReordering".}
{. hint[XDeclaredButNotUsed]:off .}

type u8 = uint8
type u16 = uint16
type u32 = uint32
type u64 = uint64
type f32 = float32
type f64 = float64 # lazy Rust-like abbreviations

type Selection = u8
type Slot = u8
type Choice = u8
type DieVal = u8 

type SlotType = enum 
  ACES=1, TWOS, THREES, FOURS, FIVES, SIXES,  
  THREE_OF_A_KIND, FOUR_OF_A_KIND, FULL_HOUSE, 
  SM_STRAIGHT, LG_STRAIGHT, YAHTZEE, CHANCE

# -------------------------------------------------------------
# UTILS 
# -------------------------------------------------------------

macro `:=` (name, value :untyped) :untyped = newVarStmt(name, value)

proc set_to[T] (left :var T, right :Option[T] ) = 
  if right!=none(T): left=right.get

func as_long_as [T] (left :T, cond:bool) :Option[T] = 
  if cond: some(left) else: none(T) 

func unless [T] (left :T, cond:bool) :Option[T] = 
  if not cond: some(left) else: none(T) 

func factorial(n:int) :int= 
  if (n<=1): return 1
  return n * factorial(n-1)

# count of arrangements that can be formed from r selections, chosen from n items, 
# where order DOES or DOESNT matter, and WITH or WITHOUT replacement, as specified.
func n_take_r(n :int, r :int, order_matters :bool = false, with_replacement:bool = false) :int= 
  if (order_matters): # order matters; we're counting "permutations" 
    if (with_replacement): 
      return n^r
    else: # no replacement
      return factorial(n) div factorial(n-r) # this = factorial(n) when r=n
  else : # we're counting "combinations" where order doesn't matter; there are less of these 
    if (with_replacement) :
      return factorial(n+r-1) div (factorial(r)*factorial(n-1));
    else : # no replacement
      return factorial(n) div (factorial(r)*factorial(n-r));

proc combos_with_rep[T](lst: seq[T], k: int): seq[seq[T]] =
  if k == 0:
    @[newSeq[T]()]
  elif lst.len == 0:
    @[]
  else:
    lst.combos_with_rep(k-1).mapIt(lst[0] & it) 
    & lst[1..^1].combos_with_rep(k)

func distinct_arrangements_for [T] (dieval_seq :seq[T]) :f32 = 
    let key_counts = dieval_seq.toCountTable
    var divisor = 1
    var non_zero_dievals = 0
    for key, count in key_counts:  
        if key != 0:  
            divisor *= factorial(count)
            non_zero_dievals += count
    return f32( factorial(non_zero_dievals) / divisor )

#[

// returns a range which corresponds the precomputed dice roll outcome data corresponding to the given selection
func outcomes_range_for(_ selection :Selection) -> Range<Int>{
    let idx = RANGE_IDX_FOR_SELECTION[Int(selection)];
    let range = SELECTION_RANGES[idx]; // for @inbounds, see https://blog.tedd.no/2020/06/01/faster-c-array-access/
    return range;
} 

func print_state_choices_header() { 
    print("choice_type,choice,dice,rolls_remaining,upper_total,yahtzee_bonus_avail,open_slots,expected_value");
} 

// should produce one line of output kinda like ...
// D,01111,65411,2,31,Y,1_3_4_6_7_8_11_,119.23471
// S,13,66641,0,11,Y,3_4_5_9_10_13_,113.45208
func print_state_choice(_ state :GameState , _ choice_ev: ChoiceEV ) { 
    let Y="Y"; let N="N"; let S="S"; let D="D"; let C=","; // TODO hoist these to constants
    var sb:String=""; sb.reserveCapacity(60)
    if (state.rolls_remaining==0){ // for slot choice 
        sb += (S); sb+=(C);
        sb += (choice_ev.choice.description); // for dice choice 
    } else {
        sb+=(D); sb+=(C);
        sb+=("00000"+choice_ev.choice.description).suffix(5)
    }
    sb+=(C);
    sb+=(state.sorted_dievals.description); sb+=(C);
    sb+=(state.rolls_remaining.description); sb+=(C);
    sb+=(state.upper_total.description); sb+=(C);
    sb+=(state.yahtzee_bonus_avail ? Y : N); sb+=(C);
    sb+=(state.open_slots.description); sb+=(C);
    sb+=String(format: "%.2f", choice_ev.ev)
    print(sb);
} 

]#

# -------------------------------------------------------------
# DieVals
# -------------------------------------------------------------

type DieVals = u16 # 5 dievals, each from 0 to 6, can be encoded in 2 bytes total, each taking 3 bits

func init_dievals (self :array[5,int]) :DieVals = # construct a DieVals from an array of 5 DieVal types
  for i in 0..4:
    result = result or u16(self[i] shl (i * 3))

func `[]`(self :DieVals, i :int): DieVal = # extract a DieVal from a DieVals // TODO: try Nim bitset?
  assert i >= 0 and i < 5
  result = DieVal (self shr (i * 3)) and 0b111

iterator items (self :DieVals) :DieVal =
  for i in 0..4: 
    let val = (self shr (i * 3)) and 7
    yield val.DieVal

iterator pairs (self :DieVals) :(int,DieVal) =
  for i in 0..4: 
    let val = (self shr (i * 3)) and 7
    yield (i, val.DieVal)


# -------------------------------------------------------------
# SCORING FNs
# -------------------------------------------------------------

func score_upperbox (slot :Slot, sorted_dievals :DieVals) :u8 = 
  var sum :u8 
  for d in sorted_dievals:
    if d==slot: sum+=slot 
  return sum 

func score_n_of_a_kind(n :int, sorted_dievals :DieVals) :u8 = 
  var inarow=1; var maxinarow=1; var lastval=100.u8; var tot=0.u8; 
  for x in sorted_dievals:
    if x==lastval and x!=0.DieVal: inarow+=1 else: inarow=1 
    maxinarow = max(inarow,maxinarow)
    lastval = x
    tot+=x
  result .set_to tot .as_long_as maxinarow >= n  # TODO test performance of this sugar

func straight_len(sorted_dievals :DieVals) :u8 = 
  var inarow:u8 = 1 
  var lastval= uint8.high # stub
  for x in sorted_dievals:
    if x==lastval+1 and x!=0:
      inarow+=1 
    elif x!=lastval: 
      inarow=1 
    result = max(inarow, result)
    lastval = x

func score_aces  (sorted_dievals :DieVals) :u8 = score_upperbox(1,sorted_dievals)   
func score_twos  (sorted_dievals :DieVals) :u8 = score_upperbox(2,sorted_dievals) 
func score_threes(sorted_dievals :DieVals) :u8 = score_upperbox(3,sorted_dievals) 
func score_fours (sorted_dievals :DieVals) :u8 = score_upperbox(4,sorted_dievals) 
func score_fives  (sorted_dievals :DieVals) :u8 = score_upperbox(5,sorted_dievals) 
func score_sixes (sorted_dievals :DieVals) :u8 = score_upperbox(0,sorted_dievals) 
    
func score_three_of_a_kind(sorted_dievals :DieVals) :u8 = score_n_of_a_kind(3,sorted_dievals)
func score_four_of_a_kind(sorted_dievals :DieVals)  :u8 = score_n_of_a_kind(4,sorted_dievals)
func score_sm_str8(sorted_dievals :DieVals)         :u8 = (if straight_len(sorted_dievals) >= 4: 30 else: 0)
func score_lg_str8(sorted_dievals :DieVals)         :u8 = (if straight_len(sorted_dievals) == 5: 40 else: 0)

# The official rule is that a Full House is "three of one number and two of another
func score_fullhouse(sorted_dievals :DieVals) :u8 = 
 
  var valcounts1, valcounts2, j :int 

  for i, val in sorted_dievals:
    if val==0: return 0
    if j==0 or sorted_dievals[i]!=sorted_dievals[i-1]: inc j
    if j==1: valcounts1+=1
    if j==2: valcounts2+=1
    if j==3: return 0

  if (valcounts1==3 and valcounts2==2) or (valcounts2==3 and valcounts1==2): return 25 
  return 0 

func score_chance(sorted_dievals :DieVals) :u8 = 
  #foldr(sorted_dievals, a + b) # too much sugar for this 
  let dv = sorted_dievals
  return dv[0]+dv[1]+dv[2]+dv[3]+dv[4]
    
func score_yahtzee(sorted_dievals :DieVals) :u8 =
    let dv = sorted_dievals
    if dv[0]==dv[4] and dv[0]!=0: result = 50

# reports the score for a set of dice in a given slot w/o regard for exogenous gamestate (bonuses, yahtzee wildcards etc) 
func score_slot_with_dice(slot :Slot, sorted_dievals :DieVals) :u8 =
    case SlotType slot
    of ACES: return score_aces sorted_dievals 
    of TWOS: return score_twos sorted_dievals 
    of THREES: return score_threes sorted_dievals 
    of FOURS: return score_fours sorted_dievals 
    of FIVES: return score_fives sorted_dievals 
    of SIXES: return score_sixes sorted_dievals 
    of THREE_OF_A_KIND: return score_three_of_a_kind sorted_dievals 
    of FOUR_OF_A_KIND: return score_four_of_a_kind sorted_dievals 
    of SM_STRAIGHT: return score_sm_str8 sorted_dievals 
    of LG_STRAIGHT: return score_lg_str8 sorted_dievals 
    of FULL_HOUSE: return score_fullhouse sorted_dievals 
    of CHANCE: return score_chance sorted_dievals 
    of YAHTZEE: return score_yahtzee sorted_dievals 

when isMainModule:

  # test some stuff
  
  # Test for distinct_arrangements_for
  let dieval_seq = @[2, 2, 3]
  echo distinct_arrangements_for(dieval_seq) 
