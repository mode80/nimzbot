import macros
import options

# {.experimental: "codeReordering".}
{. hint[XDeclaredButNotUsed]:off .}

type u8 = uint8
type u16 = uint16
type u32 = uint32
type f32 = float32
type f64 = float64 # lazy Rust-like abbreviations

type Selection = u8
type Slot = u8
type Choice = u8
type DieVal = u8 

# proc `+`(a, b :DieVal) :DieVal {.borrow.} # imbue DieVal with addability 

# -------------------------------------------------------------
# Utils 
# -------------------------------------------------------------

## runnableExample:
##   result =? (tot, maxinarow >= n)
#TODO turn this into a macro that allows for:  X =? Y if X>0: else: X=1
#     https://dev.to/beef331/demystification-of-macros-in-nim-13n8 
proc set_maybe [T] (startval :var T, condval_cond: (T, bool) ) = 
  let (condval, cond) = condval_cond
  if cond: startval=condval

macro `:=` (name, value :untyped) :untyped = newVarStmt(name, value)

# a =? 0.iff 1==0 
# a =? 0.unless 1==0 

proc `=?` [T] (left :var T, right :Option[T] ) = 
  if right!=none(T): left=right.get

proc setTo [T] (left :var T, right :Option[T] ) = 
  if right!=none(T): left=right.get

func iff [T] (left :T, cond:bool) :Option[T] = 
  if cond: some(left) else: none(T) 

func unless [T] (left :T, cond:bool) :Option[T] = 
  if not cond: some(left) else: none(T) 


# -------------------------------------------------------------
# DieVals
# -------------------------------------------------------------

type DieVals = u16 # 5 dievals, each from 0 to 6, can be encoded in 2 bytes total, each taking 3 bits

func init (self :array[5,int]) :DieVals = # construct a DieVals from an array of 5 DieVal types
  for i in 0..4:
    result = result or u16(self[i] shl (i * 3))

func `[]`(self :DieVals, i :int): DieVal = # extract a DieVal from a DieVals // TODO: try Nim bitset?
  assert i >= 0 and i < 5
  result = DieVal (self shr (i * 3)) and 0b111

iterator items (self :DieVals) :DieVal =
  for i in 0..4: 
    let val = (self shr (i * 3)) and 7
    yield val.DieVal

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
    result = if maxinarow >= n: (tot) else: (0) 
    result.set_maybe (tot, maxinarow >= n)
    # result = tot unless (maxinarow>=n)

# straight_len(sorted_dievals) ::u8 = let
#     inarow=1 
#     lastval=254 # stub
#     maxinarow=1
#     for x in sorted_dievals 
#         if (x==lastval+1 && x!=0) 
#             inarow+=1 
#         elseif x!=lastval 
#             inarow=1 
#         end
#         maxinarow = max(inarow,maxinarow)
#         lastval = x
#     end  
#     maxinarow 
# end

# score_aces(sorted_dievals)      ::u8         = score_upperbox(0x1,sorted_dievals)   
# score_twos(sorted_dievals)      ::u8         = score_upperbox(0x2,sorted_dievals) 
# score_threes(sorted_dievals)    ::u8         = score_upperbox(0x3,sorted_dievals) 
# score_fours(sorted_dievals)     ::u8         = score_upperbox(0x4,sorted_dievals) 
# score_fives(sorted_dievals)     ::u8         = score_upperbox(0x5,sorted_dievals) 
# score_sixes(sorted_dievals)     ::u8         = score_upperbox(0x6,sorted_dievals) 
    
# score_three_of_a_kind(sorted_dievals)   ::u8     = score_n_of_a_kind(0x3,sorted_dievals) 
# score_four_of_a_kind(sorted_dievals)    ::u8     = score_n_of_a_kind(0x4,sorted_dievals) 
# score_sm_str8(sorted_dievals)           ::u8     = ifelse( straight_len(sorted_dievals) >= 0x4, 30, 0)
# score_lg_str8(sorted_dievals)           ::u8     = ifelse( straight_len(sorted_dievals) == 0x5, 40, 0)

# # The official rule is that a Full House is "three of one number and two of another
# score_fullhouse(sorted_dievals) ::u8 = let
   
#     valcounts1 = valcounts2 = 0
#     j=0

#     for (i,val) in enumerate(sorted_dievals) 
#         if val==0 return 0 end
#         if (j==0 || sorted_dievals[i]!=sorted_dievals[i-1]) 
#             j+=1 
#         end
#         if j==1 valcounts1+=1 end
#         if j==2 valcounts2+=1 end
#         if j==3 return 0 end
#     end

#     if valcounts1==3 && valcounts2==2 || valcounts2==3 && valcounts1==2 return 25 end
#     return 0 

# end 
    
# score_chance(sorted_dievals) ::u8 = sum(sorted_dievals) 
    
# score_yahtzee(sorted_dievals) ::u8 =
#     (sorted_dievals[1] == sorted_dievals[5] != 0) ? 50 : 0 

# # reports the score for a set of dice in a given slot w/o regard for exogenous gamestate (bonuses, yahtzee wildcards etc) 
# score_slot_with_dice(slot::Slot, sorted_dievals) ::u8 = let
#     if slot==ACES return score_aces(sorted_dievals) end 
#     if slot==TWOS return score_twos(sorted_dievals) end 
#     if slot==THREES return score_threes(sorted_dievals) end 
#     if slot==FOURS return score_fours(sorted_dievals) end 
#     if slot==FIVES return score_fives(sorted_dievals) end 
#     if slot==SIXES return score_sixes(sorted_dievals) end 
#     if slot==THREE_OF_A_KIND return score_three_of_a_kind(sorted_dievals) end 
#     if slot==FOUR_OF_A_KIND return score_four_of_a_kind(sorted_dievals) end 
#     if slot==SM_STRAIGHT return score_sm_str8(sorted_dievals) end 
#     if slot==LG_STRAIGHT return score_lg_str8(sorted_dievals) end 
#     if slot==FULL_HOUSE return score_fullhouse(sorted_dievals) end 
#     if slot==CHANCE return score_chance(sorted_dievals) end 
#     if slot==YAHTZEE return score_yahtzee(sorted_dievals) end 
# end

when isMainModule:

  # test some stuff
  # let dv = [1,2,3,4,5].init
  # for d in dv.items: 
  #   echo repr(d)

  a := 1
  b := 2

  a =? 0 .iff 1==0 
  echo a

  b.set_to 0 .unless 1==0 
  echo b

