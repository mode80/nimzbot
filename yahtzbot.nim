# include prelude
import macros
import options
import tables
import sequtils
import math
import algorithm

{.experimental: "codeReordering".}
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
type DieValsID = u8 

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


func n_take_r (n :int, r :int, order_matters :bool = false, with_replacement :bool = false) :int= 
    ## count of arrangements that can be formed from r selections, chosen from n items, 
    ## where order DOES or DOESNT matter, and WITH or WITHOUT replacement, as specified.
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


proc combos_with_rep [T] (list :seq[T], k: int): seq[seq[T]] =

    if k == 0:
        @[newSeq[T]()]
    elif list.len == 0:
        @[]
    else:
        list.combos_with_rep(k-1).mapIt(list[0] & it) & 
            list[1..^1].combos_with_rep(k)


func distinct_arrangements_for [T] (dieval_seq :seq[T]) :f32 = 

    let key_counts = dieval_seq.toCountTable
    var divisor = 1
    var non_zero_dievals = 0

    for key, count in key_counts: 
        if key != 0: 
            divisor *= factorial(count)
            non_zero_dievals += count

    return factorial(non_zero_dievals) / divisor 


func powerset [T] (set :seq[T]) :seq[seq[T]] =

    let count :int = 2^set.len # set_size of power set of a set with set_size n is (2**n -1)
    var i, j :int

    for i in 0..<count: # Run from counter 000..0 to 111..1
        var innerList = newSeqOfCap[T](count) 
        # Check each jth bit in the counter is set If set then add jth element from set 
        for j in 0..<set.len: 
            if (i and (1 shl j)) > 0: innerList .add set[j]
        result .add innerList
    return result

func unique_permutations (sorted_list :seq[int]) :seq[seq[int]] = 
    ## returns a seq of seqs, where each inner seq is a unique permutation of the input seq
    var list = sorted_list
    while list.nextPermutation:
        if not result.contains(list): result.add(list)

# -------------------------------------------------------------
# DIEVALS 
# -------------------------------------------------------------

type DieVals = u16 # 5 dievals, each from 0 to 6, can be encoded in 2 bytes total, each taking 3 bits


func init_dievals (self :array[5,int]) :DieVals = # construct a DieVals from an array of 5 DieVal types
    for i in 0..4:
        result = result or u16(self[i] shl (i * 3))


func init_dievals (self :openArray[int]) :DieVals = # construct a DieVals from an array of 5 DieVal types
    assert self.len == 5
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
    result .set_to tot .as_long_as maxinarow >= n    # TODO test performance of this sugar


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


func score_aces    (sorted_dievals :DieVals) :u8 = score_upperbox(1,sorted_dievals)     
func score_twos    (sorted_dievals :DieVals) :u8 = score_upperbox(2,sorted_dievals) 
func score_threes(sorted_dievals :DieVals) :u8 = score_upperbox(3,sorted_dievals) 
func score_fours (sorted_dievals :DieVals) :u8 = score_upperbox(4,sorted_dievals) 
func score_fives    (sorted_dievals :DieVals) :u8 = score_upperbox(5,sorted_dievals) 
func score_sixes (sorted_dievals :DieVals) :u8 = score_upperbox(0,sorted_dievals) 
        
func score_three_of_a_kind(sorted_dievals :DieVals) :u8 = score_n_of_a_kind(3,sorted_dievals)
func score_four_of_a_kind(sorted_dievals :DieVals)    :u8 = score_n_of_a_kind(4,sorted_dievals)
func score_sm_str8(sorted_dievals :DieVals)                 :u8 = (if straight_len(sorted_dievals) >= 4: 30 else: 0)
func score_lg_str8(sorted_dievals :DieVals)                 :u8 = (if straight_len(sorted_dievals) == 5: 40 else: 0)


func score_fullhouse(sorted_dievals :DieVals) :u8 = 
# The official rule is that a Full House is "three of one number and two of another
 
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
    
    let dv = sorted_dievals
    return dv[0]+dv[1]+dv[2]+dv[3]+dv[4] 

        
func score_yahtzee(sorted_dievals :DieVals) :u8 =
    let dv = sorted_dievals
    if dv[0]==dv[4] and dv[0]!=0: result = 50


func score_slot_with_dice(slot :Slot, sorted_dievals :DieVals) :u8 =
    # reports the score for a set of dice in a given slot w/o regard for exogenous gamestate (bonuses, yahtzee wildcards etc) 
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
    
#-------------------------------------------------------------
# INITIALIZERS etc 
#-------------------------------------------------------------

# DieValsID SORTED_DIEVALS [32767]; 

var OUTCOME_DIEVALS :array[1683,DieVals] 
var OUTCOME_MASKS :array[1683,DieVals] 
var OUTCOME_ARRANGEMENTS :array[1683,f32] 
var SORTED_DIEVALS :array[32767, DieValsID]

## These are index spans into the OUTCOME arrays above which correspond to each dieval selection.
## Each of the 32 indecis from 0b00000 to 0b11111 represents the dieval selection as a bitfield 
const SELECTION_RANGES = [(0, 1), (1, 7), (7, 13), (13, 34), (90, 96), (179, 200), (592, 613), 
    (34, 90), (96, 102), (200, 221), (613, 634), (102, 158), (221, 242), (634, 690), (263, 319), 
    (746, 872), (1005, 1011), (158, 179), (319, 340), (690, 746), (242, 263), (872, 928), (1011, 1067), 
    (340, 466), (928, 949), (1067, 1123), (1249, 1305), (466, 592), (949, 1005), (1123, 1249), 
    (1305, 1431), (1431, 1683)] # = cache_selection_ranges()   # TODO confirm these are correct

# func cache_selection_ranges() :seq[(u16,u16)] = #TODO confirm the order of the powerset corresponds to RANGE_IDX_FOR_SELECTION
#     ## this generates the ranges that correspond to the outcomes, 
#     ## within the set of all outcomes, indexed by a given selection 
#     var s :u16 = 0
#     let idxs0to4 = @[0, 1, 2, 3, 4]
#     let combos = powerset(idxs0to4)
#     result = newSeq[(u16,u16)](32) 
#     # the sequence below reorders the output of powerset such that the result index is also a bitfield for dice selection 
#     for i in [0,1,2,3,7,4,8,11,17,5,9,12,20,14,18,23,27,6,10,13,19,15,21,24,28,16,22,25,29,26,30,31] :
#         let count = u16( n_take_r(6, combos[i].len, 
#             order_matters=false, with_replacement=true) )
#         result[i] = (s, s+count,)
#         s+=count

proc cache_roll_outcomes_data() = 
    ## preps the caches of roll outcomes data for every possible 5-die selection (where '0' represents an unselected die) 
    var i = 0
    let idx_combos: seq[seq[int]] = powerset @[0,1,2,3,4] 
    assert idx_combos.len==32 
    let one_thru_six = @[1,2,3,4,5,6] 

    for idx_combo in idx_combos:
        var dievals_arr = [0,0,0,0,0] 
        let die_count = idx_combo.len 
        
        let combos = combos_with_rep(one_thru_six, die_count) 
 
        for die_combo in combos:
            var mask_arr = [0b111,0b111,0b111,0b111,0b111]
            for j, idx in idx_combo:
                dievals_arr[idx] = die_combo[j]
                mask_arr[idx]=0
            var arrangement_count = distinct_arrangements_for(die_combo)
            var dievals = init_dievals(dievals_arr)
            var mask = init_dievals(mask_arr)
            OUTCOME_DIEVALS[i] = dievals
            OUTCOME_MASKS[i] = mask
            OUTCOME_ARRANGEMENTS[i] = arrangement_count
            inc i


# proc cache_sorted_dievals() = 
#     # for fast access later, this generates an array of dievals in sorted form, 
#     # along with each's unique "ID" between 0-252, indexed by DieVals data
#     SORTED_DIEVALS[0] = 0 #// first one is for the special wildcard 
#     let one_to_six = @[1,2,3,4,5,6] 
#     let combos = combos_with_rep(one_to_six, 5)
#     for combo in combos: 
#         var dv_sorted = init_dievals(combo)
#         Ints8* ints8_perms = get_unique_perms(combos[i], &perm_count)
#         for (int j=0; j<perm_count; j++) {
#             Ints8 perm = ints8_perms[j];
#             DieVals dv_perm = dievals_from_ints8(perm);
#             SORTED_DIEVALS[dv_perm] = (DieValsID){.dievals=dv_sorted, .id=i};
#         }
#     }
# }



#[


V* EV_CACHE; // 2^29 indexes hold all game state EVs
Choice* CHOICE_CACHE; // 2^29 indexes hold all corresponding Choices

Ints32 SELECTION_SET_OF_ALL_DICE_ONLY; //  selections are bitfields where '1' means roll and '0' means don't roll 
Ints32 SELECTION_SET_OF_ALL_POSSIBLE_SELECTIONS; // Ints32 type can hold 32 different selections 



void init_caches(){

    OUTCOME_EVS_BUFFER = malloc(NUM_THREADS * sizeof(f32*));
    for (int i = 0; i < NUM_THREADS; i++) { OUTCOME_EVS_BUFFER[i] = malloc(1683 * sizeof(f32)); }

    NEWVALS_BUFFER = malloc(NUM_THREADS * sizeof(u16*));
    for (int i = 0; i < NUM_THREADS; i++) { NEWVALS_BUFFER[i] = malloc(1683 * sizeof(DieVals)); }

    EVS_TIMES_ARRANGEMENTS_BUFFER = malloc(NUM_THREADS * sizeof(f32*));
    for (int i = 0; i < NUM_THREADS; i++) { EVS_TIMES_ARRANGEMENTS_BUFFER[i] = malloc(1683 * sizeof(f32)); }

    # setup helper values
    cache_selection_ranges(); 
    cache_sorted_dievals(); 
    cache_roll_outcomes_data();

    # selection sets
    SELECTION_SET_OF_ALL_DICE_ONLY = (Ints32){ 1, 0b11111 }; //  selections are bitfields where '1' means roll and '0' means don't roll 
    SELECTION_SET_OF_ALL_POSSIBLE_SELECTIONS = (Ints32){}; // Ints32 type can hold 32 different selections 
    for(int i=0b00000; i<=0b11111; i++) SELECTION_SET_OF_ALL_POSSIBLE_SELECTIONS.arr[i]=i; 
    SELECTION_SET_OF_ALL_POSSIBLE_SELECTIONS.count=32;

    //gignormous cache for holding EVs of all game states
    EV_CACHE = malloc(pow(2,29) * sizeof(EV)); // 2^29 slots hold all unique game states 
    CHOICE_CACHE = malloc(pow(2,29) * sizeof(Choice)); // 2^29 slots hold all unique game states 
 
}


void init_bar_for(GameState game) {
    tick_limit = counts(game);
    tick_interval = (tick_limit) / 100;
    printf("Progress: %d%%\r", 0);
    fflush(stdout);
} 

void tick(){
    ticks++;
    if (ticks % tick_interval == 0) {
        printf("Progress: %d%%\r", (int)(ticks * 100 / tick_limit));
        // printf("█");
        fflush(stdout);
    }
}



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


when isMainModule:

  # test some stuff
   # Create a sequence with multiple elements
   let inputSeq = @[1, 1, 3]
   
   # Call the `unique_permutations` function on the sequence
   let resultSeq = unique_permutations(inputSeq)
   
   # Create a sequence containing all the expected permutations
   let expectedSeq = @[@[1, 1, 3], @[1, 3, 1], @[3, 1, 1]]
   
   # Loop through the result and compare each element to the expected permutations
   for result in resultSeq:
       if not expectedSeq.contains(result):
           echo "Test failed: unexpected permutation"
           quit 1
   
   # If all elements are in the expected permutations, the test passes
   echo "Test passed"
    