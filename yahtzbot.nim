{. hint[XDeclaredButNotUsed]:off .}
# {.experimental: "codeReordering".}
import macros, options, tables, sequtils, math, algorithm
# -------------------------------------------------------------
# TYPES 


type u8 = uint8
type u16 = uint16
type u32 = uint32
type u64 = uint64
type f32 = float32
type f64 = float64 # lazy Rust-like abbreviations

type Selection = u8
type Choice = u8
type DieVal = u8 

type Slot= enum 
    ACES=1, TWOS, THREES, FOURS, FIVES, SIXES,    
    THREE_OF_A_KIND, FOUR_OF_A_KIND, FULL_HOUSE, 
    SM_STRAIGHT, LG_STRAIGHT, YAHTZEE, CHANCE

# -------------------------------------------------------------
# UTILS 
# -------------------------------------------------------------

macro `:=` (name, value :untyped) :untyped = newVarStmt(name, value)

iterator items (i :SomeOrdinal) :SomeOrdinal = ## enable use of "for i in 5:" syntax 
    for j in 0..<i: yield j

proc set_to[T] (left :var T, right :Option[T] ) = 
    if right!=none(T): left=right.get


func as_long_as [T] (left :T, cond:bool) :Option[T] = 
    if cond: some(left) else: none(T) 


func unless [T] (left :T, cond:bool) :Option[T] = 
    if not cond: some(left) else: none(T) 


func n_take_r (n :int, r :int, order_matters :bool = false, with_replacement :bool = false) :int= 
    ## count of arrangements that can be formed from r selections, chosen from n items, 
    ## where order DOES or DOESNT matter, and WITH or WITHOUT replacement, as specified.
    if (order_matters): # order matters; we're counting "permutations" 
        if (with_replacement): 
            return n^r
        else: # no replacement
            return fac(n) div fac(n-r) # this = factorial(n) when r=n
    else : # we're counting "combinations" where order doesn't matter; there are less of these 
        if (with_replacement) :
            return fac(n+r-1) div (fac(r)*fac(n-1));
        else : # no replacement
            return fac(n) div (fac(r)*fac(n-r));


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
            divisor *= fac(count)
            non_zero_dievals += count

    return fac(non_zero_dievals) / divisor 


func powerset [T] (list :seq[T]) :seq[seq[T]] =

    let count :int = 2^list.len # set_size of power set of a set with set_size n is (2**n -1)
    var i, j :int

    for i in count: # Run from counter 000..0 to 111..1
        var innerList = newSeqOfCap[T](count) 
        # Check each jth bit in the counter is set If set then add jth element from set 
        for j in list.len: 
            if (i and (1 shl j)) > 0: innerList .add list[j]
        result .add innerList
    return result

func unique_permutations (sorted_list :seq[int]) :seq[seq[int]] = 
    ## returns a seq of seqs, where each inner seq is a unique permutation of the input seq
    var list = sorted_list
    while list.nextPermutation:
        if not result.contains(list): result.add(list)

func inverse [T] (s :set[T]) :set[T] =
    ## returns the inverse of a set, i.e. the set of all elements not in the input set
    for i in T.low..T.high: 
        if not s.contains(i): result.incl(i)

# -------------------------------------------------------------
# DIEVALS 
# -------------------------------------------------------------

type DieVals = distinct u16 # 5 dievals, each from 0 to 6, can be encoded in 2 bytes total, each taking 3 bits


func init_dievals(d1 :int, d2 :int, d3 :int, d4 :int, d5 :int) :DieVals = # construct a DieVals from 5 int args 
    result = DieVals(u16(d1) or u16(d2 shl 3) or u16(d3 shl 6) or u16(d4 shl 9) or u16(d5 shl 12))


func toDieVals (it:array[5,int]) :DieVals = # convert an array of 5 ints to a DieVals
    var intout :int = 0
    for i in 0..4:
        intout = intout or it[i] shl (i * 3)
    result = intout.DieVals


func toDieVals (it :seq[int]) :DieVals = # convert a seq of 5 ints to a DieVals
    assert it.len == 5
    var intout :int = 0
    for i in 0..4:
        intout = intout or it[i] shl (i * 3)
    result = intout.DieVals


using self: DieVals # declare self to be of DieVals for below methods


func toIntSeq(self) :seq[int] = # convert a DieVals to a seq of 5 ints
    var int_self = self.int
    for i in 0..4:
        let val = (int_self shr (i * 3)) and 7
        result.add val.int


func toIntArray(self) :array[5,int] = # convert a DieVals to a array of 5 ints
    var int_self = self.int
    for i in 0..4:
        let val = (int_self shr (i * 3)) and 7
        result[i] = val.int


func `[]`(self; i :int): DieVal = # extract a DieVal from a DieVals // TODO: try Nim bitset?
    assert i >= 0 and i < 5
    var int_self = self.int
    result = DieVal (int_self shr (i * 3)) and 0b111


iterator items(self) :DieVal =
    var int_self = self.int
    for i in 0..4: 
        let val = (int_self shr (i * 3)) and 7
        yield val.DieVal


iterator pairs(self) :(int,DieVal) =
    var int_self = self.int
    for i in 0..4: 
        let val = (int_self shr (i * 3)) and 7
        yield (i, val.DieVal)


func `$`(self) :string = # convert a DieVals to a string
    result = ""
    var int_self = self.int
    for i in 0..4:
        let val = (int_self shr (i * 3)) and 7
        result.add $val

#-------------------------------------------------------------
# SLOTS 
#-------------------------------------------------------------

# use Nim's built-in bitset type for slots
type Slots = set[Slot] 

using self: Slots

func init_slots(args: varargs[int]): Slots = ## construct a Slots from a varargs of Slot args) 
    for arg in args: result.incl arg.Slot


func `$`(self) :string = ## convert a Slots to a string
    for slot in self:
        result.add $slot.int
        result.add '_' 

func used_upper_slots(unused_slots :Slots) :Slots =
    const upper_slots = {ACES, TWOS, THREES, FOURS, FIVES, SIXES}
    var used_slots = unused_slots.inverse 
    result = used_slots * upper_slots # intersection 

func best_upper_total(slots :Slots) :int=
    for slot in slots: 
        if slot>SIXES: break 
        if slots.contains(slot): result += slot.int
    result *= 5

func useful_upper_totals(unused_slots :Slots) :seq[int] = 
    ## a non-exact but fast estimate of relevant_upper_totals
    ## ie the unique and relevant "upper bonus total" that could have occurred from the previously used upper slots
    var totals = toSeq(0..63) 
    var used_uppers = used_upper_slots(unused_slots)
    var all_even = true
    const BLANK = int.low

    for slot in used_uppers:
        if slot.int mod 2 == 1: (all_even = false; break)

    if all_even:  # stub out odd totals if the used uppers are all even 
        for total in totals.mitems: 
            if total mod 2 == 1: total = BLANK 

    # filter out the lowish totals that aren't relevant because they can't reach the goal with the upper slots remaining 
    # this filters out a lot of dead state space but means the lookup function must later map extraneous deficits to a default 

    var best_unused_slot_total = best_upper_total(unused_slots)

    for total in totals:
        if (total!=BLANK and total+best_unused_slot_total>=63) or total==0: 
            result.add total


# -------------------------------------------------------------
# SCORING FNs
# -------------------------------------------------------------

using 
    sorted_dievals: DieVals # declare self to be of DieVals for below methods
    slot: Slot


func score_upperbox (slot, sorted_dievals) :u8 = 
    for d in sorted_dievals:
        if d.u8 == slot.u8: result += slot.u8


func score_n_of_a_kind(n :int; sorted_dievals) :u8 = 
    var inarow=1; var maxinarow=1; var lastval=100.u8; var tot=0.u8; 
    for x in sorted_dievals:
        if x==lastval and x!=0.DieVal: inarow+=1 else: inarow=1 
        maxinarow = max(inarow,maxinarow)
        lastval = x
        tot+=x
    result .set_to tot .as_long_as maxinarow >= n    # TODO test performance of this sugar


func straight_len(sorted_dievals) :u8 = 
    var inarow:u8 = 1 
    var lastval= uint8.high # stub
    for x in sorted_dievals:
        if x==lastval+1 and x!=0:
            inarow+=1 
        elif x!=lastval: 
            inarow=1 
        result = max(inarow, result)
        lastval = x


func score_aces  (sorted_dievals) :u8 = score_upperbox(1.Slot,sorted_dievals)     
func score_twos  (sorted_dievals) :u8 = score_upperbox(2.Slot,sorted_dievals) 
func score_threes(sorted_dievals) :u8 = score_upperbox(3.Slot,sorted_dievals) 
func score_fours (sorted_dievals) :u8 = score_upperbox(4.Slot,sorted_dievals) 
func score_fives (sorted_dievals) :u8 = score_upperbox(5.Slot,sorted_dievals) 
func score_sixes (sorted_dievals) :u8 = score_upperbox(6.Slot,sorted_dievals) 
        
func score_three_of_a_kind (sorted_dievals) :u8 = score_n_of_a_kind(3,sorted_dievals)
func score_four_of_a_kind  (sorted_dievals) :u8 = score_n_of_a_kind(4,sorted_dievals)
func score_sm_str8         (sorted_dievals) :u8 = (if straight_len(sorted_dievals) >= 4: 30 else: 0)
func score_lg_str8         (sorted_dievals) :u8 = (if straight_len(sorted_dievals) == 5: 40 else: 0)


func score_fullhouse(sorted_dievals) :u8 = 
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

func score_chance(sorted_dievals) :u8 = 
    
    let dv = sorted_dievals
    return dv[0]+dv[1]+dv[2]+dv[3]+dv[4] 

        
func score_yahtzee(sorted_dievals) :u8 =
    let dv = sorted_dievals
    if dv[0]==dv[4] and dv[0]!=0: result = 50


func score_slot_with_dice(slot, sorted_dievals) :u8 =
    # reports the score for a set of dice in a given slot w/o regard for exogenous gamestate (bonuses, yahtzee wildcards etc) 
    case Slot slot
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
        
# -------------------------------------------------------------
# INITIALIZERS etc
# -------------------------------------------------------------

## These are index spans into the OUTCOME_ arrays below which correspond to each dieval selection.
## Each of the 32 indecis from 0b00000 to 0b11111 represents the dieval selection as a bitfield 
const SELECTION_RANGES = [(0, 1), (1, 7), (7, 13), (13, 34), (90, 96), (179, 200), (592, 613), 
    (34, 90), (96, 102), (200, 221), (613, 634), (102, 158), (221, 242), (634, 690), (263, 319), 
    (746, 872), (1005, 1011), (158, 179), (319, 340), (690, 746), (242, 263), (872, 928), (1011, 1067), 
    (340, 466), (928, 949), (1067, 1123), (1249, 1305), (466, 592), (949, 1005), (1123, 1249), 
    (1305, 1431), (1431, 1683)] # = cache_selection_ranges()   # TODO confirm these are correct

## these are filled with cache_roll_outcomes()
var OUTCOME_DIEVALS :array[1683,DieVals] 
var OUTCOME_MASKS :array[1683,DieVals] 
var OUTCOME_ARRANGEMENTS :array[1683,f32] 

# these are filled with cache_sorted_dievals()
var SORTED_DIEVALS :array[32767, DieVals]
var SORTED_DIEVAL_IDS :array[32767, u8]

# ## these are filled with build_ev_cache()
var EV_CACHE   {.noInit.} :ref array[1_073_741_824, f32] # 2^30 indexes hold all game state EVs
var CHOICE_CACHE {.noInit.} : ref array[1_073_741_824, Choice] # 2^30indexes hold all corresponding Choices

const SELECTION_SET_OF_ALL_DICE_ONLY = [0b11111.Selection] #  selections are bitfields where '1' means roll and '0' means don't roll 
var SET_OF_ALL_SELECTIONS = toSeq[Selection](0b00000..0b11111)

proc cache_roll_outcomes() = 
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
            OUTCOME_DIEVALS[i] = dievals_arr.toDieVals
            OUTCOME_MASKS[i] = mask_arr.toDieVals
            OUTCOME_ARRANGEMENTS[i] = arrangement_count
            inc i


proc cache_sorted_dievals() = 
    # for fast access later, this generates an array indexed by every possible DieVals value,
    # with each entry being the DieVals in sorted form, along with each's unique "ID" between 0-252, 
    SORTED_DIEVALS[0] = 0.DieVals #// first one is for the special wildcard 
    SORTED_DIEVAL_IDS[0] = 0.u8 #// first one is for the special wildcard 
    let one_to_six = @[1,2,3,4,5,6] 
    let combos = combos_with_rep(one_to_six, 5)
    for combo in combos: 
        var sorted_combo = combo.sorted()
        var dv_sorted:DieVals = sorted_combo.toDieVals
        let perms = unique_permutations(sorted_list=sorted_combo)
        for i, perm in perms: 
            let dv_perm:DieVals = perm.toDieVals
            SORTED_DIEVALS[dv_perm.int] = dv_sorted 
            SORTED_DIEVAL_IDS[dv_perm.int] = i.u8


proc init_caches() =
    ## setup helper values
    cache_sorted_dievals() 
    cache_roll_outcomes()

#[


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
# GAMESTATE 
# -------------------------------------------------------------

#-------------------------------------------------------------
# BUILD CACHE 
#-------------------------------------------------------------


#-------------------------------------------------------------
# MAIN
#-------------------------------------------------------------

when isMainModule:

    #test stuff

    var slots:Slots = init_slots(2,2,3,6,5,8,9,10,11,12,13)
    echo $slots
    var slot = toSeq(slots.items)[1]
    echo slot
    echo slots.contains(FULL_HOUSE)
    slots.excl(FULL_HOUSE)
    echo slots.len
    echo slots.contains(FULL_HOUSE)
    var unused = used_upper_slots(unused_slots=slots)
    echo slots
    echo slots.best_upper_total

    # Test useful_upper_totals
    var used_uppers = init_slots(1,2,3,4,5,6)
    var results = useful_upper_totals(used_uppers)
    var expected_output = @[0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62]
    assert results == expected_output

    used_uppers = init_slots(3,4,5)
    results = useful_upper_totals(used_uppers)
    expected_output = @[0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
    assert results == expected_output
    echo "tests passed"
