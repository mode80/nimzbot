import options, tables, sequtils, math, algorithm, strformat#, threadpool
{. hint[XDeclaredButNotUsed]:off .}
# {.experimental: "codeReordering".}

# -------------------------------------------------------------
# TYPES 
# -------------------------------------------------------------
type 
    u8 = uint8
    u16 = uint16
    u32 = uint32
    u64 = uint64
    f32 = float32
    f64 = float64 # lazy Rust-like abbreviations

    Selection = range[0b00000..0b11111]  # types can be constrained to range. cool
    Choice = u8
    DieVal = u8 

    Slot= enum 
        ACES=1, TWOS, THREES, FOURS, FIVES, SIXES,    
        THREE_OF_A_KIND, FOUR_OF_A_KIND, FULL_HOUSE, 
        SM_STRAIGHT, LG_STRAIGHT, YAHTZEE, CHANCE

# -------------------------------------------------------------
# UTILS 
# -------------------------------------------------------------

iterator `|||`[S, T](a: S, b: T): T {.inline, sideEffect.} = 
    ## a special iterator that encourages the compiler to apply loop vectorization 
    ## works by abusing the built in || iterator to inject arbitrary loop preface #pragmas 
    for i in `||`(a,b, "simd \n#pragma GCC ivdepi \n#pragma clang loop vectorize(enable)\n#pragma FP_CONTRACT STDC ON\n#pragma float_control(precise, off)") : 
        yield i # others? https://www.openmp.org/wp-content/uploads/OpenMP-4.5-1115-CPP-web.pdf

proc print(it :string) =
    ## print to stdout, without a newline
    stdout.write(it)
    stdout.flushFile()

iterator items (i :SomeOrdinal) :SomeOrdinal = ## one-liner enables use of "for i in 5:" syntax. pretty cool 
    for j in 0..<i: yield j

proc set_to[T] (left :var T, right :Option[T] ) = ## enables "result .set_to tot .as_long_as maxinarow >= n" syntax 
    if right!=none(T): left=right.get


func as_long_as [T] (left :T, cond:bool) :Option[T] = ## enables "result .set_to tot .as_long_as maxinarow >= n" syntax 
    if cond: some(left) else: none(T) 


func unless [T] (left :T, cond:bool) :Option[T] = ## enables "result .set_to tot .unless maxinarow < n" syntax 
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
    ## combos with repetition
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
    while true: 
        if not result.contains(list): result.add(list)
        if list.nextPermutation == false: break # nextPermutation modifies list in-place and returns false if done 

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


func toDieVals (args :varargs[int]) :DieVals = # convert a seq of 5 ints to a DieVals
    assert args.len == 5
    var intout :int = 0
    for i in 0..4:
        intout = intout or args[i] shl (i * 3)
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


func `[]`(self; i :int): DieVal = # extract a DieVal from a DieVals 
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

func toSlots(args: varargs[Slot]): Slots = ## construct a Slots from a varargs 
    for arg in args: result.incl arg

func toSlots(args: varargs[int]): Slots = ## construct a Slots from a varargs 
    for arg in args: 
        assert arg in 1..13
        result.incl arg.Slot

func toSlotSeq(self) :seq[Slot] = ## convert a Slots to a seq of Slots
    for slot in self: result.add slot

func `$`(self) :string = ## convert a Slots to a string
    for slot in self:
        result.add $slot.int
        result.add '_' 
    
func removing(self; slot :Slot) :Slots = ## return a new Slots with the given slot removed
    result = self
    result.excl slot

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
using sorted_dievals: DieVals # declare self to be of DieVals for below methods
using slot: Slot

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

    if (valcounts1,valcounts2) in [(2,3), (3,2)]: return 25
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

const NUM_THREADS=6

type UI = object
    tick_limit: int 
    tick_interval: int 
    ticks: int 
    progress_blocks: int


## These are index spans into the OUTCOME_ arrays below which correspond to each dieval selection.
## Each of the 32 indecis from 0b00000 to 0b11111 represents the dieval selection as a bitfield 
const OUTCOMES_IDX_FOR_SELECTION = [(0..<1), (1..<7), (7..<13), (13..<34), (34..<40), (40..<61),
(61..<82), (82..<138), (138..<144), (144..<165), (165..<186), (186..<242), (242..<263),
(263..<319), (319..<375), (375..<501), (501..<507), (507..<528), (528..<549), (549..<605),
(605..<626), (626..<682), (682..<738), (738..<864), (864..<885), (885..<941), (941..<997),
(997..<1123), (1123..<1179), (1179..<1305), (1305..<1431), (1431..<1683),] 

func make_roll_outcomes(): (array[1683,DieVals], array[1683,DieVals], array[1683,f32]) = 
    ## preps the caches of roll outcomes data for every possible 5-die selection (where '0' represents an unselected die) 
    var OUTCOME_DIEVALS {.noinit.} : array[1683,DieVals]
    var OUTCOME_MASKS {.noinit.} : array[1683,DieVals]
    var OUTCOME_ARRANGEMENTS {.noinit.} : array[1683,f32]

    var i = 0
    let idx_powerset: seq[seq[int]] = powerset @[0,1,2,3,4] 
    assert idx_powerset.len==32 
    let one_thru_six = @[1,2,3,4,5,6] 

    for idx_combo in idx_powerset:
        var dievals_arr = [0,0,0,0,0] 
        let die_count = idx_combo.len 
        
        let dieval_combos = combos_with_rep(one_thru_six, die_count) 

        for dieval_combo in dieval_combos:
            var mask_arr = [0b111,0b111,0b111,0b111,0b111]
            for j, idx in idx_combo:
                dievals_arr[idx] = dieval_combo[j]
                mask_arr[idx]=0
            OUTCOME_DIEVALS[i] = dievals_arr.toDieVals
            OUTCOME_MASKS[i] = mask_arr.toDieVals
            OUTCOME_ARRANGEMENTS[i] = distinct_arrangements_for(dieval_combo)
            inc i

    result = (OUTCOME_DIEVALS, OUTCOME_MASKS, OUTCOME_ARRANGEMENTS)


func make_sorted_dievals(): (array[32767, DieVals], array[32767, u8]) = 
    # for fast access later, this generates an array indexed by every possible DieVals value,
    # with each entry being the DieVals in sorted form, along with each's unique "ID" between 0-252, 
    var SORTED_DIEVALS {.noinit.} : array[32767, DieVals]
    var SORTED_DIEVAL_IDS {.noinit.} : array[32767, u8]
    SORTED_DIEVALS[0] = 0.DieVals #// first one is for the special wildcard 
    SORTED_DIEVAL_IDS[0] = 0.u8 #// first one is for the special wildcard 
    let one_to_six = @[1,2,3,4,5,6] 
    let combos = combos_with_rep(one_to_six, 5)
    for i,sorted_combo in combos: 
        # var sorted_combo = combo.sorted() # TODO appears this is redundant . is it??
        var dv_sorted:DieVals = sorted_combo.toDieVals
        let perms = unique_permutations(sorted_list=sorted_combo)
        for perm in perms: 
            let dv_perm:DieVals = perm.toDieVals
            SORTED_DIEVALS[dv_perm.int] = dv_sorted 
            SORTED_DIEVAL_IDS[dv_perm.int] = i.u8
    result = (SORTED_DIEVALS, SORTED_DIEVAL_IDS)


const (OUTCOME_DIEVALS, OUTCOME_MASKS, OUTCOME_ARRANGEMENTS) = make_roll_outcomes()
const (SORTED_DIEVALS, SORTED_DIEVAL_IDS) = make_sorted_dievals()

var EV_CACHE = cast[ptr UncheckedArray[f32]](createSharedU(f32, 1_073_741_824))
var CHOICE_CACHE = cast[ptr UncheckedArray[Choice]](createSharedU(Choice, 1_073_741_824))


# ------------------------------------------------------------
# GAMESTATE 
# ------------------------------------------------------------
  
#we can store all of below in a sparse array using 2^(8+13+6+2+1) entries = 1_073_741_824 entries = 5.2GB when storing 32bit EVs + 8bit Choice 
type GameState = object 
    id: u32                     # the 30-bit encoding which also serves as an index into EV_CACHE and CHOICE_CACHE for this game state 
    sorted_dievals: DieVals     # 15, 3 for each die, OR 8 bits once convereted to an ordinal DieVal_ID (252 possibilities)
    yahtzee_bonus_avail: bool   # 1bit         
    open_slots: Slots           # 13 bits        
    upper_total: u8             # 6 bits       
    rolls_remaining: u8         # 2 bits 

func init(T: type GameState, sorted_dievals: DieVals, open_slots: Slots, upper_total: u8, rolls_remaining: u8, yahtzee_bonus_avail: bool): GameState {.thread.}= 
    var id:u32
    var dievals_id = SORTED_DIEVAL_IDS[sorted_dievals.int] # self.id will use 30 bits total...
    id= (dievals_id.u32) or # this is the 8-bit encoding of self.sorted_dievals
        (yahtzee_bonus_avail.u32 shl 8.u32)  or  # this is the 1-bit encoding of self.yahtzee_bonus_avail 
        (cast[u32](open_slots)   shl 9.u32)  or # slots uses 13 bits 
        (upper_total.u32         shl 22.u32) or# upper total uses 6 bits 
        (rolls_remaining.u32     shl 28.u32) # 0-3 rolls is stored in 2 bits.  8+1+13+6+2 = 30 bits total 
    result = GameState( 
        id:id, 
        sorted_dievals: sorted_dievals, 
        yahtzee_bonus_avail: yahtzee_bonus_avail, 
        open_slots: open_slots, 
        upper_total: upper_total, 
        rolls_remaining: rolls_remaining 
    )

func counts(self: GameState): int = 
    ## calculate relevant counts for gamestate: required lookups and saves
    var slotsets = powerset(self.open_slots.toSlotSeq) 
    for slotset in slotsets:
        var joker_rules = not slotset.contains YAHTZEE # yahtzees aren't wild whenever yahtzee slot is still available 
        var totals = useful_upper_totals(slotset.toSlots)
        for total in totals:
            inc result # this just counts the cost of one pass through the bar.tick call in the dice-choose section of build_cache() loop


func score_first_slot_in_context(self: GameState): u8 = 

    assert self.open_slots!={}

    # score slot itself w/o regard to game state 
    var slot = toSeq(self.open_slots)[0] # first slot in open_slots
    result = score_slot_with_dice(slot, self.sorted_dievals) 

    # add upper bonus when needed total is reached 
    if slot<=SIXES and self.upper_total<63:
        var new_total = min(self.upper_total+result, 63) 
        if new_total==63 : # we just reach bonus threshold
            result += 35   # add the 35 bonus points 

    # special handling of "joker rules" 
    var just_rolled_yahtzee = (score_yahtzee(self.sorted_dievals)==50)
    var joker_possible = (slot != YAHTZEE) # joker rules in effect when the yahtzee slot is not open 
    if (just_rolled_yahtzee and joker_possible): # standard scoring applies against the yahtzee dice except ... 
        if (slot==FULL_HOUSE) :result=25
        if (slot==SM_STRAIGHT):result=30
        if (slot==LG_STRAIGHT):result=40

    # # special handling of "extra yahtzee" bonus per rules
    if (just_rolled_yahtzee and self.yahtzee_bonus_avail): result+=100

#-------------------------------------------------------------
# UI 
#-------------------------------------------------------------

proc init_ui(game: GameState) :UI =
    result.tick_limit = counts(game)
    result.tick_interval = (result.tick_limit) div 100
    print "Progress: 0%\r"

proc tick(ui: var UI) =
    ui.ticks.inc
    if ui.tick_interval==0 or ui.ticks mod ui.tick_interval == 0: 
        print &"Progress: {$(ui.ticks * 100 div ui.tick_limit)}%\r" 

proc print_state_choice_header() = 
    print"rolls_remaining,sorted_dievals,upper_total,yahtzee_bonus_avail,open_slots,choice,ev"

proc print_state_choice(s: GameState, c: Choice, ev: f32, threadid: int) = 
    ## sample output:     2,33366,63,Y,1_,00011,9.61
    const N_Y = ['N','Y'] 
    if s.rolls_remaining==0: 
        echo &"{threadid:2d}|{s.rolls_remaining},{$s.sorted_dievals},{s.upper_total:2d},{N_Y[s.yahtzee_bonus_avail.int]},{s.open_slots},{c:05d},{ev:0.2f}"
    else:
        echo &"{threadid:2d}|{s.rolls_remaining},{$s.sorted_dievals},{s.upper_total:2d},{N_Y[s.yahtzee_bonus_avail.int]},{s.open_slots},{c:05b},{ev:0.2f}"

proc output(s: GameState, choice: Choice, ev: f32, threadid: int) = 
    # Uncomment below for more verbose progress output at the expense of speed 
    # print_state_choice(s, choice, ev, threadid);
    discard
        

#-------------------------------------------------------------
# BUILD CACHE 
#-------------------------------------------------------------

const ALL_DICE = 0b11111.Selection #selections are bitfields where '1' means roll and '0' mean don't
const SELECTION_SET_OF_ALL_DICE_ONLY = @[ALL_DICE] 
const SET_OF_ALL_SELECTIONS = toSeq(0b00000.Selection..0b11111.Selection)


proc avg_ev(start_dievals: DieVals, selection:Selection, slots: Slots, upper_total: u8, 
            next_roll: u8, yahtzee_bonus_available: bool, threadid: int): f32 = 
    ## calculates the average EV for a dice selection from a starting dice combo 
    ## within the context of the other relevant gamestate variables

    var total_ev_for_selection: f32 = 0.0 
    var outcomes_arrangements_count: f32 = 0.0
    var range = OUTCOMES_IDX_FOR_SELECTION[selection]
    var OUTCOME_EVS_BUFFER {.noinit.} : array[1683,f32]
    var NEWVALS_BUFFER {.noinit.} : array[1683,DieVals] 

    var floor_state = GameState.init(
        0.DieVals,
        slots, 
        upper_total, 
        next_roll, # we'll average all the 'next roll' possibilities (which we'd calclated on the last pass) to get ev for 'this roll' 
        yahtzee_bonus_available 
    )
    var floor_state_idx = floor_state.id.int  
    # from this floor gamestate we can blend in a dievals_id to quickly calc the index we need to access the ev for the complete state 

    # blit all each roll outcome for the given dice selection onto the unrolled start_dievals and stash results in the NEWVALS_BUFFER 
    for i in range.a ||| range.b :  # the custom ||| operator is for a SIMD friendly loop
        NEWVALS_BUFFER[i] = (start_dievals.u16 and OUTCOME_MASKS[i].u16).DieVals #make some holes in the dievals for newly rolled die vals 
        NEWVALS_BUFFER[i] = (NEWVALS_BUFFER[i].u16 or OUTCOME_DIEVALS[i].u16).DieVals # fill in the holes with the newly rolled die vals

    for i in range: # this loop is a bunch of lookups so doesn't benefit from SIMD
        #= gather sorted =#
        var newvals_idx = NEWVALS_BUFFER[i].int
        var sorted_dievals_id = SORTED_DIEVAL_IDS[newvals_idx].int
        #= gather ev =#
        var state_to_get_id = floor_state_idx or sorted_dievals_id
        OUTCOME_EVS_BUFFER[i] = EV_CACHE[state_to_get_id]

    for i in range.a ||| range.b:
        # we have EVs for each "combination" but we need the average all "permutations" 
        # -- so we mutliply by the number of distinct arrangements for each combo 
        var count = OUTCOME_ARRANGEMENTS[i]
        total_ev_for_selection = OUTCOME_EVS_BUFFER[i] * count + total_ev_for_selection
        outcomes_arrangements_count += count

    # this final step gives us the average EV for all permutations of rolled dice 
    return total_ev_for_selection / outcomes_arrangements_count 

# end avg_ev


proc process_state(state: GameState, thread_id: int) = #{.thread.}= 
    ## this does the work of calculating and store the expected value of a single gamestate

    var best_choice: Choice = 0
    var best_ev: f32 = 0.0

    if state.rolls_remaining==0 : 

    #= HANDLE SLOT SELECTION  #=

        for slot in state.open_slots :

            # joker rules say extra yahtzees must be played in their matching upper slot if it's available
            var first_dieval = state.sorted_dievals[0]
            var joker_rules_matter = state.yahtzee_bonus_avail and # TODO check this departure from C code
                score_yahtzee(state.sorted_dievals) > 0 and
                first_dieval.Slot in state.open_slots
            var head_slot = if joker_rules_matter: first_dieval.Slot else: slot

            var yahtzee_bonus_avail_now = state.yahtzee_bonus_avail
            var upper_total_now :u8 = state.upper_total
            var dievals_or_placeholder = state.sorted_dievals
            var head_plus_tail_ev: f32 = 0.0
            var rolls_remaining_now :u8 = 0
            var choice: Choice = 0
            var ev: f32 = 0.0 

            # find the collective ev for the all the slots with this iteration's slot being first 
            # do this by summing the ev for the first (head) slot with the ev value that we look up for the remaining (tail) slots
            var passes = if state.open_slots.len==1: 1 else: 2 # to do this, we need two passes unless there's only 1 slot left 
            for pass in 1..passes:

                var slots_piece = if pass==1: {head_slot} else: state.open_slots.removing head_slot # work on 1)the head only, or 2) the set without the head
                var relevant_upper_total = if (upper_total_now + best_upper_total(slots_piece).u8 >= 63): upper_total_now else: 0 # only relevant totals are cached
                var state_to_get = GameState.init(
                    dievals_or_placeholder,
                    slots_piece, 
                    relevant_upper_total,
                    rolls_remaining_now, 
                    yahtzee_bonus_avail_now,
                )
                choice = CHOICE_CACHE[state_to_get.id]
                ev = EV_CACHE[state_to_get.id]
                if pass==1 and passes > 1 : # prep 2nd pass on relevant 1st pass only..  
                    # going into tail slots next, we may need to adjust the state based on the head choice
                    if choice.Slot <= SIXES:  # adjust upper total for the next pass 
                        var added = ev.u8 mod 100 # removes any yahtzee bonus from ev since that doesnt' count toward upper bonus total
                        upper_total_now = min(63.u8, upper_total_now + added)
                    elif choice.Slot==YAHTZEE :  # adjust yahtzee related state for the next pass
                        if ev>0.0: yahtzee_bonus_avail_now=true

                    rolls_remaining_now=3 # for upcoming tail lookup, we always want the ev for 3 rolls remaining
                    dievals_or_placeholder = 0.DieVals # for 3 rolls remaining, use "wildcard" representative dievals since dice don't matter when rolling all of them
                # end if pass==1
                head_plus_tail_ev += ev;

            # end for pass in 1..passes

            if head_plus_tail_ev >= best_ev : 
                best_choice = slot.Choice
                best_ev = head_plus_tail_ev
            
            if (joker_rules_matter): break # if joker-rules-matter we were forced to choose one slot, so we can skip trying the rest  

        #end for slot in slots                               

        output(state, best_choice, best_ev, thread_id);

        CHOICE_CACHE[state.id] = best_choice 
        EV_CACHE[state.id] = best_ev


    elif state.rolls_remaining > 0:   
        
    #= HANDLE DICE SELECTION =#    

        var next_roll = state.rolls_remaining-1
        var selections = if state.rolls_remaining==3: SELECTION_SET_OF_ALL_DICE_ONLY else: SET_OF_ALL_SELECTIONS
  
        # HOT LOOP !
        # for each possible selection of dice from this starting dice combo, 
        # we calculate the expected value of rolling that selection, then store the best selection along with its EV 
        for selection in selections:
            var avg_ev_for_selection = avg_ev(
                state.sorted_dievals, 
                selection, 
                state.open_slots, 
                state.upper_total, 
                next_roll, 
                state.yahtzee_bonus_avail, 
                thread_id
            ) 
            if (avg_ev_for_selection > best_ev):
                best_choice = selection.Choice
                best_ev = avg_ev_for_selection

        output(state, best_choice, best_ev, thread_id);
        CHOICE_CACHE[state.id] = best_choice # we're writing from multiple threads but each thread will be setting a different state_to_set.id
        EV_CACHE[state.id] = best_ev # " " " " 

    # end if rolls_remaining...  

# end process_state

type ProcessChunkArgs= tuple[slots: Slots, upper_total :u8, rolls_remaining: u8, joker_possible: bool, chunk_range: HSlice[int,int], thread_id: int]

# proc process_chunk(slots: Slots, upper_total :u8, rolls_remaining: u8, joker_possible: bool, chunk_range: HSlice[int,int], thread_id: int) = #{.thread.}=
proc process_chunk(args: ProcessChunkArgs) {.thread.}=

    var (slots, upper_total, rolls_remaining, joker_possible, chunk_range, thread_id) = args

    #for each yahtzee bonus possibility 
    for yahtzee_bonus_avail in false..joker_possible:

        # for each dieval combo in this chunk ...
        # for combo in OUTCOME_DIEVALS[1..3]:
        for i in chunk_range:
            var combo = OUTCOME_DIEVALS[i] 
            var state = GameState.init(combo, slots , upper_total.u8, rolls_remaining.u8, yahtzee_bonus_avail)
            process_state(state, thread_id)


proc build_ev_cache(apex_state: GameState) =
    ## for a given gamestate, calc and cache all the expected values for dependent states. (this is like.. the main thing)

    var threads: array[NUM_THREADS, Thread[ProcessChunkArgs]]
    
    var ui = init_ui(apex_state)

    var placeholder_dievals = 0.DieVals

    # first handle special case of the most leafy leaf calcs -- where there's one slot left and no rolls remaining
    for single_slot in apex_state.open_slots:
        var single_slot_set :Slots = {single_slot} # set of a single slot 
        var bonus_possibile = (single_slot != YAHTZEE)
        # for each yahtzee bonus availability
        for yahtzee_bonus_avail in false..bonus_possibile:
            # for each upper_total 
            var upper_totals = useful_upper_totals(single_slot_set)
            for upper_total in upper_totals:
                # for each outcome_combo 
                for outcome_combo in OUTCOME_DIEVALS[ OUTCOMES_IDX_FOR_SELECTION[ ALL_DICE ] ]: 
                    var state = GameState.init(outcome_combo, single_slot_set, upper_total.u8, 0.u8, yahtzee_bonus_avail)
                    var score = score_first_slot_in_context(state) 
                    CHOICE_CACHE[state.id] = single_slot.Choice
                    EV_CACHE[state.id] = score.f32
                    output(state, single_slot.Choice, score.f32, 0);

    # for each slotset of each length 
    for slot_seq in powerset(apex_state.open_slots.toSlotSeq): 

        if slot_seq.len==0: continue # skip empty slotsets
        var slots = slot_seq.toSlots
        var joker_possible = not slots.contains YAHTZEE # joker rules might be in effect whenever the yahtzee slot is already filled 
        var upper_totals = useful_upper_totals(slots) 

        # for each upper total 
        for upper_total in upper_totals: 

            ui.tick() # advance the progress bar  

            # for each rolls remaining
            for rolls_remaining in 0..3:

                var outcome_range = if rolls_remaining==3: 
                    OUTCOMES_IDX_FOR_SELECTION[0b00000] 
                    else: OUTCOMES_IDX_FOR_SELECTION[0b11111]
                
                var full_count = outcome_range.len 
                var chunk_count = full_count .ceilDiv NUM_THREADS
                if full_count < NUM_THREADS: chunk_count = full_count
                var thread_id=0

                # for each dieval_combo chunk
                for chunk_idx in countup(outcome_range.a, outcome_range.b, step=chunk_count): 
                    var chunk_range = chunk_idx..min(chunk_idx+chunk_count-1, outcome_range.b)
                    var args = (slots, upper_total.u8, rolls_remaining.u8, joker_possible, chunk_range, thread_id) 
                    if chunk_count==1: 
                        process_chunk(args)
                    else:
                        createThread threads[thread_id], process_chunk, args 
                        inc thread_id

                joinThreads(threads)# wait for all threads to finish


#-------------------------------------------------------------
# MAIN
#-------------------------------------------------------------

proc main() =
    #test stuff

    # var game = GameState.init( [3,4,4,6,6].toDieVals, [1].toSlots, 0, 1, false )
    # var game = GameState.init( [3,4,4,6,6].toDieVals, [4,5,6].toSlots, 0, 2, false ) #38.9117 
    # var game = GameState.init( [3,4,4,6,6].toDieVals, [1,2,8,9,10,11,12,13].toSlots, 0, 2, false ) #137.3749 
    var game = GameState.init( [0,0,0,0,0].toDieVals, [1,2,3,4,5,6,7,8,9,10,11,12,13].toSlots, 0, 3, false ) # 254.5896 

    build_ev_cache(game)

    echo "\n", CHOICE_CACHE[game.id], " ", EV_CACHE[game.id]


when isMainModule: main()