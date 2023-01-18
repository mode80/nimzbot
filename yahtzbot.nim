# {.experimental: "codeReordering".}

type u8 = uint8
type u16 = uint16
type u32 = uint32
type f32 = float32
type f64 = float64 # lazy Rust-like abbreviations

type Selection = distinct u8
type Slot = distinct u8
type Choice = distinct u8
type DieVal = distinct u8; 

proc `+`(a, b :DieVal) :DieVal {.borrow.} # imbue DieVal with addability 
 

# -------------------------------------------------------------
# DieVals
# -------------------------------------------------------------

type DieVals = u16 # 5 dievals, each from 0 to 6, can be encoded in 2 bytes total, each taking 3 bits

proc init(dv: array[5,int]) :DieVals = # construct a DieVals from an array of 5 DieVal types
  var res:u16 = 0
  for i in 0..4:
    res = res or u16(dv[i] shl (i * 3))
  return DieVals(res)

iterator items(dv:DieVals):DieVal =
  let dv = dv.uint16
  for i in 0..4: 
    let val = (dv shr (i * 3)) and 7
    yield DieVal(val)

when isMainModule:
  # test some stuff
  let dv = [1,2,3,4,5].init
  for d in dv.items: 
    echo repr(d)
