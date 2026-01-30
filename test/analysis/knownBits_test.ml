open Bincaml_util.Common
open Analysis.Known_bits.IsKnownBitsOps

let%test "mul_bothknown" = 
let a = known (Bitvec.of_int ~size:4 5) in
let b = known (Bitvec.of_int ~size:4 3) in
  let res = known (Bitvec.of_int ~size:4 15) in
  equal res @@ mul a b

let%test "mul_aknown" = 
let a = known (Bitvec.of_int ~size:4 5) in
let b = tnum
      (Bitvec.of_int ~size:4 0b1000)
      (Bitvec.of_int ~size:4 0b0111) in
  let res = tnum
      (Bitvec.of_int ~size:8 0b00000000)
      (Bitvec.of_int ~size:8 0b00111111) in
  equal res @@ mul a b

  let%test "mul_bothknown" = 
let a = known (Bitvec.of_int ~size:4 5) in
let b = known (Bitvec.of_int ~size:4 3) in
  let res = known (Bitvec.of_int ~size:4 15) in
  equal res @@ mul a b

let%test "mul_aknown" = 
let a = tnum
      (Bitvec.of_int ~size:4 0b1000)
      (Bitvec.of_int ~size:4 0b0111) in
let b = tnum
      (Bitvec.of_int ~size:4 0b1000)
      (Bitvec.of_int ~size:4 0b0111) in
  let res = tnum
      (Bitvec.of_int ~size:8 0b00000000)
      (Bitvec.of_int ~size:8 0b00111111) in
  equal res @@ mul a b
