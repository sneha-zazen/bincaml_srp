open Common
open Containers
open Value

module Maps = struct
  (* map, value -> result *)
  type binary = [ `MapIndex ] [@@deriving show { with_path = false }, eq, ord]
  type intrin = [ `MapUpdate ] [@@deriving show { with_path = false }, eq, ord]

  let show = function
    | #binary as b -> show_binary b
    | #intrin as b -> show_intrin b

  let hash = Hashtbl.hash
end

module LogicalOps = struct
  type const = [ `Bool of bool ]
  [@@deriving show { with_path = false }, eq, ord]

  type unary = [ `LNOT ] [@@deriving show { with_path = false }, eq, ord]

  type binary = [ `EQ | `NEQ | `IMPLIES ]
  [@@deriving show { with_path = false }, eq, ord]

  type intrin = [ `AND | `OR ] [@@deriving show { with_path = false }, eq, ord]

  let show = function
    | #const as c -> show_const c
    | #unary as u -> show_unary u
    | #binary as b -> show_binary b

  let hash_boolop = Hashtbl.hash
end

module BVOps = struct
  type const = [ `Bitvector of PrimQFBV.t ]
  [@@deriving show { with_path = false }, eq, ord]

  type unary = [ `BVNOT | `BVNEG | `BOOL2BV1 ]
  [@@deriving show { with_path = false }, eq, ord]

  type binary =
    [ `BVAND
    | `BVOR
    | `BVADD
    | `BVMUL
    | `BVUDIV
    | `BVUREM
    | `BVSHL
    | `BVLSHR
    | `BVNAND
    | `BVNOR
    | `BVXOR
    | `BVXNOR
    | `BVCOMP
    | `BVSUB
    | `BVSDIV
    | `BVSREM
    | `BVSMOD
    | `BVASHR
    | `BVULT
    | `BVULE
    | `BVSLT
    | `BVSLE
    | `BVConcat ]
  [@@deriving show { with_path = false }, eq, ord]

  type intrin =
    [ `ZeroExtend of int
    | `SignExtend of int
    | `Extract of int * int
    | `BVAND
    | `BVOR
    | `BVADD
    | `BVXOR ]
  [@@deriving show { with_path = false }, eq, ord]

  let show = function
    | #const as c -> show_const c
    | #unary as u -> show_unary u
    | #binary as b -> show_binary b
end

module IntOps = struct
  type const = [ `Integer of PrimInt.t ]
  [@@deriving show { with_path = false }, eq, ord]

  type unary = [ `INTNEG ] [@@deriving show { with_path = false }, eq, ord]

  type binary =
    [ `INTADD | `INTMUL | `INTSUB | `INTDIV | `INTMOD | `INTLT | `INTLE ]
  [@@deriving show { with_path = false }, eq, ord]

  let show = function
    | #const as c -> show_const c
    | #unary as u -> show_unary u
    | #binary as b -> show_binary b
end

module Spec = struct
  type unary = [ `Forall | `Old | `Exists ]
  [@@deriving show { with_path = false }, eq, ord]

  let hash_intrin a = Hashtbl.hash a
end

module AllOps = struct
  type const = [ IntOps.const | BVOps.const | LogicalOps.const ]
  [@@deriving show { with_path = false }, eq, ord]

  type unary = [ IntOps.unary | BVOps.unary | Spec.unary | LogicalOps.unary ]
  [@@deriving show { with_path = false }, eq, ord]

  type binary =
    [ IntOps.binary | BVOps.binary | Maps.binary | LogicalOps.binary ]
  [@@deriving show { with_path = false }, eq, ord]

  type intrin = [ BVOps.intrin | Maps.intrin | LogicalOps.intrin ]
  [@@deriving show { with_path = false }, eq, ord]

  let hash_const = Hashtbl.hash
  let hash_unary = Hashtbl.hash
  let hash_binary = Hashtbl.hash
  let hash_intrin = Hashtbl.hash
end
