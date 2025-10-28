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

  type unary = [ `NOT ] [@@deriving show { with_path = false }, eq, ord]

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

  type unary =
    [ `BVNOT | `BVNEG | `BOOL2BV1 | `ZeroExtend of int | `SignExtend of int ]
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

  type intrin = [ `Extract of int * int | `BVAND | `BVOR | `BVADD | `BVXOR ]
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

  type binary = [ IntOps.binary | BVOps.binary | LogicalOps.binary ]
  [@@deriving show { with_path = false }, eq, ord]

  type intrin = [ BVOps.intrin | LogicalOps.intrin ]
  [@@deriving show { with_path = false }, eq, ord]

  type op_fun_type =
    | Fun of { args : Types.BType.t list; ret : Types.BType.t }
    (* list of expected type equalities *)
    | Conflict of (Types.BType.t * string) list

  let ret_type_const (o : const) =
    let open Types.BType in
    let return ret = Fun { args = []; ret } in
    match o with
    | `Bool _ -> return Boolean
    | `Integer _ -> return Integer
    | `Bitvector v -> return (Bitvector (PrimQFBV.width v))

  let ret_type_unary (o : unary) a =
    let open Types.BType in
    let return ret = Fun { args = [ a ]; ret } in
    match o with
    | `SignExtend sz -> (
        match a with
        | Bitvector s -> return @@ Bitvector (sz + s)
        | o -> Conflict [ (o, "<bitvector") ])
    | `ZeroExtend sz -> (
        match a with
        | Bitvector s -> return @@ Bitvector (sz + s)
        | o -> Conflict [ (o, "<bitvector") ])
    | `Forall -> return Boolean
    | `BVNEG -> return a
    | `INTNEG -> return Integer
    | `Old -> return a
    | `NOT -> return Boolean
    | `Exists -> return Boolean
    | `BVNOT -> return a
    | `BOOL2BV1 -> return @@ Bitvector 1

  let ret_type_bin (o : binary) l r =
    let open Types.BType in
    let return ret = Fun { args = [ l; r ]; ret } in
    match o with
    | `EQ | `NEQ | `BVULT | `BVULE | `BVSLT | `BVSLE | `INTLT | `IMPLIES
    | `INTLE ->
        return Boolean
    | `INTDIV | `INTADD | `INTMUL | `INTSUB | `INTMOD -> return Integer
    | `BVAND | `BVOR | `BVADD | `BVMUL | `BVUDIV | `BVUREM | `BVSHL | `BVLSHR
    | `BVNAND | `BVNOR | `BVXOR | `BVXNOR | `BVCOMP | `BVSUB | `BVSDIV | `BVSREM
    | `BVSMOD | `BVASHR ->
        return l
    | `BVConcat -> (
        match (l, r) with
        | Bitvector i, Bitvector j -> return @@ Bitvector (i + j)
        | i, j -> Conflict [ (i, "<Bitvector"); (j, "<bitvector") ])

  let ret_type_intrin (o : intrin) args =
    let open Types.BType in
    let return ret = Fun { args; ret } in
    match o with
    | `BVADD -> return @@ List.hd args
    | `Extract (hi, lo) -> return (Bitvector (hi - lo))
    | `BVOR -> return @@ List.hd args
    | `BVXOR -> return @@ List.hd args
    | `BVAND -> return @@ List.hd args
    | `OR -> return Boolean
    | `AND -> return Boolean

  (** ops returning booleans *)

  let to_string (op : [< const | unary | binary | intrin ]) =
    match op with
    | `BVADD -> "bvadd"
    | `BVNOR -> "bvnor"
    | `BVSREM -> "bvsrem"
    | `BVSDIV -> "bvsdiv"
    | `Forall -> "forall"
    | `BVCOMP -> "bvcomp"
    | `BVNEG -> "bvneg"
    | `Bool true -> "true"
    | `Bool false -> "false"
    | `BVASHR -> "bvashr"
    | `NEQ -> "neq"
    | `INTNEG -> "intneg"
    | `Old -> "old"
    | `BVMUL -> "bvmul"
    | `BVSHL -> "bvshl"
    | `Extract (hi, lo) -> Printf.sprintf "extract_%d_%d " hi lo
    | `INTDIV -> "intdiv"
    | `Exists -> "exists"
    | `SignExtend n -> Printf.sprintf "sign_extend_%d" n
    | `ZeroExtend n -> Printf.sprintf "zero_extend_%d" n
    | `BVXNOR -> "bvxnor"
    | `EQ -> "eq"
    | `INTADD -> "intadd"
    | `BVNAND -> "bvnand"
    | `BVSLE -> "bvsle"
    | `BVUREM -> "bvurem"
    | `BVNOT -> "bvnot"
    | `Integer i -> PrimInt.to_string i
    | `BVXOR -> "bvxor"
    | `BVOR -> "bvor"
    | `BVConcat -> "bvconcat"
    | `BVSUB -> "bvsub"
    | `BVUDIV -> "bvudiv"
    | `BVLSHR -> "bvlshr"
    | `INTMOD -> "intmod"
    | `BVAND -> "bvand"
    | `INTMUL -> "intmul"
    | `Bitvector z -> PrimQFBV.to_string z
    | `BVSMOD -> "bvsmod"
    | `INTLT -> "intlt"
    | `IMPLIES -> "implies"
    | `OR -> "or"
    | `INTLE -> "intle"
    | `BVULT -> "bvult"
    | `AND -> "and"
    | `INTSUB -> "intsub"
    | `BVULE -> "bvule"
    | `BOOL2BV1 -> "bool2bv1"
    | `NOT -> "not"
    | `BVSLT -> "bvslt"

  let hash_const = Hashtbl.hash
  let hash_unary = Hashtbl.hash
  let hash_binary = Hashtbl.hash
  let hash_intrin = Hashtbl.hash
end
