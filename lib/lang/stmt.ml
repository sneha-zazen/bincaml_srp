open Value
open Common
module ID = Int
open Types
open Ast

module Stmt = struct
  type endian = Big | Litle [@@deriving eq, ord]
  type ident = string

  type ('var, 'expr) t =
    | Instr_Assign of ('var * 'expr) list
    | Instr_Load of { lhs : 'var; addr : 'expr; endian : endian }
    | Instr_Store of {
        lhs : 'var;
        addr : 'expr;
        value : 'expr;
        endian : endian;
      }
    | Instr_Call of { lhs : 'var list; procid : ID.t; args : 'expr list }
    | Instr_IntrinCall of { lhs : 'var list; name : string; args : 'expr list }
    | Instr_IndirectCall of { target : 'expr }
  [@@deriving eq, ord]
end

module Block = struct
  type ident = Block of int [@@unboxed]

  type 'var phi = Phi of { lhs : 'var; rhs : (ID.t * 'var) list }
  [@@deriving eq, ord]

  type ('var, 'expr) t = {
    id : ID.t;
    phis_in : 'var phi list;
    stmts : ('var, 'expr) Stmt.t list;
    phis_out : 'var phi list;
  }
  [@@deriving eq, ord]
end

module Procedure = struct
  type ident = Proc of int [@@unboxed]

  module Vert = struct
    type t = int [@@deriving show { with_path = false }, eq, ord]

    let hash v = Int.hash v
  end

  module Edge = struct
    type t = Block of ID.t | Jump [@@deriving eq, ord]

    let default = Jump
  end

  module Loc = Int
  module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)

  type ('var, 'e) t = {
    id : ID.t;
    name : string;
    requires : 'e list;
    ensures : 'e list;
    blocks : (ID.t, ('var, 'e) Block.t) Hashtbl.t;
    graph : G.t;
  }

  let copy e = { e with graph = G.copy e.graph }
end

module Program = struct
  module IDMap = Map.Make (ID)

  type e
  type v
  type proc = (v, e) Procedure.t
  type bloc = (v, e) Block.t
  type t = { procs : proc IDMap.t }

  (*type t = { procedure_name : string IDMap.t; block_label : string IDMap.t }*)
end
