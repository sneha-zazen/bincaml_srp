open Value
open Common
module ID = Int
open Types

module Stmt = struct
  type endian = Big | Litle
  type ident = string

  module BlockID = ID
  module ProcID = ID

  type 'a predicate =
    | Or of 'a list
    | And of 'a list
    | Eq of 'a * 'a
    | Truth of 'a

  type ('var, 'expr) instr =
    | Instr_Assign of ('var * 'expr) list
    | Instr_Load of { lhs : 'var; addr : 'expr; endian : endian }
    | Instr_Store of {
        lhs : 'var;
        addr : 'expr;
        value : 'expr;
        endian : endian;
      }
    | Instr_Call of { lhs : 'var list; procid : ProcID.t; args : 'expr list }
    | Instr_IntrinCall of { lhs : 'var list; name : string; args : 'expr list }
    | Instr_IndirectCall of 'expr

  type ('var, 'expr) t =
    | Stmt_Instr of ('var, 'expr) instr
    | Stmt_Assume of 'expr predicate
    | Stmt_Guard of 'expr predicate
    | Stmt_Assert of 'expr predicate
    | Stmt_If of 'expr predicate * 'expr * 'expr
end

module Program = struct
  module IDMap = Map.Make (ID)

  type t = { procedure_name : string IDMap.t; block_label : string IDMap.t }
end
