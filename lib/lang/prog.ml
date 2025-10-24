open Value
open Common
open Types
open Expr
open ContainersLabels

module ID = struct
  include Int
  module Map = Map.Make (Int)

  module Named = struct
    (* generator for unique integer identifiers with an optionally associated name. 
       maintains a mapping between id and name.

       note: ID.t is the canonical identifier, 
        with the associated name assumed to be unique with respect to it.
       *)
    module M = CCBijection.Make (String) (Int)

    type cache = { names : M.t ref; gen : Fix.Gensym.gensym }

    let get_id c name = M.find_left name !(c.names)
    let get_name c id = M.find_right id !(c.names)

    let fresh c ?(name : string option) () =
      let id = c.gen () in
      Option.iter (fun n -> c.names := M.add n id !(c.names)) name;
      id

    type t = {
      get_id : string -> int;
      get_name : int -> string;
      fresh : ?name:string -> unit -> int;
    }

    let make () =
      let c = { names = ref M.empty; gen = Fix.Gensym.make () } in
      { get_id = get_id c; fresh = fresh c; get_name = get_name c }
  end
end

module Params = struct
  module M = Map.Make (String)

  type formal = Var.t M.t [@@deriving eq, ord]
  type actual = BasilExpr.t M.t [@@deriving eq, ord]
  type lhs = Var.t M.t [@@deriving eq, ord]

  let show_actual a =
    M.to_list a
    |> List.map ~f:(function k, v ->
           Printf.sprintf "%s -> %s" k (BasilExpr.to_string v))
    |> String.concat ~sep:", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_actual fmt a = Format.pp_print_string fmt (show_actual a)

  let show_formal (a : formal) =
    M.to_list a
    |> List.map ~f:(function k, v ->
           Printf.sprintf "%s -> %s" k (Var.to_string v))
    |> String.concat ~sep:", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_formal fmt a = Format.pp_print_string fmt (show_formal a)

  let show_lhs (a : lhs) =
    M.to_list a
    |> List.map ~f:(function k, v ->
           Printf.sprintf "%s <- %s" (Var.to_string v) k)
    |> String.concat ~sep:", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_lhs fmt a = Format.pp_print_string fmt (show_lhs a)
end

module Stmt = struct
  type endian = [ `Big | `Little ] [@@deriving eq, ord]
  type ident = string

  let show_endian = function `Big -> "be" | `Little -> "le"
  let pp_endian fmt e = Format.pp_print_string fmt (show_endian e)

  type ('var, 'expr) t =
    | Instr_Assign of ('var * 'expr) list
    | Instr_Assert of { body : 'expr }
    | Instr_Assume of { body : 'expr; branch : bool }
    | Instr_Load of { lhs : 'var; mem : Var.t; addr : 'expr; endian : endian }
    | Instr_Store of {
        mem : Var.t;
        addr : 'expr;
        value : 'expr;
        endian : endian;
      }
    | Instr_Call of { lhs : Params.lhs; procid : ID.t; args : Params.actual }
    | Instr_Return of { args : Params.actual }
    | Instr_IntrinCall of {
        lhs : Params.lhs;
        name : string;
        args : Params.actual;
      }
    | Instr_IndirectCall of { target : 'expr }
  [@@deriving eq, ord, map, show]

  let p = pp

  let to_string show_var show_expr (s : (Var.t, BasilExpr.t) t) =
    map show_var show_expr s |> function
    | Instr_Assign ls ->
        List.map ~f:(function lhs, rhs -> lhs ^ " := " ^ rhs) ls
        |> String.concat ~sep:", "
    | Instr_Assert { body } -> "assert " ^ body
    | Instr_Assume { body; branch = false } -> "assume " ^ body
    | Instr_Assume { body; branch = true } -> "guard " ^ body
    | Instr_Load { lhs; mem; addr; endian } ->
        lhs ^ " := " ^ "load_" ^ show_endian endian ^ " " ^ addr
    | Instr_Store { mem; addr; value; endian } ->
        "store_" ^ show_endian endian ^ " " ^ addr ^ " " ^ value
    | Instr_Call { lhs; procid; args } ->
        let lhs =
          if Params.M.is_empty lhs then "" else Params.show_lhs lhs ^ " := "
        in
        lhs ^ " := call " ^ Params.show_actual args
    | Instr_Return { args } -> "return " ^ Params.show_actual args
    | Instr_IntrinCall { lhs; name; args } ->
        let lhs =
          if Params.M.is_empty lhs then "" else Params.show_lhs lhs ^ " := "
        in
        lhs ^ " := call " ^ name ^ Params.show_actual args
    | Instr_IndirectCall { target } -> "indirect_call " ^ target
end

module Block = struct
  type 'var phi = Phi of { lhs : 'var; rhs : (ID.t * 'var) list }
  [@@deriving eq, ord, show]

  type t = {
    id : ID.t;
    phis : Var.t list;
    stmts : (Var.t, BasilExpr.t) Stmt.t list;
  }
  [@@deriving eq, ord, show, map]

  let to_string b =
    Printf.sprintf "block %d [\n  %s]\n" b.id
      (List.map
         ~f:(fun stmt -> Stmt.to_string Var.to_string BasilExpr.to_string stmt)
         b.stmts
      |> String.concat ~sep:";\n  ")
end

module Procedure = struct
  type ident = Proc of int [@@unboxed]

  module Vert = struct
    type t = Begin of ID.t | End of ID.t
    [@@deriving show { with_path = false }, eq, ord]

    let hash (v : t) =
      let h = Hash.pair Hash.int Hash.int in
      Hash.map (function Begin i -> (31, i) | End i -> (37, i)) h v
  end

  module Edge = struct
    type block = Block.t [@@deriving eq, ord]
    type t = Block of block | Jump [@@deriving eq, ord]

    let show = function Block b -> Block.show b | Jump -> "goto"
    let to_string = function Block b -> Block.to_string b | Jump -> "goto"
    let default = Jump
  end

  module Loc = Int
  module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)

  type t = {
    id : ID.t;
    formal_in_params : Params.formal;
    formal_out_params : Params.formal;
    captures_globs : Var.Decls.t;
    modifies_globs : Var.Decls.t;
    requires : BasilExpr.t list;
    ensures : BasilExpr.t list;
    locals : Var.Decls.t;
    graph : G.t;
    gensym : Fix.Gensym.gensym;
    gensym_bloc : Fix.Gensym.gensym;
  }

  let add_goto p ~(from : ID.t) ~(targets : ID.t list) =
    let open Vert in
    let g = p.graph in
    let fr = End from in
    List.iter ~f:(fun t -> G.add_edge g fr (Begin t)) targets

  let create id ?(formal_in_params = Params.M.empty)
      ?(formal_out_params = Params.M.empty)
      ?(captures_globs = Var.Decls.empty ())
      ?(modifies_globs = Var.Decls.empty ()) ?(requires = []) ?(ensures = [])
      ?(locals = Var.Decls.empty ()) ?(blocks = Vector.create ()) () =
    {
      id;
      formal_in_params;
      formal_out_params;
      captures_globs;
      modifies_globs;
      requires;
      ensures;
      locals;
      graph = G.create ();
      gensym = Fix.Gensym.make ();
      gensym_bloc = Fix.Gensym.make ();
    }

  (*
  let update_block_by_index p (b : ('a, 'b) Block.t) =
    let i =
      Hashtbl.get p.block_i b.id |> Option.get_exn_or "update nonexistent block"
    in
    Vector.set p.blocks i b
    *)

  let fresh_block p ?(phis = []) ~(stmts : ('var, 'expr) Stmt.t list)
      ?(successors = []) () =
    let open Block in
    let id = p.gensym_bloc () in
    let b = Edge.(Block { id; phis; stmts }) in
    let open Vert in
    G.add_vertex p.graph (Begin id);
    G.add_vertex p.graph (Begin id);
    G.add_edge_e p.graph (Begin id, b, End id);
    List.iter ~f:(fun i -> G.add_edge p.graph (End id) (Begin i)) successors;
    id

  let get_block p id =
    let open Edge in
    let open G in
    try
      let _, e, _ = G.find_edge p.graph (Begin id) (End id) in
      match e with Block b -> Some b | Jump -> None
    with Not_found -> None

  let update_block p (block : Block.t) =
    let open Edge in
    let open G in
    let id = block.id in
    G.remove_edge p.graph (Begin id) (End id);
    G.add_edge_e p.graph (Begin id, Block block, End id)

  let fresh_var p ?(pure = true) typ =
    let n = "v" ^ Int.to_string (p.gensym ()) in
    let v = Var.create n typ in
    Var.Decls.add p.locals v;
    v

  let copy e = { e with graph = G.copy e.graph }
end

module Program = struct
  type e = BasilExpr.t
  type proc = Procedure.t
  type bloc = Block.t
  type stmt = (Var.t, e) Stmt.t

  type t = {
    modulename : string;
    globals : Var.Decls.t;
    procs : proc ID.Map.t;
    proc_names : ID.Named.t;
  }

  let decl_glob p = Var.Decls.add p.globals

  let empty ?name () =
    let modulename = Option.get_or ~default:"<module>" name in
    {
      modulename;
      globals = Var.Decls.empty ();
      procs = ID.Map.empty;
      proc_names = ID.Named.make ();
    }
end
