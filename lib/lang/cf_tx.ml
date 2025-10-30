open Prog
open Expr_eval
open Containers

let identity x = x

let simplify_proc_exprs p =
  let blocks = Procedure.blocks_to_list p in
  let open Procedure.Edge in
  let nblocks =
    List.iter
      (function
        | Procedure.Vert.Begin id, (b : (Var.t, Expr.BasilExpr.t) Block.t) ->
            Vector.map_in_place
              (Stmt.map ~f_lvar:identity ~f_rvar:identity
                 ~f_expr:partial_eval_expr)
              b.stmts
        | _ -> ())
      blocks
  in
  ()
