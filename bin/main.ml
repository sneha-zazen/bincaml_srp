open Cmdliner
open Lang.Prog

let check fname =
  let p = Ocaml_of_basil.Loadir.ast_of_fname fname in
  ID.Map.iter
    (fun _ (p : Procedure.t) ->
      Lang.Livevars.print_live_vars_dot Format.std_formatter p)
    p.prog.procs

let fname =
  let doc = "Input file name (filename.il)" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FNAME" ~doc)

let check_f = Term.(const check $ fname)

let cmd =
  let doc = "obasil" in
  let info = Cmd.info "obasil" ~version:"alpha" ~doc in
  Cmd.v info check_f

let main () = exit (Cmd.eval cmd)
let () = main ()
