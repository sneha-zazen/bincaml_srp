open Common
open Containers
open Value

module V = struct
  type t = { name : string; typ : Types.BType.t; pure : bool }
  [@@deriving eq, ord]

  let var name ?(pure = true) typ = { name; typ; pure }
  let hash v = Hashtbl.hash v
end

module H = Fix.HashCons.ForHashedTypeWeak (V)

type t = V.t Fix.HashCons.cell

let create name ?(pure = false) typ = H.make { name; typ; pure }
let name (e : t) = (Fix.HashCons.data e).name
let typ (e : t) = (Fix.HashCons.data e).typ
let pure (e : t) = (Fix.HashCons.data e).pure
let compare (a : t) (b : t) = Fix.HashCons.compare a b
let equal (a : t) (b : t) = Fix.HashCons.equal a b
let hash (a : t) = Fix.HashCons.hash a

module Set = CCHashSet.Make (V)
module Bindings = CCHashTrie.Make (V)

module Decls = struct
  type var = t
  type t = (string, var) Hashtbl.t

  let find_opt m name = Hashtbl.find_opt m name
  let empty () : t = Hashtbl.create 30

  let add m (v : var) =
    let d = find_opt m (name v) in
    match d with
    | Some e when equal e v -> ()
    | Some e -> failwith "Already declared diff var with that name: "
    | None -> Hashtbl.add m (name v) v
end
