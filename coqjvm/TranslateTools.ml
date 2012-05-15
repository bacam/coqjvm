open CoqModules

module CP = Ocaml_jvml.Constpool
module CF = Ocaml_jvml.Classfile

(* Adapted from the internal name parsing of ocaml_jvml. *)
let index_from_limited s idx limit c =
  let rec loop i =
    if i = limit then None
    else if s.[i] = c then Some i
    else loop (i + 1)
  in
    loop idx

let class_of_string s =
  let end_idx = String.length s in
  let rec loop pkgs idx =
    match index_from_limited s idx end_idx '.' with
      | None ->
          (List.rev pkgs, String.sub s idx (end_idx - idx))
      | Some idx' ->
          let pkg_component = String.sub s idx (idx' - idx) in
            loop (pkg_component::pkgs) (idx'+1)
  in
    loop [] 0

let find_attr pool s l =
  match List.find (fun (CF.Attribute (cpid,_)) -> CP.lookup_utf8 pool cpid = s) l with
    | CF.Attribute (_, CF.Attr a) -> a
    | _ -> failwith ("Attribute " ^ s ^ " was of the wrong type")

let breakup_res s =
  let len = String.length s in
  let rec next i l =
    let j = try String.index_from s i ' ' with Not_found -> len in
    let bang = s.[i] == '!' in
    let i' = if bang then i+1 else i in
    let rs = (bang,String.sub s i' (j-i))::l in
    if j < len then next (j+1) rs
    else List.map (function (x,y) -> (x,class_of_string y)) (List.rev rs)
  in next 0 []

