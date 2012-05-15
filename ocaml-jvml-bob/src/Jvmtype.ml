type jclass = string list * string

type jref_type =
  | TObject of jclass
  | TArray  of jtype
and jtype =
  | TBoolean
  | TChar
  | TFloat
  | TDouble
  | TByte
  | TShort
  | TInt
  | TLong
  | TRef of jref_type

type methodsig = jtype list * jtype option

let string_of_class (packages, classname) =
  if packages = [] then
    classname
  else
    String.concat "/" packages ^ "/" ^ classname

let rec reftype_as_type_to_buffer buffer rt = match rt with
  | TObject fqclass ->
      Buffer.add_char buffer 'L';
      Buffer.add_string buffer (string_of_class fqclass);
      Buffer.add_char buffer ';'
  | TArray typ      ->
      Buffer.add_char buffer '[';
      type_to_buffer buffer typ
and type_to_buffer buffer typ = match typ with
  | TBoolean ->
      Buffer.add_char buffer 'Z'
  | TChar ->
      Buffer.add_char buffer 'C'
  | TFloat ->
      Buffer.add_char buffer 'F'
  | TDouble ->
      Buffer.add_char buffer 'D'
  | TByte ->
      Buffer.add_char buffer 'B'
  | TShort ->
      Buffer.add_char buffer 'S'
  | TInt ->
      Buffer.add_char buffer 'I'
  | TLong ->
      Buffer.add_char buffer 'J'
  | TRef rtyp ->
      reftype_as_type_to_buffer buffer rtyp

let string_of_reftype rt = match rt with
  | TObject fqclass -> string_of_class fqclass
  | rt              ->
      let buffer = Buffer.create 20 in
	reftype_as_type_to_buffer buffer rt;
	Buffer.contents buffer

let string_of_type t =
  let buffer = Buffer.create 20 in
    type_to_buffer buffer t;
    Buffer.contents buffer

let string_of_methodsig (arg_types, return_type) =
  let buffer = Buffer.create 20 in
    Buffer.add_char buffer '(';
    List.iter (type_to_buffer buffer) arg_types;
    Buffer.add_char buffer ')';
    (match return_type with
       | None   -> Buffer.add_char buffer 'V'
       | Some t -> type_to_buffer buffer t);
    Buffer.contents buffer

let index_from_limited s idx limit c =
  let rec loop i =
    if i = limit then None
    else if s.[i] = c then Some i
    else loop (i + 1)
  in
    loop idx

let class_of_substring s start_idx end_idx =
  let rec loop pkgs idx =
    match index_from_limited s idx end_idx '/' with
      | None ->
	  Some (List.rev pkgs, String.sub s idx (end_idx - idx))
      | Some idx' ->
	  let pkg_component = String.sub s idx (idx' - idx) in
	    loop (pkg_component::pkgs) (idx'+1)
  in
    loop [] start_idx

let class_semi_of_substring s idx =
  try
    let semi_colon_idx = String.index_from s idx ';' in
      match class_of_substring s idx semi_colon_idx with
	| Some c -> Some (c,semi_colon_idx + 1)
	| None   -> None
  with Not_found -> None (* if String.index_from fails to find a ';' *)

let rec type_of_substring s idx = match s.[idx] with
  | 'B' -> Some (TByte, idx + 1)
  | 'C' -> Some (TChar, idx + 1)
  | 'D' -> Some (TDouble, idx + 1)
  | 'F' -> Some (TFloat, idx + 1)
  | 'I' -> Some (TInt, idx + 1)
  | 'J' -> Some (TLong, idx + 1)
  | 'S' -> Some (TShort, idx + 1)
  | 'Z' -> Some (TBoolean, idx + 1)
  | 'L'
  | '[' -> Option.map (fun (t,idx) -> (TRef t, idx)) (reftype_as_type_of_substring s idx)
  | _   -> None

and reftype_as_type_of_substring s idx = match s.[idx] with
  | 'L' ->
      (match class_semi_of_substring s (idx + 1) with
	 | Some (t, idx) -> Some (TObject t, idx)
	 | None          -> None)
  | '[' ->
      (match type_of_substring s (idx + 1) with
	 | Some (t, idx) -> Some (TArray t, idx)
	 | None          -> None)
  | _   ->
      None

let class_of_string s =
  class_of_substring s 0 (String.length s)

let type_of_string s = match type_of_substring s 0 with
  | Some (t, idx) when idx = String.length s -> Some t
  | _                                        -> None

let reftype_of_string s =
  if String.length s = 0 then
    None
  else if s.[0] = '[' then
    (match reftype_as_type_of_substring s 0 with
       | Some (t, idx) when idx = String.length s -> Some t
       | _                                        -> None)
  else
    Option.map (fun x -> TObject x) (class_of_string s)

let methodsig_of_string s =
  let return_type args idx = match s.[idx] with
    | 'V' -> Some ((args, None), idx + 1)
    | _   ->
	(match type_of_substring s idx with
	   | Some (t, idx') -> Some ((args, Some t), idx')
	   | None           -> None)
  in

  let rec arg_list arg_accum idx = match s.[idx] with
    | ')' -> return_type (List.rev arg_accum) (idx + 1)
    | _   ->
	(match type_of_substring s idx with
	   | Some (t, idx') -> arg_list (t::arg_accum) idx'
	   | None           -> None)
  in
  let parse = match s.[0] with
    | '(' -> arg_list [] 1
    | _   -> None
  in
    match parse with
      | Some (methodsig, idx) when idx = String.length s -> Some methodsig
      | _ -> None
