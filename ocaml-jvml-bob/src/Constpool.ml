(* Constpool.sml
 *
 * Kenneth MacKenzie
 * May 2006
 *)

module JT = Jvmtype

exception BadIndex of int

type index = int

let maxPool = 0xffff

let index_of_int k =
  if 0 < k && k < maxPool then k else raise (BadIndex k)

let index_option_of_int = function
    0 -> None
  | n -> Some (index_of_int n)

let index_to_int i = i

type entry =
    CPutf8       of string
  | CPint        of int32
  | CPfloat      of JFloat.t
  | CPlong       of int64
  | CPdouble     of float
  | CPclass      of index
  | CPstring     of index
  | CPfieldref   of index * index
  | CPmethodref  of index * index
  | CPimethodref of index * index
  | CPnametype   of index * index

(* Constant pools are represented as arrays of their elements,
 * since index 0 is invalid in all constant pools, we store the index 1 element at location 0 in the array
 * inaccessible elements (the ones that are the index after a long or double) are represented as None
 *)
   
type pool = entry option array

(* this actually returns the size + 1 *)
let size pool = Array.length pool + 1

let iter f pool =
  Array.iter (fun e -> match e with None -> () | Some e -> f e) pool

let iteri f pool =
  Array.iteri (fun i e -> match e with None -> () | Some e -> f (i+1) e) pool

exception BadLookup of string * int

let lookup pool idx = 
  if idx > Array.length pool then raise (BadLookup ("Constant pool index out of range", idx));
  match pool.(idx-1) with
    | None       -> raise (BadLookup ("Attempt to lookup invalid entry in constant pool", idx))
    | Some entry -> entry

let lookup_utf8 pool idx = match lookup pool idx with
  | CPutf8 s -> s
  | _        -> raise (BadLookup ("bad link to utf8", idx))

let lookup_class pool idx = match lookup pool idx with
  | CPclass idx -> (match JT.reftype_of_string (lookup_utf8 pool idx) with
		      | None -> raise (BadLookup ("Invalid reference type name in constant pool", idx))
		      | Some t -> t)
  | _           -> raise (BadLookup ("Invalid reference type name in constant pool", idx))

let lookup_class_notarray pool idx = match lookup_class pool idx with
  | JT.TObject cnm -> cnm
  | JT.TArray _    -> raise (BadLookup ("Expecting a class name in the constant pool", idx))

let lookup_methodsig pool idx = match JT.methodsig_of_string (lookup_utf8 pool idx) with
  | None    -> raise (BadLookup ("Invalid method signature in constant pool", idx))
  | Some ms -> ms

let lookup_type pool idx = match JT.type_of_string (lookup_utf8 pool idx) with
  | None   -> raise (BadLookup ("Invalid type in constant pool", idx))
  | Some t -> t

let lookup_methoddesc pool idx = match lookup pool idx with
  | CPnametype (method_name_idx, method_sig_idx) ->
      (lookup_utf8 pool method_name_idx, lookup_methodsig pool method_sig_idx)
  | _ -> raise (BadLookup ("Bad constant pool reference to method descriptor", idx))

let lookup_fielddesc pool idx = match lookup pool idx with
  | CPnametype (field_name_idx, field_type_idx) ->
      (lookup_utf8 pool field_name_idx, lookup_type pool field_type_idx)
  | _ -> raise (BadLookup ("Bad constant pool reference to field descriptor", idx))

let lookup_fieldref pool idx = match lookup pool idx with
  | CPfieldref (class_name_idx, field_desc_idx) ->
      (match lookup_class pool class_name_idx with
	 | JT.TObject nm -> 
	     let fnm, ftype = lookup_fielddesc pool field_desc_idx in
	       (nm, fnm, ftype)
	 | _             -> raise (BadLookup ("Bad constant pool reference to field ref", idx)))
  | _ -> raise (BadLookup ("Bad constant pool reference to field ref", idx))

let lookup_methodref pool idx = match lookup pool idx with
  | CPmethodref (class_name_idx, method_desc_idx) ->
      let cnm = lookup_class pool class_name_idx in
      let (mnm, msig) = lookup_methoddesc pool method_desc_idx in
	(cnm, mnm, msig)
  | _ -> raise (BadLookup ("Bad constant pool reference to method ref", idx))

let lookup_imethodref pool idx = match lookup pool idx with
  | CPimethodref (class_name_idx, method_desc_idx) ->
      (match lookup_class pool class_name_idx with
	 | JT.TObject nm ->
	     let (mnm, msig) = lookup_methoddesc pool method_desc_idx in
	       (nm, mnm, msig)
	 | _          -> raise (BadLookup ("Bad constant pool reference to interface method ref", idx)))
  | _ -> raise (BadLookup ("Bad constant pool reference to interface method ref", idx))

let lookup_int pool idx = match lookup pool idx with
  | CPint i -> i
  | _       -> raise (BadLookup ("Bad constant pool reference to integer", idx))

let lookup_double pool idx = match lookup pool idx with
  | CPdouble d -> d
  | _          -> raise (BadLookup ("Bad constant pool reference to double", idx))

let lookup_float pool idx = match lookup pool idx with
  | CPfloat f -> f
  | _            -> raise (BadLookup ("Bad constant pool reference to float", idx))

let lookup_long pool idx = match lookup pool idx with
  | CPlong l -> l
  | _        -> raise (BadLookup ("Bad constant pool reference to long", idx))

(* building constant pools *)
type builder = { builder_pool    : entry option DynArray.t
	       ; builder_reverse : (entry, int) Hashtbl.t
	       }

exception PoolTooLarge

let create_builder ?(initial_size=10) () =
  { builder_pool    = DynArray.make initial_size
  ; builder_reverse = Hashtbl.create initial_size
  }

let pool_of_builder builder =
  DynArray.to_array builder.builder_pool

let builder_of_pool pool =
  let builder =
    { builder_pool    = DynArray.of_array pool
    ; builder_reverse = Hashtbl.create (Array.length pool)
    } in
    DynArray.iteri
      (fun i -> function
	 | None -> ()
	 | (Some entry) -> Hashtbl.add builder.builder_reverse entry (i+1))
      builder.builder_pool;
    builder

let is_wide_entry e = match e with CPdouble _ | CPlong _ -> true | _ -> false

(* first way: just adding things to the end *)
let append_entry builder entry =
  let idx = DynArray.length builder.builder_pool in
    if idx = 0xffff || (is_wide_entry entry && idx = 0xfffe) then raise PoolTooLarge;
    DynArray.add builder.builder_pool (Some entry);
    Hashtbl.add builder.builder_reverse entry (idx+1);
    (match entry with
       | CPdouble _ | CPlong _ ->
	   DynArray.add builder.builder_pool None
       | _ -> ());
    idx + 1

(* the second way: smart adding that does not add the same thing twice *)
let add_entry builder entry =
  if Hashtbl.mem builder.builder_reverse entry then
    Hashtbl.find builder.builder_reverse entry
  else
    append_entry builder entry
	
let add_utf8 builder str = add_entry builder (CPutf8 str)

let add_int builder i = add_entry builder (CPint i)

let add_float builder f = add_entry builder (CPfloat f)

let add_long builder l = add_entry builder (CPlong l)

let add_double builder d = add_entry builder (CPdouble d)

let add_string builder str =
  let utf8_idx = add_utf8 builder str in
    add_entry builder (CPstring utf8_idx)

let add_class builder ref_typ =
  let name = Jvmtype.string_of_reftype ref_typ in
  let name_idx = add_utf8 builder name in
    add_entry builder (CPclass (name_idx))

let add_methoddesc builder (mname,msig) =
  let method_name = add_utf8 builder mname in
  let method_sig  = add_utf8 builder (Jvmtype.string_of_methodsig msig) in
    add_entry builder (CPnametype (method_name, method_sig))

let add_method_ref builder (mclass,mname,msig) =
  let class_idx   = add_class builder mclass in
  let nt_idx      = add_methoddesc builder (mname,msig) in
    add_entry builder (CPmethodref (class_idx, nt_idx))

let add_imethod_ref builder (mclass,mname,msig) =
  let class_idx   = add_class builder (Jvmtype.TObject mclass) in
  let nt_idx      = add_methoddesc builder (mname,msig) in
    add_entry builder (CPimethodref (class_idx, nt_idx))
      
let add_field_ref builder (fclass, fname, ftype) =
  let field_name = add_utf8 builder fname in
  let field_type = add_utf8 builder (Jvmtype.string_of_type ftype) in
  let class_idx  = add_class builder (Jvmtype.TObject fclass) in
  let nt_idx     = add_entry builder (CPnametype (field_name, field_type)) in
    add_entry builder (CPfieldref (class_idx, nt_idx))

let find builder entry =
  try Some (index_of_int (Hashtbl.find builder.builder_reverse entry)) with Not_found -> None

let find_utf8 builder str = find builder (CPutf8 str)
let find_int builder i = find builder (CPint i)
let find_float builder f = find builder (CPfloat f)
let find_class builder ref_type =
  let name = (match ref_type with
		| Jvmtype.TObject nm -> Jvmtype.string_of_class nm
		| typ                -> Jvmtype.string_of_reftype ref_type) in
    match find_utf8 builder name with
      | None -> None
      | Some index -> find builder (CPclass (index))
let find_string builder str =
  match find_utf8 builder str with
    | None -> None
    | Some idx -> find builder (CPstring idx)
