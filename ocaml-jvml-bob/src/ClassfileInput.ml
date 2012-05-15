(* ---------------------------- Classfile input ----------------------------*)

module CF = Classfile
module CP = Constpool
module AF = AccessFlags

exception ClassfileInputError of string

(* -------------------- auxiliary functions -------------------- *)

let read_list input f =
  let len = IO.BigEndian.read_ui16 input in
  let items = Util.repeat_collect len f in
    items

let read_byte_list input f =
  let len = IO.read_byte input in
  let items = Util.repeat_collect len f in
    items

let safe_read_unsigned_i32 input =
  let i = IO.BigEndian.read_real_i32 input in
    if i < 0l || i > 0x3fffffffl (* max_int on 32bit machines *) then
      raise (ClassfileInputError "Attribute length overflow");
    Int32.to_int i

let read_constpool_idx input =
  let i = IO.BigEndian.read_ui16 input in
    CP.index_of_int i

let read_constpool_idxopt input =
  let i = IO.BigEndian.read_ui16 input in
    CP.index_option_of_int i

(* Reading in the constant pool *)
let read_constant_pool input size =
  let read_constant_pool_item () = let tag = IO.read_byte input in match tag with
    | 1  ->
	let len = IO.BigEndian.read_ui16 input in
	let s = IO.really_nread input len in
	  CP.CPutf8 s, 1
    | 3  ->
	let i = IO.BigEndian.read_real_i32 input in
	  CP.CPint i, 1
    | 4  -> 
	let f = JFloat.read input in
	  CP.CPfloat f, 1
    | 5  -> 
	let l = IO.BigEndian.read_i64 input in
	  CP.CPlong l, 2
    | 6  ->
	let d = Int64.float_of_bits (IO.BigEndian.read_i64 input) in
	  CP.CPdouble d, 2
    | 7  -> 
	let idx = read_constpool_idx input in
	  CP.CPclass idx, 1
    | 8  ->
	let idx = read_constpool_idx input in
	  CP.CPstring idx, 1
    | 9  ->
	let class_idx = read_constpool_idx input in
	let name_and_type_idx = read_constpool_idx input in
	  CP.CPfieldref (class_idx, name_and_type_idx), 1
    | 10 -> 
	let class_idx = read_constpool_idx input in
	let name_and_type_idx = read_constpool_idx input in
	  CP.CPmethodref (class_idx, name_and_type_idx), 1
    | 11 -> 
	let class_idx = read_constpool_idx input in
	let name_and_type_idx = read_constpool_idx input in
	  CP.CPimethodref (class_idx, name_and_type_idx), 1
    | 12 -> 
	let name_idx = read_constpool_idx input in
	let type_idx = read_constpool_idx input in
	  CP.CPnametype (name_idx, type_idx), 1
    | _  ->
	raise (ClassfileInputError ("Unknown constant pool tag "^ string_of_int tag))
  in
  let builder = CP.create_builder ~initial_size:size () in
  let rec loop idx =
    if idx > size then
      raise (ClassfileInputError "read_classpool: too many entries for size")
    else if idx = size then
      ()
    else
      let entry, delta = read_constant_pool_item () in
      let _ = CP.append_entry builder entry in
	loop (idx + delta)
  in
    loop 1;
    CP.pool_of_builder builder

(* reading in Java 5 annotations *)
let rec read_annotation input pool () =
  let type_idx = read_constpool_idx input in
  let elements = read_list input (read_named_element input pool) in
    (type_idx, elements)
and read_named_element input pool () =
  let name_idx = read_constpool_idx input in
  let value    = read_element_value input pool () in
    (name_idx, value)
and read_element_value input pool () =
  let make_const tag =
    let idx = read_constpool_idx input in
      CF.Const_Value (tag, idx)
  in
  let tag = IO.read_byte input in match Char.chr tag with
    | 'B' -> make_const CF.Byte
    | 'C' -> make_const CF.Char
    | 'D' -> make_const CF.Double
    | 'F' -> make_const CF.Float
    | 'I' -> make_const CF.Int
    | 'J' -> make_const CF.Long
    | 'S' -> make_const CF.Short
    | 'Z' -> make_const CF.Bool
    | 's' -> make_const CF.String
    | 'e' ->
	let type_name_idx  = read_constpool_idx input in
	let const_name_idx = read_constpool_idx input in
	  CF.Enum_Const_Value (type_name_idx, const_name_idx)
    | 'c' ->
	let class_idx = read_constpool_idx input in
	  CF.Class_Info class_idx
    | '@' ->
	let a = read_annotation input pool () in
	  CF.Annot_Value a
    | '[' ->
	let elems = read_list input (read_element_value input pool) in
	  CF.Array_Value elems
    | c ->
	raise (ClassfileInputError (Printf.sprintf "read_element_value: invalid tag: %c" c))

(* reading in Java 6 stack maps *)
let read_vtype_info input pool () =
  let tag = IO.read_byte input in match tag with
    | 0 -> CF.Top_vi
    | 1 -> CF.Integer_vi
    | 2 -> CF.Float_vi
    | 3 -> CF.Double_vi
    | 4 -> CF.Long_vi
    | 5 -> CF.Null_vi
    | 6 -> CF.UninitializedThis_vi
    | 7 -> let index = read_constpool_idx input in CF.Object_vi index
    | 8 -> let offset = IO.BigEndian.read_ui16 input in CF.Uninitialized_vi offset
    | _ -> raise (ClassfileInputError (Printf.sprintf "read_vtype_info: invalid tag: %d" tag))

let read_stackmap_frame input pool () =
  let tag = IO.read_byte input in 
    if 0 <= tag && tag <= 63 then         (* same_frame *)
      (tag, CF.Same_frame)
    else if 64 <= tag && tag <= 127 then  (* same_locals_1_stack_item *)
      let delta = tag - 64 in
      let vtype = read_vtype_info input pool () in
	(delta, CF.Same_locals_1_stk vtype)
    else if 128 <= tag && tag <= 246 then (* reserved *)
      raise (ClassfileInputError (Printf.sprintf "read_stackmap_frame: invalid stackmap tag %d" tag))
    else if tag = 247 then                (* same_locals_1_stack_item_extended *)
      let delta = IO.BigEndian.read_ui16 input in
      let vtype = read_vtype_info input pool () in
	(delta, CF.Same_locals_1_stk vtype)
    else if 248 <= tag && tag <= 250 then (* chop frame *)
      let k = 251 - tag in
      let delta = IO.BigEndian.read_ui16 input in
	(delta, CF.Chop_frame k)
    else if tag = 251 then                (* same_frame_extended *)
      let delta = IO.BigEndian.read_ui16 input in
	(delta, CF.Same_frame)
    else if 252 <= tag && tag <= 254 then (* append_frame *)
      let delta = IO.BigEndian.read_ui16 input in
      let num = tag - 251 in
      let vtypes = Util.repeat_collect num (read_vtype_info input pool) in
	(delta, CF.Append_frame vtypes)
    else if tag = 255 then                (* full_frame *)
      let delta = IO.BigEndian.read_ui16 input in
      let locals = read_list input (read_vtype_info input pool) in
      let stack = read_list input (read_vtype_info input pool) in
	(delta, CF.Full_frame (locals, stack))
    else
      raise (ClassfileInputError (Printf.sprintf "read_stackmap_frame: IO.read_byte gave us a value which is not a byte : %d" tag))

(* reading in CLDC stack maps *)
let read_cldc_stackmap_frame input pool () =
  let offset = IO.BigEndian.read_ui16 input in
  let locals = read_list input (read_vtype_info input pool) in
  let stack  = read_list input (read_vtype_info input pool) in
    (offset, CF.CLDC_full_frame (locals, stack))

(* reading in exception handlers for code attributes *)
let read_exception_handler input pool () =
  let start_pc   = IO.BigEndian.read_ui16 input in
  let end_pc     = IO.BigEndian.read_ui16 input in
  let handler_pc = IO.BigEndian.read_ui16 input in
  let catch_type = read_constpool_idxopt input in
    if end_pc < start_pc then raise (ClassfileInputError "read_exception_handler: end before start");
    { CF.exn_start = start_pc
    ; CF.exn_end   = end_pc
    ; CF.exn_pc    = handler_pc
    ; CF.exn_type  = catch_type
    }

(* reading in attributes: most of the work is done here *)
let rec read_attribute input pool () =
  let attr_name_idx = read_constpool_idx input in
  let attr_name     = CP.lookup_utf8 pool attr_name_idx in
  let attr_len      = safe_read_unsigned_i32 input in
  let l_input       = Util.IO.limited_input attr_len input in
  let attr_data     = read_specific_attribute l_input attr_name attr_len pool in
    CF.Attribute (attr_name_idx, attr_data)

and read_specific_attribute input attr_name attr_len pool = 
  match attr_name with
  | "ConstantValue" ->
      let const_val_idx = read_constpool_idx input in
	CF.Attr_ConstantValue const_val_idx
  | "Code" ->
      let max_stack   = IO.BigEndian.read_ui16 input in
      let max_locals  = IO.BigEndian.read_ui16 input in
      let code_length = safe_read_unsigned_i32 input in
      let code        =
	try LowlevelBytecode.read_code input code_length
	with LowlevelBytecode.Invalid_bytecode s -> raise (ClassfileInputError ("read_code: " ^ s))
      in
      let exc_table   = read_list input (read_exception_handler input pool) in
      let attrs       = read_list input (read_attribute input pool) in
	CF.Attr_Code (max_stack, max_locals,
		      code, exc_table, attrs)
  | "Exceptions" ->
      let exc_idxs = read_list input (fun () -> read_constpool_idx input) in
	CF.Attr_Exceptions exc_idxs
  | "InnerClasses" ->
      let read_inner_class () =
	let inner_info_idx = read_constpool_idxopt input in
	let outer_info_idx = read_constpool_idxopt input in
	let inner_name_idx = read_constpool_idxopt input in
	let inner_flags    = IO.BigEndian.read_ui16 input in
	  { CF.inner_info  = inner_info_idx
	  ; CF.outer_info  = outer_info_idx
	  ; CF.inner_name  = inner_name_idx
	  ; CF.inner_flags = AccessFlags.class_flags_of_ui16 inner_flags
	  }
      in
      let classes = read_list input read_inner_class in
	CF.Attr_InnerClasses classes
  | "EnclosingMethod" ->
      let class_index  = read_constpool_idx input in
      let method_index = read_constpool_idxopt input in
	CF.Attr_EnclosingMethod (class_index, method_index)
  | "Synthetic" ->
      if attr_len = 0 then
	CF.Attr_Synthetic
      else
	raise (ClassfileInputError "read_specific_attribute: 'Synthetic' attribute of non-zero length")
  | "Signature" ->
      let sig_index = read_constpool_idx input in
	CF.Attr_Signature sig_index
  | "SourceFile" ->
      let srcfile_idx = read_constpool_idx input in
	CF.Attr_SourceFile srcfile_idx
  | "SourceDebugExtension" ->
      let s = IO.really_nread input attr_len in
	CF.Attr_SourceDebugExtension s
  | "LineNumberTable" ->
      let read_lineref () =
	let start_pc = IO.BigEndian.read_ui16 input in
	let line_number = IO.BigEndian.read_ui16 input in
	  { CF.ln_start = start_pc
	  ; CF.ln_line  = line_number
	  }
      in
      let table = read_list input read_lineref in
	CF.Attr_LineNumberTable table
  | "LocalVariableTable" ->
      let read_item () =
	let start_pc   = IO.BigEndian.read_ui16 input in
	let length     = IO.BigEndian.read_ui16 input in
	let name_index = read_constpool_idx input in
	let desc_index = read_constpool_idx input in
	let index      = IO.BigEndian.read_ui16 input in
	{ CF.lv_start = start_pc
	; CF.lv_length = length
	; CF.lv_name   = name_index
	; CF.lv_desc   = desc_index
	; CF.lv_index  = index
	}
      in
      let table = read_list input read_item in
	CF.Attr_LocalVariableTable table
  | "Deprecated" ->
      if attr_len = 0 then
	CF.Attr_Deprecated
      else
	raise (ClassfileInputError "read_specific_attribute: 'Deprecated' attribute of non-zero length")
  | "RuntimeVisibleAnnotations" ->
      let annots = read_list input (read_annotation input pool) in
	CF.Attr_RuntimeVisibleAnnotations annots
  | "RuntimeInvisibleAnnotations" ->
      let annots = read_list input (read_annotation input pool) in
	CF.Attr_RuntimeInvisibleAnnotations annots
  | "RuntimeVisibleParameterAnnotations" ->
      let l = read_byte_list input (fun () -> read_list input (read_annotation input pool)) in
	CF.Attr_RuntimeVisibleParameterAnnotations l
  | "RuntimeInvisibleParameterAnnotations" ->
      let l = read_byte_list input (fun () -> read_list input (read_annotation input pool)) in
	CF.Attr_RuntimeInvisibleParameterAnnotations l
  | "AnnotationDefault" ->
      let elt = read_element_value input pool () in
	CF.Attr_AnnotationDefault elt
  | "StackMapTable" -> (* Java 6 style stack maps *)
      let t = read_list input (read_stackmap_frame input pool) in
	CF.Attr_StackMapTable t
  | "StackMap" -> (* CLDC/MIDP style stack maps *)
      let t = read_list input (read_cldc_stackmap_frame input pool) in
	CF.Attr_StackMap t
  | x ->
      let s = IO.really_nread input attr_len in
	CF.Attr s

let read_method input constant_pool () =
  let access_flags     = IO.BigEndian.read_ui16 input in
  let name_index       = read_constpool_idx input in
  let descriptor_index = read_constpool_idx input in
  let attributes       = read_list input (read_attribute input constant_pool) in
    { CF.m_flags = AF.method_flags_of_ui16 access_flags
    ; CF.m_name  = name_index
    ; CF.m_desc  = descriptor_index
    ; CF.m_attrs = attributes
    }

let read_field input constant_pool () =
  let access_flags     = IO.BigEndian.read_ui16 input in
  let name_index       = read_constpool_idx input in
  let descriptor_index = read_constpool_idx input in
  let attributes       = read_list input (read_attribute input constant_pool) in
    { CF.f_flags = AF.field_flags_of_ui16 access_flags
    ; CF.f_name  = name_index
    ; CF.f_desc  = descriptor_index
    ; CF.f_attrs = attributes
    }

(* -------------------- Main function -------------------- *)

(* FIXME:
   exceptions this function can throw:
   - ClassfileInputError
   - IO.No_more_input
   - Constpool.BadLookup
   - Constpool.BadIndex
   - Whatever the underlying IO can throw
   - Should catch all exceptions and wrap them in ClassfileInputError
*)

let read_classfile input =
  let magic = IO.BigEndian.read_real_i32 input in
  let minor = IO.BigEndian.read_ui16 input in
  let major = IO.BigEndian.read_ui16 input in
  let () = if magic <> 0xCAFEBABEl then raise (ClassfileInputError (Printf.sprintf "Bad magic number %lx" magic)) in

  let cp_count = IO.BigEndian.read_ui16 input in
  let pool     = read_constant_pool input cp_count in

  let access_flags = AF.class_flags_of_ui16 (IO.BigEndian.read_ui16 input) in
  let this_class   = read_constpool_idx input in
  let super_class  = read_constpool_idxopt input in
  let interfaces   = read_list input (fun () -> CP.index_of_int (IO.BigEndian.read_ui16 input)) in

  let fields     = read_list input (read_field input pool) in
  let methods    = read_list input (read_method input pool) in
  let attributes = read_list input (read_attribute input pool) in

  let () = try let _ = IO.read_byte input in raise (ClassfileInputError ("Extra data at end of class file")) with IO.No_more_input -> () in

  { CF.minor   = minor
  ; CF.major   = major
  ; CF.pool    = pool
  ; CF.flags   = access_flags
  ; CF.this    = this_class
  ; CF.super   = super_class
  ; CF.ifcs    = interfaces
  ; CF.fields  = fields
  ; CF.methods = methods
  ; CF.attrs   = attributes
  }

(* Strictly, we should check that there's no superfluous data at the end of the classfile *)

let of_file infile =
  let is = open_in_bin infile 
  in let ic = IO.input_channel is
  in let cf =
    try read_classfile ic
    with e -> IO.close_in ic; close_in is; raise e
  in let () = IO.close_in ic 
  in let () = close_in is 
  in cf
