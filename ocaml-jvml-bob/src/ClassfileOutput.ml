(* ---------------------------- Classfile output ----------------------------*)

module CF = Classfile
module CP = Constpool
module AF = AccessFlags

exception ClassfileOutputError of string

let write_list output f l =
  let len = List.length l in
    if len > 0xfff then raise (IO.Overflow "list too long"); (* or rely on write_ui16 to check? *)
    IO.BigEndian.write_ui16 output len;
    List.iter f l

let write_byte_list output f l =
  let len = List.length l in
    if len > 255 then raise (IO.Overflow "list too long for byte-length list");
    IO.write_byte output (List.length l);
    List.iter f l

let write_constpool_idx output idx =
  IO.BigEndian.write_ui16 output (CP.index_to_int idx)

let write_constpool_idxopt output idxopt = match idxopt with
  | None     -> IO.BigEndian.write_ui16 output 0
  | Some idx -> write_constpool_idx output idx

let write_constant_pool output pool =
  let write_constant_pool_item entry = match entry with
    | CP.CPclass idx ->
	IO.write_byte output 7;
	write_constpool_idx output idx
    | CP.CPfieldref (class_idx, nt_idx) ->
	IO.write_byte output 9;
	write_constpool_idx output class_idx;
	write_constpool_idx output nt_idx
    | CP.CPmethodref (class_idx, nt_idx) ->
	IO.write_byte output 10;
	write_constpool_idx output class_idx;
	write_constpool_idx output nt_idx
    | CP.CPimethodref (class_idx, nt_idx) ->
	IO.write_byte output 11;
	write_constpool_idx output class_idx;
	write_constpool_idx output nt_idx
    | CP.CPstring idx ->
	IO.write_byte output 8;
	write_constpool_idx output idx
    | CP.CPint i ->
	IO.write_byte output 3;
	IO.BigEndian.write_real_i32 output i
    | CP.CPfloat f ->
	IO.write_byte output 4;
	JFloat.write output f
    | CP.CPlong l ->
	IO.write_byte output 5;
	IO.BigEndian.write_i64 output l
    | CP.CPdouble d ->
	IO.write_byte output 6;
	IO.BigEndian.write_i64 output (Int64.bits_of_float d)
    | CP.CPnametype (name_idx, desc_idx) ->
	IO.write_byte output 12;
	write_constpool_idx output name_idx;
	write_constpool_idx output desc_idx
    | CP.CPutf8 str ->
	IO.write_byte output 1;
	IO.BigEndian.write_ui16 output (String.length str);
	IO.nwrite output str
  in
    IO.BigEndian.write_ui16 output (CP.size pool);
    CP.iter write_constant_pool_item pool

let write_exception_handler output e =
  IO.BigEndian.write_ui16 output e.CF.exn_start;
  IO.BigEndian.write_ui16 output e.CF.exn_end;
  IO.BigEndian.write_ui16 output e.CF.exn_pc;
  write_constpool_idxopt output e.CF.exn_type

let write_linenumber_info output l =
  IO.BigEndian.write_ui16 output l.CF.ln_start;
  IO.BigEndian.write_ui16 output l.CF.ln_line

let write_localvariable_info output l =
  IO.BigEndian.write_ui16 output l.CF.lv_start;
  IO.BigEndian.write_ui16 output l.CF.lv_length;
  write_constpool_idx output l.CF.lv_name;
  write_constpool_idx output l.CF.lv_desc;
  IO.BigEndian.write_ui16 output l.CF.lv_index

let write_localvartype_info output l =
  IO.BigEndian.write_ui16 output l.CF.vt_start;
  IO.BigEndian.write_ui16 output l.CF.vt_length;
  write_constpool_idx output l.CF.vt_name;
  write_constpool_idx output l.CF.vt_sign;
  IO.BigEndian.write_ui16 output l.CF.vt_index

let write_innerclass_info output i =
  write_constpool_idxopt output i.CF.inner_info;
  write_constpool_idxopt output i.CF.outer_info;
  write_constpool_idxopt output i.CF.inner_name;
  IO.BigEndian.write_ui16 output (AF.ui16_of_class_flags i.CF.inner_flags)

let rec write_annotation_element output el = match el with
  | CF.Const_Value (type_tag, idx) ->
      IO.write output (match type_tag with
			 | CF.Byte      -> 'B'
			 | CF.Char      -> 'C'
			 | CF.Double    -> 'D'
			 | CF.Float     -> 'F'
			 | CF.Int       -> 'I'
			 | CF.Long      -> 'J'
			 | CF.Short     -> 'S'
			 | CF.Bool      -> 'Z'
			 | CF.String    -> 's');
      write_constpool_idx output idx
  | CF.Enum_Const_Value (type_name, const_name) ->
      IO.write output 'e';
      write_constpool_idx output type_name;
      write_constpool_idx output const_name
  | CF.Class_Info idx ->
      IO.write output 'c';
      write_constpool_idx output idx
  | CF.Annot_Value annot ->
      IO.write output '@';
      write_annotation output annot
  | CF.Array_Value l ->
      IO.write output '[';
      write_list output (write_annotation_element output) l

and write_named_element output (name_index, element) =
  write_constpool_idx output name_index;
  write_annotation_element output element

and write_annotation output (type_index, params) =
  write_constpool_idx output type_index;
  write_list output (write_named_element output) params

(* writing stack maps *)
let write_vtype_info output v = match v with
  | CF.Top_vi               -> IO.write_byte output 0
  | CF.Integer_vi           -> IO.write_byte output 1
  | CF.Float_vi             -> IO.write_byte output 2
  | CF.Long_vi              -> IO.write_byte output 4
  | CF.Double_vi            -> IO.write_byte output 3
  | CF.Null_vi              -> IO.write_byte output 5
  | CF.UninitializedThis_vi -> IO.write_byte output 6
  | CF.Object_vi idx        -> IO.write_byte output 7; write_constpool_idx output idx
  | CF.Uninitialized_vi loc -> IO.write_byte output 8; IO.BigEndian.write_ui16 output loc

let write_stackmapframe output (delta, frame) = match frame with
  | CF.Same_frame when delta <= 63             -> IO.write_byte output delta
  | CF.Same_frame                              -> IO.write_byte output 251; IO.BigEndian.write_ui16 output delta
  | CF.Same_locals_1_stk item when delta <= 63 -> IO.write_byte output (delta+64); write_vtype_info output item
  | CF.Same_locals_1_stk item                  -> IO.write_byte output 247; IO.BigEndian.write_ui16 output delta; write_vtype_info output item
  | CF.Chop_frame n when 1 <= n && n <= 3      -> IO.write_byte output (251-n); IO.BigEndian.write_ui16 output delta
  | CF.Chop_frame n                            -> raise (ClassfileOutputError (Printf.sprintf "write_stackmapframe: Invalid tag %d in Chop_frame (should be 1, 2 or 3)" n))
  | CF.Append_frame locals ->
      let n = List.length locals in
	if 1 <= n && n <= 3 then
	  (IO.write_byte output (251+n);
	   IO.BigEndian.write_ui16 output delta;
	   List.iter (write_vtype_info output) locals)
	else
	  raise (ClassfileOutputError (Printf.sprintf "write_stackmapframe: wrong number of locals (%d) in Append_frame (should be 1, 2 or 3)" n))
  | CF.Full_frame (locals, stack) ->
      IO.write_byte output 255;
      IO.BigEndian.write_ui16 output delta;
      write_list output (write_vtype_info output) locals;
      write_list output (write_vtype_info output) stack

let write_cldcstackframe output (loc, CF.CLDC_full_frame (locals, stack)) =
  IO.BigEndian.write_ui16 output loc;
  write_list output (write_vtype_info output) locals;
  write_list output (write_vtype_info output) stack

(* This trick with recursive modules is used to get around the lack of
   polymorphic recursion in OCaml. We want write_attribute to have
   type 'a IO.output -> attribute -> unit, but the use of a string
   IO.output internally forces the outermost type to be string
   IO.output -> ... . Trick due to Jeremy Yallop:

   http://caml.inria.fr/pub/ml-archives/caml-list/2007/04/ae7f124ffddc77cb092d42385d04e040.en.html
*)
module rec WriteAttribute :
sig val write_attribute : 'a IO.output -> CF.attribute -> unit end =
struct 
  let rec write_attribute output (CF.Attribute (name_idx, attr)) =
    let output'    = IO.output_string () in
    let _          = write_specific_attribute output' attr in
    let attr_bytes = IO.close_out output' in
      write_constpool_idx output name_idx;
      IO.BigEndian.write_i32 output (String.length attr_bytes);
      IO.nwrite output attr_bytes

  and write_specific_attribute output attr = match attr with
    | CF.Attr_ConstantValue value_idx ->
	write_constpool_idx output value_idx
    | CF.Attr_Code (max_stack, max_locals, code, hdlrs, attrs) ->
	IO.BigEndian.write_ui16 output max_stack;
	IO.BigEndian.write_ui16 output max_locals;
	IO.BigEndian.write_i32 output (Array.length code);
	LowlevelBytecode.write_code code output;
	write_list output (write_exception_handler output) hdlrs;
	write_list output (WriteAttribute.write_attribute output) attrs
    | CF.Attr_Exceptions exns ->
	write_list output (write_constpool_idx output) exns
    | CF.Attr_InnerClasses classes ->
	write_list output (write_innerclass_info output) classes
    | CF.Attr_EnclosingMethod (cl, mthd) ->
	write_constpool_idx output cl;
	write_constpool_idxopt output mthd
    | CF.Attr_Synthetic ->
	()
    | CF.Attr_Signature signature ->
	write_constpool_idx output signature
    | CF.Attr_SourceFile file ->
	write_constpool_idx output file
    | CF.Attr_SourceDebugExtension txt ->
	IO.nwrite output txt
    | CF.Attr_LineNumberTable lines ->
	write_list output (write_linenumber_info output) lines
    | CF.Attr_LocalVariableTable vars ->
	write_list output (write_localvariable_info output) vars
    | CF.Attr_LocalVariableTypeTable vartypes ->
	write_list output (write_localvartype_info output) vartypes
    | CF.Attr_Deprecated ->
	()
    | CF.Attr_RuntimeVisibleAnnotations annotations 
    | CF.Attr_RuntimeInvisibleAnnotations annotations ->
	write_list output (write_annotation output) annotations
    | CF.Attr_RuntimeVisibleParameterAnnotations annotations
    | CF.Attr_RuntimeInvisibleParameterAnnotations annotations ->
	write_byte_list output (write_list output (write_annotation output)) annotations
    | CF.Attr_AnnotationDefault default_value ->
	write_annotation_element output default_value
    | CF.Attr_StackMapTable m ->
	write_list output (write_stackmapframe output) m
    | CF.Attr_StackMap m ->
	write_list output (write_cldcstackframe output) m
    | CF.Attr txt ->
	IO.nwrite output txt
end

let write_method output method_decl =
  IO.BigEndian.write_ui16 output (AF.ui16_of_method_flags method_decl.CF.m_flags);
  write_constpool_idx output method_decl.CF.m_name;
  write_constpool_idx output method_decl.CF.m_desc;
  write_list output (WriteAttribute.write_attribute output) method_decl.CF.m_attrs

let write_field output field_decl =
  IO.BigEndian.write_ui16 output (AF.ui16_of_field_flags field_decl.CF.f_flags);
  write_constpool_idx output field_decl.CF.f_name;
  write_constpool_idx output field_decl.CF.f_desc;
  write_list output (WriteAttribute.write_attribute output) field_decl.CF.f_attrs

let write_classfile output cf =
  IO.BigEndian.write_real_i32 output 0xCAFEBABEl;
  IO.BigEndian.write_ui16 output cf.CF.minor;
  IO.BigEndian.write_ui16 output cf.CF.major;
  write_constant_pool output cf.CF.pool;
  IO.BigEndian.write_ui16 output (AF.ui16_of_class_flags cf.CF.flags);
  write_constpool_idx output cf.CF.this;
  write_constpool_idxopt output cf.CF.super;
  write_list output (write_constpool_idx output) cf.CF.ifcs;
  write_list output (write_field output) cf.CF.fields;
  write_list output (write_method output) cf.CF.methods;
  write_list output (WriteAttribute.write_attribute output) cf.CF.attrs

let to_file cf filename =
  let out = open_out_bin filename in
  let out' = IO.output_channel out in
  let _ = write_classfile out' cf in
  let () = IO.close_out out' in
  let () = close_out out in
    ()
