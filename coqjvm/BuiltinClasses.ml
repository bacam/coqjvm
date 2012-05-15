open Common.Types
open CoqModules
open TranslateAnnos

let make_class (name, opt_parent_name) =
  { C.preclass_name = name
  ; C.preclass_super_name = opt_parent_name
  ; C.preclass_super_interfaces = []
  ; C.preclass_public = true
  ; C.preclass_final = false
  ; C.preclass_super = false
  ; C.preclass_interface = false
  ; C.preclass_abstract = false
  ; C.preclass_methods =
      [{ C.premethod_name = "<init>"
	    ; C.premethod_descriptor = { C.descriptor_ret_type = None; C.descriptor_arg_types = [] }
	    ; C.premethod_public = true
	    ; C.premethod_protected = false
	    ; C.premethod_private = false
	    ; C.premethod_abstract = false
	    ; C.premethod_static = false
	    ; C.premethod_final = false
	    ; C.premethod_synchronized = false
	    ; C.premethod_strict = false
	    ; C.premethod_code = Some { C.precode_code = [C.Coq_op_return]
				      ; C.precode_max_lvars = S O
				      ; C.precode_max_stack = O
				      ; C.precode_exception_table = []
				      ; C.precode_annot = trivial_code_annot }
	    ; C.premethod_annot = PlainAnn.trivial_method_annotation
      }]
  ; C.preclass_fields = C.FieldList.empty
  ; C.preclass_constantpool = C.ConstantPool.empty
  ; C.preclass_annotation = trivial_class_annot
  }

let boot_classes =
  [ BasicsImpl.java_lang_Object, None
  ; BasicsImpl.java_lang_Throwable, Some BasicsImpl.java_lang_Object
  ; BasicsImpl.java_lang_Error, Some BasicsImpl.java_lang_Throwable
  ; BasicsImpl.java_lang_LinkageError, Some BasicsImpl.java_lang_Error
  ; BasicsImpl.java_lang_ClassCircularityError, Some BasicsImpl.java_lang_LinkageError
  ; BasicsImpl.java_lang_ClassFormatError, Some BasicsImpl.java_lang_LinkageError
  ; BasicsImpl.java_lang_IncompatibleClassChangeError, Some BasicsImpl.java_lang_LinkageError
  ; BasicsImpl.java_lang_NoClassDefFoundError, Some BasicsImpl.java_lang_LinkageError
  ; BasicsImpl.java_lang_AbstractMethodError, Some BasicsImpl.java_lang_IncompatibleClassChangeError
  ; BasicsImpl.java_lang_IllegalAccessError, Some BasicsImpl.java_lang_IncompatibleClassChangeError
  ; BasicsImpl.java_lang_InstantiationError, Some BasicsImpl.java_lang_IncompatibleClassChangeError
  ; BasicsImpl.java_lang_NoSuchFieldError, Some BasicsImpl.java_lang_IncompatibleClassChangeError
  ; BasicsImpl.java_lang_NoSuchMethodError, Some BasicsImpl.java_lang_IncompatibleClassChangeError
  ; BasicsImpl.java_lang_VerifyError, Some BasicsImpl.java_lang_LinkageError
  ; BasicsImpl.java_lang_Exception, Some BasicsImpl.java_lang_Throwable
  ; BasicsImpl.java_lang_RuntimeException, Some BasicsImpl.java_lang_Exception
  ; BasicsImpl.java_lang_NullPointerException, Some BasicsImpl.java_lang_RuntimeException
  ; BasicsImpl.java_lang_ClassCastException, Some BasicsImpl.java_lang_RuntimeException
  ]

let boot_preclasses =
  List.fold_left
    (fun preclasses (nm,snm) ->
       CP.Preclasspool.update preclasses nm (make_class (nm,snm)))
    CP.Preclasspool.empty
    boot_classes
