module Int32 = struct
  type t = int32

  let zero = Int32.zero
  let one = Int32.one
  let minus_one = Int32.minus_one
  let neg = Int32.neg
  let add = Int32.add
  let sub = Int32.sub
  let mul = Int32.mul
  let div = Int32.div
  let logor = Int32.logor
  let logand = Int32.logand
  let logxor = Int32.logxor
  let rem = Int32.rem
  let eq a b = a=b
  let neq a b = not (a=b)
  let lt a b = a < b
  let le a b = a <= b
  let gt a b = a > b
  let ge a b = a >= b
end

let coq_compare a b =
  let r = compare a b in
    if r < 0 then Coqextract.OrderedType.LT
    else if r = 0 then Coqextract.OrderedType.EQ
    else Coqextract.OrderedType.GT

module Classname = struct
  type t = Ocaml_jvml.Jvmtype.jclass
  let eq_dec (a:t) (b:t) = (a = b)
  let compare = coq_compare
  let to_string (pkgs,cls) = String.concat "." (pkgs@[cls])
end

module Methodname = struct
  type t = string
  let eq_dec = (=)
  let compare = coq_compare
  let to_string x = x
end

module Fieldname = struct
  type t = string
  let eq_dec = (=)
  let compare = coq_compare
  let to_string x = x
end

module ConstantPoolRef = struct
  type t = Ocaml_jvml.Constpool.index
  let eq_dec = (=)
  let compare = coq_compare
  let to_string i = string_of_int (Ocaml_jvml.Constpool.index_to_int i)
end

let java_lang_Object = (["java";"lang"],"Object")
let java_lang_Throwable = (["java";"lang"],"Throwable")
let java_lang_Error = (["java";"lang"],"Error")
let java_lang_LinkageError = (["java";"lang"],"LinkageError")
let java_lang_ClassCircularityError = (["java";"lang"],"ClassCircularityError")
let java_lang_ClassFormatError = (["java";"lang"],"ClassFormatError")
let java_lang_IncompatibleClassChangeError = (["java";"lang"],"IncompatibleClassChangeError")
let java_lang_NoClassDefFoundError = (["java";"lang"],"NoClassDefFoundError")
let java_lang_AbstractMethodError = (["java";"lang"],"AbstractMethodError")
let java_lang_IllegalAccessError = (["java";"lang"],"IllegalAccessError")
let java_lang_InstantiationError = (["java";"lang"],"InstantiationError")
let java_lang_NoSuchFieldError = (["java";"lang"],"NoSuchFieldError")
let java_lang_NoSuchMethodError = (["java";"lang"],"NoSuchMethodError")
let java_lang_VerifyError = (["java";"lang"],"VerifyError")
let java_lang_Exception = (["java";"lang"],"Exception")
let java_lang_RuntimeException = (["java";"lang"],"RuntimeException")
let java_lang_NullPointerException = (["java";"lang"],"NullPointerException")
let java_lang_ClassCastException = (["java";"lang"],"ClassCastException")
let init = "<init>"
