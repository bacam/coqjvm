val trivial_code_annot   : CoqModules.PlainAnn.code_annotation
(* trivial_method_annot is now in coq *)
val trivial_class_annot  : CoqModules.PlainAnn.class_annotation

val trans_code_annot : Ocaml_jvml.Constpool.pool ->
                       int array ->
                       Ocaml_jvml.Classfile.attribute list ->
                       CoqModules.PlainAnn.code_annotation
val trans_method_annot : Ocaml_jvml.Constpool.pool ->
                         Ocaml_jvml.Classfile.method_decl ->
                         CoqModules.PlainAnn.method_annotation
val trans_class_annot : Ocaml_jvml.Constpool.pool ->
                        Ocaml_jvml.Classfile.class_file ->
                        CoqModules.PlainAnn.class_annotation
