Require Import MLStrings.

(* Messages that are ocaml string constants. *)
Axiom err_cycle : MLString.
Extract Constant err_cycle => """Cycle in recursive lookup at """.
Axiom err_notfound : MLString.
Extract Constant err_notfound => """Not found: """.
Axiom err_noproof   : MLString.
Extract Constant err_noproof    => """No proof present for """.
Axiom err_badproof  : MLString.
Extract Constant err_badproof   => """Bad proof present for """.
Axiom err_entails   : MLString.
Extract Constant err_entails    => """ entails """.
Axiom err_emptycode : MLString.
Extract Constant err_emptycode  => """Empty bytecode array""".
Axiom err_native_missing : MLString.
Extract Constant err_native_missing => """Missing native method""".
Axiom err_native_bad_spec : MLString.
Extract Constant err_native_bad_spec => """Specification for native method does not match specification in class""".
Axiom err_incomplete : MLString.
Extract Constant err_incomplete => """Failed to complete certificate""".
Axiom err_checkmethod : MLString.
Extract Constant err_checkmethod => """Failed to check method: """.
Axiom err_poorcert : MLString.
Extract Constant err_poorcert   => """Certificate does not contain required assertion at pc """.
Axiom err_badoffset : MLString.
Extract Constant err_badoffset  => """Bad offset in bytecode at pc """.
Axiom err_unsupported : MLString.
Extract Constant err_unsupported => """Unsupported bytecode instruction at pc """.
Axiom err_missingcpinfo : MLString.
Extract Constant err_missingcpinfo => """Information missing from constant pool at pc """.
Axiom err_missingcpainfo : MLString.
Extract Constant err_missingcpainfo => """Information missing from additional constant pool at pc """.
Axiom err_sep : MLString.
Extract Constant err_sep => """: """.

Axiom err_overriding_problem : MLString.
Extract Constant err_overriding_problem => """Problem during overriding checking """.
Axiom err_duplicate_method : MLString.
Extract Constant err_duplicate_method => """Duplicate method""".
Axiom err_overriding_failure : MLString.
Extract Constant err_overriding_failure => """ Overriding failure (proof failed)""".
Axiom err_limit_exceeded : MLString.
Extract Constant err_limit_exceeded => """Inheritance limit exceeded""".
Axiom err_class_should_be_interface : MLString.
Extract Constant err_class_should_be_interface => """Class should be interface""".
Axiom err_class_should_not_be_interface : MLString.
Extract Constant err_class_should_not_be_interface => """Class should not be interface""".
Axiom err_no_spec_found_for_class : MLString.
Extract Constant err_no_spec_found_for_class => """No spec found for class""".
Axiom err_preclass_should_have_superclass : MLString.
Extract Constant err_preclass_should_have_superclass => """Preclass should have superclass""".
Axiom err_preclass_no_exist : MLString.
Extract Constant err_preclass_no_exist => """Preclass doesn't exist""".
Axiom err_cpae_bad : MLString.
Extract Constant err_cpae_bad => """Bad constant pool additional entry """.
Axiom err_no_impl : MLString.
Extract Constant err_no_impl => """No implementation for method """.
Axiom err_implementing_failure : MLString.
Extract Constant err_implementing_failure => """Implementing interface failure (proof failed) for """.
Axiom err_grants_no_privilege : MLString.
Extract Constant err_grants_no_privilege => """Method has grants annotation but is in unprivileged class""".

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)
