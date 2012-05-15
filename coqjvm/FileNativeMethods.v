Require Import ClassDatatypesIface.
Require Import CertRuntimeTypesIface.
Require Import JVMState.
Require Import List.
Require Import NativeMethods.

Require Import BasicMachineTypes.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import ResolutionIface.
Require Import VirtualMethodLookupIface.
Require Import ResourceAlgebra.
Require Import AnnotationIface.


Module Type FileImpl.

Axiom nint : Set.
(* Not sure how much I can rely on evaluation order... *)
Axiom open_file  : nint -> nint.
Axiom read_int   : nint -> nint.
Axiom close_file : nint -> nint.

Axiom classnames  : Set.
Axiom methodnames : Set.
Axiom fileclass : classnames.
Axiom openmeth  : methodnames.
Axiom readmeth  : methodnames.
Axiom closemeth : methodnames.

End FileImpl.

Module FileNativeMethods
  (B   : BASICS)
  (RA  : RESOURCE_ALGEBRA B)
  (ANN : ANNOTATION B)
  (C   : CLASSDATATYPES B ANN)
  (CP  : CLASSPOOL B ANN C)
  (A   : ASSIGNABILITY B ANN C CP)
  (R   : RESOLUTION B ANN C CP A)
  (VM  : VIRTUALMETHODLOOKUP B ANN C CP A)
  (RDT : CERTRUNTIMETYPES B ANN C CP A)
  (JVM : JVMSTATE B RA ANN C CP A R VM RDT)
  (F : FileImpl with Definition nint := B.Int32.t with Definition classnames := B.Classname.t with Definition methodnames := B.Methodname.t)
  <: NATIVE_METHODS B RA ANN C CP A R VM RDT JVM.

Inductive resultval : Type :=
 | void : resultval
 | val  : RDT.rt_val -> resultval
 | exn  : Heap.addr_t   -> resultval.

Record result : Type :=
 { resval   : resultval
 ; classes  : CP.cert_classpool
 ; heap     : RDT.cert_heap classes
 ; static   : RDT.cert_fieldstore classes heap
 ; res      : RA.res
 ; reslimit : RA.res
 }.

Definition native_invoke :=
  fun cls mth args state =>
    if B.Classname.eq_dec (C.class_name cls) F.fileclass then
      if B.Methodname.eq_dec (C.method_name mth) F.openmeth then
        match args with
          | RDT.rt_int file::nil =>
            match state with
              | RDT.mkState fs classes heap static res reslimit =>
                Some (Build_result (val (RDT.rt_int (F.open_file file))) classes heap static res reslimit)
            end
          | _ => None (* type error *)
        end
        else if B.Methodname.eq_dec (C.method_name mth) F.readmeth then
          match args with
            | RDT.rt_int file::nil =>
              match state with
                | RDT.mkState fs classes heap static res reslimit =>
                Some (Build_result (val (RDT.rt_int (F.read_int file))) classes heap static res reslimit)
              end
            | _ => None (* type error *)
          end
          else if B.Methodname.eq_dec (C.method_name mth) F.closemeth then
            match args with
              | RDT.rt_int file::nil =>
                match state with
                  | RDT.mkState fs classes heap static res reslimit =>
                    Some (Build_result (val (RDT.rt_int (F.close_file file))) classes heap static res reslimit)
                end
              | _ => None (* type error *)
            end
            else None (* unknown method, maybe should throw exception *)
      else None (* unknown class, maybe should throw exception *)
.

End FileNativeMethods.