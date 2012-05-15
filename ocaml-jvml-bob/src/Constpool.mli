(** Representation of constant pools and functions for building them.
*)

(**{1 Constant pools}
   
   Each [.class] file contains a constant pool containing constants
   referenced by the other members of the file. This module contains
   types and functions for representing constant pools and
   constructing constant pools.
*)


(**{2 Constant pool indexes}

   Indexes into the constant pool are represented in [.class] files as
   16 bit unsigned integers, where [0] is invalid. The value [0] is
   not used by the JVM so that optional references to the constant
   pool may be represented. For the O'Caml representation we take the
   type of indexes to be abstract so we can preserve these two
   constraints. Optional references to the constant pool are
   represented by [index option].
*)


(** Exception thrown when an attempt is made to construct a constant
    pool index that is out of range i.e not a non-zero unsigned 16bit
    value. *)
exception BadIndex of int

(** Abstract type of constant pool indexes. An integer in the range
    [[1,0xffff]]. *)
type index

(** Construct a constant pool index from an integer. Raises
    {!Constpool.BadIndex} if the value is out of range. *)
val index_of_int : int -> index

(** Constructs an optional constant pool index from an integer. If the
    argument is [0] then [None] is returned, otherwise [Some
    (index_of_int i)] is returned. *)
val index_option_of_int : int -> index option

(** Retrieves the integer value of a constant pool index. This will
    always be in the range [[1, 0xffff]]. *)
val index_to_int : index -> int

(**{2 Constant pools} *)

(** The type of constant pools. Note that a value of this type is not
    necessarily internally consistent: entries may point to other
    entries that do not exist or to entries of incorrect type. This
    due to the {!Constpool.append_entry} function. *)
type pool

(** The type of constant pool entries. [CPdouble] and [CPlong] entries
    occupy two spaces in the constant pool, so the index directly
    after one of these values will be inaccessible. *)
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

(** Returns the size of the constant pool, as required for the
    [.class] file format. Note that [CPdouble] and [CPlong] values
    take up two entries. *)
val size : pool -> int

(** Iterates over the elements of the pool, invoking the function on
    each element. Skips over unusable entries after long and double
    constants. *)
val iter : (entry -> unit) -> pool -> unit

(** Iterates over the elements of the pool, invoking the function on
    each element with its index. Skips over unusable entries after
    long and double constants. *)
val iteri : (index -> entry -> unit) -> pool -> unit

(** Exception thrown when entry lookup goes wrong. *)
exception BadLookup of string * int

(** Looks up an entry in the constant pool. Raises
    {!Constpool.BadLookup} if the index is out-of-range for this pool
    or points to an invalid entry. *)
val lookup : pool -> index -> entry

val lookup_utf8 : pool -> index -> string

val lookup_class : pool -> index -> Jvmtype.jref_type

val lookup_class_notarray : pool -> index -> Jvmtype.jclass

val lookup_methodsig : pool -> index -> Jvmtype.methodsig

val lookup_type : pool -> index -> Jvmtype.jtype

val lookup_methoddesc : pool -> index -> string * Jvmtype.methodsig

val lookup_fielddesc : pool -> index -> string * Jvmtype.jtype

val lookup_fieldref : pool -> index -> Jvmtype.jclass * string * Jvmtype.jtype

val lookup_methodref : pool -> index -> Jvmtype.jref_type * string * Jvmtype.methodsig

val lookup_imethodref : pool -> index -> Jvmtype.jclass * string * Jvmtype.methodsig

val lookup_int : pool -> index -> int32

val lookup_double : pool -> index -> float

val lookup_float : pool -> index -> JFloat.t

val lookup_long : pool -> index -> int64

(**{2 Building Constant Pools}

   The following types and functions provide for the construction of
   constant pools. An abstract [builder] is created by the
   {!Constpool.create_builder} function. Entries are then added to the
   constant pool by the [add_*] functions and the
   {!Constpool.append_entry} function. When construction is complete,
   a constant pool is obtained by using the
   {!Constpool.pool_of_builder} function. The [builder] may be queried
   during construction by using the [find_*] functions *)

(** Abstract type of constant pool builders *)
type builder

(** Create a new builder. The [initial_size] argument is optional. It
    is used to pre-allocate space for the constant pool to be
    constructed. It does not affect the constructed pool itself. *)
val create_builder : ?initial_size:int -> unit -> builder

(** Create a new pool from a builder with all the entries added so
    far. This creates a fresh pool each time, so adding things to the
    builder will not affect previously created pools. *)
val pool_of_builder : builder -> pool

(** Create a new builder from an existing pool with all the entries added so
    far. The index of each entry in the pool is preserved. *)
val builder_of_pool : pool -> builder

(** {3 Adding Entries}
    
    The following functions add items to a {!Constpool.builder}. The
    difference between the [append_entry] function and the [add_*]
    functions is that [append_entry] always appends an entry to the
    pool, but [add_*] checks to see if the entry already exists before
    adding it. *)

(** Thrown when the constant pool being constructed has too many
    entries. *)
exception PoolTooLarge

(** Append an entry to the [builder]. Always takes the next available
    index in the pool. Does not search to see if the entry already
    exists. Also does not check to see if the indexes within the entry
    are valid (because they may refer to entries to be added
    later). Returns the index of the newly added entry. *)
val append_entry : builder -> entry -> index

(** Adds a string constant to the [builder] and returns the new index,
    or returns the existing index if the string already exists. *)
val add_utf8 : builder -> string -> index

(** Adds an integer constant to the [builder] and returns the new
    index, or returns the existing index if the integer already
    exists.
*)
val add_int : builder -> int32 -> index

(** Adds a float constant to the [builder] and returns the new index,
    or returns the existing index if the float already exists.
*)
val add_float : builder -> JFloat.t -> index

(** Adds a long constant to the [builder] and returns the new index,
    or returns the existing index if the long already exists.
*)
val add_long : builder -> int64 -> index

(** Adds a double constant to the [builder] and returns the new index,
    or returns the existing index if the double already exists.
*)
val add_double : builder -> float -> index

(** Adds a string constant to the [builder] and returns the new index,
    or returns the existing index if the string already exists.
*)
val add_string : builder -> string -> index

(** Adds a class constant to the [builder] and returns the new index,
    or returns the existing index if the class already exists.
*)
val add_class : builder -> Jvmtype.jref_type -> index

(** Adds a method reference constant to the [builder] and returns the
    new index, or returns the existing index if the method reference
    already exists.
*)
val add_method_ref : builder -> Jvmtype.jref_type * string * Jvmtype.methodsig -> index

(** Adds an interface method reference constant to the [builder] and
    returns the new index, or returns the existing index if the entry
    already exists.
*)
val add_imethod_ref : builder -> Jvmtype.jclass * string * Jvmtype.methodsig -> index

(** Adds a field reference constant to the [builder] and returns the
    new index, or returns the existing index if the entry already
    exists.
*)
val add_field_ref : builder -> Jvmtype.jclass * string * Jvmtype.jtype -> index

(** Adds a method descriptor constant to the [builder] and returns the
    new index, or returns the existing index if the entry already
    exists.
*)
val add_methoddesc : builder -> string * Jvmtype.methodsig -> index


(** {3 Looking up entries in a builder}

    The following functions look up the index for a given value. The
    value must have already been added by one of
    {!Constpool.append_entry} or [add_*]. This is used by the
    instruction compilation process in {!CompileBytecode} to estimate
    the sizes of constant pool indexes for constants occuring in JVM
    code. Each of these functions returns [None] if the value is not
    already in the pool being built. *)

val find_utf8 : builder -> string -> index option
val find_int : builder -> int32 -> index option
val find_float : builder -> JFloat.t -> index option
val find_class : builder -> Jvmtype.jref_type -> index option
val find_string : builder -> string -> index option
