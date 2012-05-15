(** Reading the contents of [.zip] and [.jar] files. *)

(**{1 Reading the contents of [.zip] and [.jar] files}

   This module contains functions for reading the contents of [.zip]
   format files. This includes the [.jar] files that the JVM uses. It
   relies on the [Unzip] module from [extlib] to do the actual
   decompression. *)

(** Exception thrown when there is an error during reading. First
    argument is the filename, second is the error message. *)
exception Error of string * string

(** Compression methods that we understand. *)
type compression_method = Stored | Deflated

(** Information about an entry in a [.zip] file. *)
type entry = private
    { e_filename          : string
    ; e_extra             : string
    ; e_comment           : string
    ; e_method            : compression_method
    ; e_crc               : int32
    ; e_uncompressed_size : int
    ; e_compressed_size   : int
    ; e_is_directory      : bool
    ; e_file_offset       : int64
    }

(** Abstract type of [.zip] file handles for reading. *)
type zipfile

(** Open a [.zip] file given a filename. *)
val open_in : string -> zipfile

(** Close a [.zip] file. You must close any open entry on this handle
    before calling this function. *)
val close_in : zipfile -> unit

(** Search for an entry in an open [.zip] file. Returns [Some entry]
    if it exists, [None] otherwise. *)
val find : zipfile -> string -> entry option

(** Opens an entry in the [.zip] file for reading. Decompression is
    done on the fly. Only one entry may be open at a time. *)
val open_entry : zipfile -> entry -> IO.input

(** Read an entire entry into a string in one go. There cannot be any
    open entries when this function is called. *)
val read_entry : zipfile -> entry -> string

(** Iterate over all the entries in a [.zip] file. *)
val iter : zipfile -> (entry -> unit) -> unit

(** Fold over all the entries in a [.zip] files. *)
val fold : zipfile -> (entry -> 'a -> 'a) -> 'a -> 'a

(** Return the number of entries in a [.zip] file. *)
val num_entries : zipfile -> int
