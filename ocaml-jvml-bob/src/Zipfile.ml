(* This is heavily based on (practically copied) from Xavier Leroy's
   zip.ml, part of camlzip.
*)

exception Error of string * string

let read_32 channel =
  let b1 = input_byte channel in
  let b2 = input_byte channel in
  let b3 = input_byte channel in
  let b4 = input_byte channel in
    Int32.add
      (Int32.of_int (b1 + (b2 lsl 8) + (b3 lsl 16))) 
      (Int32.shift_left (Int32.of_int b4) 24)

(* FIXME: should we use int64 to deal with really big files? *)
let read_int filename channel =
  let i = read_32 channel in
    if i < 0l || i > 0x3ffffffl then
      raise (Error (filename, "size too long"));
  Int32.to_int i

let read_16 channel =
  let b1 = input_byte channel in
  let b2 = input_byte channel in
    b1 + (b2 lsl 8)

let read_string channel len =
  let buffer = String.create len in
  let ()     = really_input channel buffer 0 len in
    buffer

type compression_method = Stored | Deflated

type entry =
    { e_filename          : string
    ; e_extra             : string
    ; e_comment           : string
    ; e_method            : compression_method
(*    ; e_mtime             : float*)
    ; e_crc               : int32
    ; e_uncompressed_size : int
    ; e_compressed_size   : int
    ; e_is_directory      : bool
    ; e_file_offset       : int64
    }

type zipfile =
    {         zf_filename   : string
    ;         zf_channel    : in_channel
    ;         zf_directory  : (string,entry) Hashtbl.t
    ;         zf_comment    : string
    ; mutable zf_open_entry : bool
    }

let find_ecd_signature buffer len =
  let rec loop state pos = match state with
    | _       when pos < 0               -> None
    | `STATE1 when buffer.[pos] = '\x06' -> loop `STATE2 (pos-1)
    | `STATE2 when buffer.[pos] = '\x05' -> loop `STATE3 (pos-1)
    | `STATE3 when buffer.[pos] = 'K'    -> loop `STATE4 (pos-1)
    | `STATE4 when buffer.[pos] = 'P'    -> Some pos
    | _       when buffer.[pos] = '\x06' -> loop `STATE2 (pos-1)
    | _                                  -> loop `STATE1 (pos-1)
  in
    loop `STATE1 (len - 1)

let filename_is_directory name =
  String.length name > 0 && name.[String.length name - 1] = '/'

let read_end_of_central_directory filename channel =
  let buffer = String.create 256 in
  let file_length = in_channel_length channel in
  let rec find_ecd_record pos length =
    if pos <= 0 || file_length - pos >= 0x10000 then
      raise (Error (filename, "End of central directory not found, not a ZIP file"));
    let toread  = min pos 128 in
    let ()      = String.blit buffer 0 buffer toread (256 - toread) in
    let newpos  = pos - toread in
    let ()      = seek_in channel newpos in
    let ()      = really_input channel buffer 0 toread in
    let newlen  = min (toread + length) 256 in
      match find_ecd_signature buffer newlen with
	| None                    -> find_ecd_record newpos newlen
	| Some _ when newlen < 22 -> find_ecd_record newpos newlen
	| Some offset ->
	    let comment_len =  Char.code buffer.[offset + 20] lor (Char.code buffer.[offset + 21] lsl 8) in
	      if newpos + offset + 22 + comment_len <> file_length then
		find_ecd_record newpos newlen
	      else
		newpos + offset
  in
  let ()          = seek_in channel (find_ecd_record file_length 0) in
  let magic       = read_32 channel in
  let disk_num    = read_16 channel in
  let cd_disk_num = read_16 channel in
  let _           = read_16 channel in (* number of entries on this disk *)
  let cd_entries  = read_16 channel in
  let cd_size     = read_32 channel in
  let cd_offset   = read_32 channel in
  let comment_len = read_16 channel in
  let comment     = read_string channel comment_len in
    assert (magic = 0x06054b50l); (* this should hold by the search algorithm above *)
    if disk_num <> 0 || cd_disk_num <> 0 then
      raise (Error (filename, "multi-disk ZIP files not supported"));
    (cd_entries, cd_size, cd_offset, comment)

let compression_method_of_int filename i = match i with
  | 0 -> Stored
  | 8 -> Deflated
  | _ -> raise (Error (filename, Printf.sprintf "unknown compression method: %d" i))

(*let unixtime_of_dostime time date =
  fst(Unix.mktime
        { Unix.tm_sec = (time lsl 1) land 0x3e;
          Unix.tm_min = (time lsr 5) land 0x3f;
          Unix.tm_hour = (time lsr 11) land 0x1f;
          Unix.tm_mday = date land 0x1f;
          Unix.tm_mon = ((date lsr 5) land 0xf) - 1;
          Unix.tm_year = ((date lsr 9) land 0x7f) + 80;
          Unix.tm_wday = 0;
          Unix.tm_yday = 0;
          Unix.tm_isdst = false })*)

let read_central_directory filename channel num_entries cd_start cd_end =
  let cd_end = Int64.of_int32 cd_end in
    try
      let () = LargeFile.seek_in channel (Int64.of_int32 cd_start) in
      let rec read_loop entries entry_count =
	if LargeFile.pos_in channel >= cd_end then
	  entries, entry_count
	else
	  let magic              = read_32 channel in
	  let _version_made_by   = read_16 channel in
	  let _version_needed    = read_16 channel in
	  let flags              = read_16 channel in
	  let compression_method = compression_method_of_int filename (read_16 channel) in
	  let _lastmod_time      = read_16 channel in
	  let _lastmod_date      = read_16 channel in
	  let crc                = read_32 channel in
	  let compressed_size    = read_int filename channel in
	  let uncompressed_size  = read_int filename channel in
	  let name_length        = read_16 channel in
	  let extra_length       = read_16 channel in
	  let comment_length     = read_16 channel in
	  let _disk_number       = read_16 channel in
	  let _internal_attr     = read_16 channel in
	  let _external_attr     = read_32 channel in
	  let header_offset      = Int64.of_int32 (read_32 channel) in
	  let name               = read_string channel name_length in
	  let extra              = read_string channel extra_length in
	  let comment            = read_string channel comment_length in
	  let ()                 = if magic <> 0x02014b50l then raise (Error (filename, "incorrect magic number in central directory")) in
	  let ()                 = if flags land 1 <> 0 then raise (Error (filename, "encrypted entries not supported")) in
	  let entry              = { e_filename          = name
				   ; e_extra             = extra
				   ; e_comment           = comment
				   ; e_method            = compression_method
				  (* ; e_mtime             = unixtime_of_dostime lastmod_time lastmod_date*)
				   ; e_crc               = crc
				   ; e_compressed_size   = compressed_size
				   ; e_uncompressed_size = uncompressed_size
				   ; e_is_directory      = filename_is_directory name
				   ; e_file_offset       = header_offset
				   } in
	    read_loop (entry::entries) (entry_count + 1)
      in
      let entries, count = read_loop [] 0 in
      let ()             = assert (cd_end = LargeFile.pos_in channel) in
      let ()             = assert (num_entries = 65535 || count = num_entries) in
	List.rev entries
    with End_of_file ->
      raise (Error (filename, "EOF while reading central directory"))

let open_in filename =
  let channel   = open_in_bin filename in
  let cd_entries, cd_size, cd_offset, cd_comment = read_end_of_central_directory filename channel in
  let entries   = read_central_directory filename channel cd_entries cd_offset (Int32.add cd_offset cd_size) in
  let directory = Hashtbl.create (cd_entries / 3) in
  let _         = List.iter (fun e -> Hashtbl.add directory e.e_filename e) entries in
    { zf_filename   = filename
    ; zf_channel    = channel
    (*; zf_entries   = entries*)
    ; zf_directory  = directory
    ; zf_comment    = cd_comment
    ; zf_open_entry = false
    }

let close_in zf = (* FIXME: issue a warning if we have an open entry? *)
  Pervasives.close_in zf.zf_channel

let find zf filename =
  try Some (Hashtbl.find zf.zf_directory filename) with Not_found -> None

let seek_entry zf entry =
  try
    let channel            = zf.zf_channel in
    let ()                 = LargeFile.seek_in channel entry.e_file_offset in
    let magic              = read_32 channel in
    let _version_needed    = read_16 channel in
    let _flags             = read_16 channel in
    let _method            = read_16 channel in
    let _lastmod_time      = read_16 channel in
    let _lastmod_date      = read_16 channel in
    let _crc               = read_32 channel in
    let _compressed_size   = read_32 channel in
    let _uncompressed_size = read_32 channel in
    let filename_length    = read_16 channel in
    let extra_length       = read_16 channel in
    let ()                 = if magic <> 0x04034b50l then raise (Error (zf.zf_filename, "wrong local file header")) in
      LargeFile.seek_in channel (Int64.add entry.e_file_offset (Int64.of_int (30 + filename_length + extra_length)))
  with End_of_file ->
    raise (Error (zf.zf_filename, "truncated local file header"))

let input_channel_no_close zf =
  IO.create_in
    ~read: (fun () -> try input_char zf.zf_channel with End_of_file -> raise IO.No_more_input)
    ~input:(fun s p l -> let n = Pervasives.input zf.zf_channel s p l in if n = 0 then raise IO.No_more_input else n)
    ~close:(fun () -> zf.zf_open_entry <- false)

let open_entry zf entry =
  let ()        = seek_entry zf entry in
  let raw_input = input_channel_no_close zf in
  let ()        = zf.zf_open_entry <- true in
    match entry.e_method with
      | Stored ->
	  Util.IO.limited_input entry.e_compressed_size raw_input
      | Deflated ->
	  (*Util.IO.limited_input entry.e_uncompressed_size*) (Unzip.inflate ~header:false raw_input)

let read_entry zf entry =
  let input = open_entry zf entry in
  let str   = IO.nread input entry.e_uncompressed_size in
  let ()    = IO.close_in input in
    str

let iter zf f =
  Hashtbl.iter (fun _ e -> f e) zf.zf_directory

let fold zf f a =
  Hashtbl.fold (fun _ e c -> f e c) zf.zf_directory a

let num_entries zf =
  Hashtbl.length zf.zf_directory
