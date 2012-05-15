type nint = int32

let files = ref (Int32.one,[])

let open_file fno =
  let i, l = !files in
    files := (Int32.add i Int32.one,(i,open_in ("coqjvm-file-" ^ Int32.to_string fno))::l);
    i

let read_int i =
  try
    Int32.of_string (input_line (List.assoc i (snd !files)))
  with _ -> Int32.zero

let close_file i =
  try
    let j, l = !files in
      close_in (List.assoc i l);
      files := (j,List.remove_assoc i l);
      Int32.one
  with _ -> Int32.zero

type classnames = BasicsImpl.Classname.t
type methodnames = BasicsImpl.Methodname.t

let fileclass = ["io"], "File"
let openmeth  = "nativeopen"
let readmeth  = "nativeread"
let closemeth = "nativeclose"
