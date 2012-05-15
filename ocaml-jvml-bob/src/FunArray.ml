module IntOrd = struct type t = int let compare = Pervasives.compare end

module IntMap = Map.Make (IntOrd)

exception Out_of_bounds of int * int

type 'a t = 
    { mapping: 'a IntMap.t
    ; length:  int
    ; default: 'a
    }

let create len default =
  { mapping = IntMap.empty
  ; length  = len
  ; default = default
  }

let length array = array.length

let get array i = 
  if i < 0 || i >= array.length then
    raise (Out_of_bounds (i, array.length))
  else
    try IntMap.find i array.mapping
    with Not_found -> array.default

let set array i v =
  if i < 0 || i >= array.length then
    raise (Out_of_bounds (i, array.length))
  else
    {array with mapping = IntMap.add i v array.mapping}
