let (@+) (b,x) bits = if b then x lor bits else bits

let (@?) b mask = b land mask <> 0

type class_flags =
    { c_public     : bool
    ; c_private    : bool
    ; c_protected  : bool
    ; c_static     : bool
    ; c_final      : bool
    ; c_super      : bool
    ; c_interface  : bool
    ; c_abstract   : bool
    ; c_synthetic  : bool
    ; c_annotation : bool
    ; c_enum       : bool
    }

let empty_class_flags =
  { c_public     = false
  ; c_private    = false
  ; c_protected  = false
  ; c_static     = false
  ; c_final      = false
  ; c_super      = false
  ; c_interface  = false
  ; c_abstract   = false
  ; c_synthetic  = false
  ; c_annotation = false
  ; c_enum       = false
  }

let ui16_of_class_flags flags =
     (flags.c_public,     0x0001)
  @+ (flags.c_private,    0x0002)
  @+ (flags.c_protected,  0x0004)
  @+ (flags.c_static,     0x0008)
  @+ (flags.c_final,      0x0010)
  @+ (flags.c_super,      0x0020)
  @+ (flags.c_interface,  0x0200)
  @+ (flags.c_abstract,   0x0400)
  @+ (flags.c_synthetic,  0x1000)
  @+ (flags.c_annotation, 0x2000)
  @+ (flags.c_enum,       0x4000)
  @+ 0

let class_flags_of_ui16 bits =
  { c_public     = bits @? 0x0001
  ; c_private    = bits @? 0x0002
  ; c_protected  = bits @? 0x0004
  ; c_static     = bits @? 0x0008
  ; c_final      = bits @? 0x0010
  ; c_super      = bits @? 0x0020
  ; c_interface  = bits @? 0x0200
  ; c_abstract   = bits @? 0x0400
  ; c_synthetic  = bits @? 0x1000
  ; c_annotation = bits @? 0x2000
  ; c_enum       = bits @? 0x4000
  }

type field_flags =
    { f_public     : bool
    ; f_private    : bool
    ; f_protected  : bool
    ; f_static     : bool
    ; f_final      : bool
    ; f_volatile   : bool
    ; f_transient  : bool
    ; f_synthetic  : bool
    ; f_enum       : bool
    }

let empty_field_flags =
  { f_public     = false
  ; f_private    = false
  ; f_protected  = false
  ; f_static     = false
  ; f_final      = false
  ; f_volatile   = false
  ; f_transient  = false
  ; f_synthetic  = false
  ; f_enum       = false
  }


let ui16_of_field_flags flags =
     (flags.f_public,     0x0001)
  @+ (flags.f_private,    0x0002)
  @+ (flags.f_protected,  0x0004)
  @+ (flags.f_static,     0x0008)
  @+ (flags.f_final,      0x0010)
  @+ (flags.f_volatile,   0x0040)
  @+ (flags.f_transient,  0x0080)
  @+ (flags.f_synthetic,  0x1000)
  @+ (flags.f_enum,       0x4000)
  @+ 0

let field_flags_of_ui16 bits =
  { f_public     = bits @? 0x0001
  ; f_private    = bits @? 0x0002
  ; f_protected  = bits @? 0x0004
  ; f_static     = bits @? 0x0008
  ; f_final      = bits @? 0x0010
  ; f_volatile   = bits @? 0x0040
  ; f_transient  = bits @? 0x0080
  ; f_synthetic  = bits @? 0x1000
  ; f_enum       = bits @? 0x4000
  }

type method_flags =
    { m_public       : bool
    ; m_private      : bool
    ; m_protected    : bool
    ; m_static       : bool
    ; m_final        : bool
    ; m_synchronized : bool
    ; m_bridge       : bool
    ; m_varargs      : bool
    ; m_native       : bool
    ; m_abstract     : bool
    ; m_strictfp     : bool
    ; m_synthetic    : bool
    }

let empty_method_flags =
  { m_public       = false
  ; m_private      = false
  ; m_protected    = false
  ; m_static       = false
  ; m_final        = false
  ; m_synchronized = false
  ; m_bridge       = false
  ; m_varargs      = false
  ; m_native       = false
  ; m_abstract     = false
  ; m_strictfp     = false
  ; m_synthetic    = false
  }

let ui16_of_method_flags flags =
     (flags.m_public,       0x0001)
  @+ (flags.m_private,      0x0002)
  @+ (flags.m_protected,    0x0004)
  @+ (flags.m_static,       0x0008)
  @+ (flags.m_final,        0x0010)
  @+ (flags.m_synchronized, 0x0020)
  @+ (flags.m_bridge,       0x0040)
  @+ (flags.m_varargs,      0x0080)
  @+ (flags.m_native,       0x0100)
  @+ (flags.m_abstract,     0x0400)
  @+ (flags.m_strictfp,     0x0800)
  @+ (flags.m_synthetic,    0x1000)
  @+ 0

let method_flags_of_ui16 bits =
    { m_public       = bits @? 0x0001
    ; m_private      = bits @? 0x0002
    ; m_protected    = bits @? 0x0004
    ; m_static       = bits @? 0x0008
    ; m_final        = bits @? 0x0010
    ; m_synchronized = bits @? 0x0020
    ; m_bridge       = bits @? 0x0040
    ; m_varargs      = bits @? 0x0080
    ; m_native       = bits @? 0x0100
    ; m_abstract     = bits @? 0x0400
    ; m_strictfp     = bits @? 0x0800
    ; m_synthetic    = bits @? 0x1000
    }
