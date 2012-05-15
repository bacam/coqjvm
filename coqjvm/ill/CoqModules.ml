module Filter = struct
  let f _ = true
end

module ResILLBase = Coqextract.ResILLBase.ResBaseSemantics (BasicsImpl) (Filter)
module ILL = Coqextract.ILLImplementation.MkILLSyntax (BasicsImpl) (ResILLBase.SYN)
