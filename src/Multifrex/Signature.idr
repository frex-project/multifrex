module Multifrex.Signature

import public Data.Vect

public export
record Arity sort where
  constructor MkArity
  {length : Nat}
  dom    : Vect length sort
  cod    : sort

public export
record Signature where
  constructor MkSignature
  sort : Type
  op   : Type
  arity : (f : op) -> Arity sort
