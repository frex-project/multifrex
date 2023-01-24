module Multifrex.Algebra

import Multifrex.Signature
import Multifrex.SortedType

import public Data.Fun

import Data.Vect.Quantifiers

infix 8 ^

public export
(^) : Type -> Vect n Type -> Type
a ^ xs = Fun xs a

public export
record Algebra (signa : Signature) where
  constructor MkAlgebra
  carrier : SortedType signa.sort
  semVect : (f : signa.op) ->
    All carrier (signa.arity f).dom ->
    carrier (signa.arity f).cod
