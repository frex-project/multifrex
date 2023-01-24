module Multifrex

import public Multifrex.Signature
import public Multifrex.SortedType
import public Multifrex.Algebra

public export
record Extension
  (a : Algebra signa)
  (x : SortedType signa.sort) where
  constructor MkExtension
  algebra : Algebra signa
  -- Assumes homo is a homomorphism
  homo : a ~> algebra
  vars : x ~> algebra.carrier

-- Output ought to be a homomorphism, and preserve
-- homo and vars.
public export
(.IsFree) :
  {signa : Signature} ->
  {a : Algebra signa} ->
  {x : SortedType signa.sort} ->
  Extension {signa} a x -> Type
ext.IsFree = (ext' : Extension a x) ->
  ext.algebra ~> ext'.algebra

public export
record Frex
  (a : Algebra signa)
  (x : SortedType signa.sort) where
  constructor MkFrex
  extension : Extension a x
  universal : extension.IsFree
