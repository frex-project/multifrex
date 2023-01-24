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

-- Terms --
public export
data Term : (signa : Signature) -> SortedType signa.sort ->
    signa.sort -> Type where
  Var : forall sort . a sort -> Term signa a sort
  App : (f : signa.op) ->
    All (Term signa a) (signa.arity f).dom ->
      Term signa a (signa.arity f).cod

mapAll : All {n} (p . f) xs ->
  All {n} p (map @{%search} f xs)
mapAll [] = []
mapAll (x :: y) = x :: mapAll y

public export total
bindAll : All (Term signa a) xs ->
  (forall sort. a sort -> Term signa b sort) ->
  All (Term signa b) xs
public export total
(>>=) : Term signa a sort0 ->
  (forall sort. a sort -> Term signa b sort) ->
  Term signa b sort0

bindAll [] f = []
bindAll (t :: ts) f = (t >>= f) :: bindAll ts f

(Var x   ) >>= f = f x
(App g ts) >>= f = App g $ bindAll ts f

public export
(~>) : {signa : Signature} -> (a,b : Algebra signa) -> Type
a ~> b = a.carrier ~> b.carrier
