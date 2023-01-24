module MultiFrexlet.Semigroup.Commutative

import public MultiFrexlet.SingleSorted
import public Data.Vect
import public Data.Vect.Quantifiers
import Multifrex

import Data.Bag.NonEmpty
import Data.List1
import Data.DPair

namespace Signature
  public export
  data Ops = Plus

  public export
  CommutativeSemigroup : Signature
  CommutativeSemigroup = MkSignature SingleSorted
    { op = Ops
    , arity = \case
        Plus => MkArity [Carrier, Carrier] Carrier
    }

namespace Nat.Additive
  public export
  Nat : Algebra CommutativeSemigroup
  Nat = MkAlgebra
    { carrier = const Nat
    , semVect =
        \Plus, [x,y] => x + y
    }

namespace Nat.Multiplicative
  public export
  Nat : Algebra CommutativeSemigroup
  Nat = MkAlgebra
    { carrier = const Nat
    , semVect =
        \Plus, [x,y] => x * y
    }

namespace FreeChar
  public export
  FreeChar : Algebra CommutativeSemigroup
  FreeChar = MkAlgebra
    { carrier = const String
    , semVect =
        \Plus, [x,y] => x ++ y
    }

namespace Free
  public export
  FreeOver : (a : Type) -> Ord a => Algebra CommutativeSemigroup
  FreeOver a = MkAlgebra
    { carrier = const $ NonEmptyBag a
    , semVect =
        \Plus, [x,y] => x `NonEmpty.union` y
    }

public export
IMPLICIT : forall a.
  (b : a -> Type) ->
  ((x : a) -> b x) ->
  ({x : a} -> b x)
IMPLICIT _ f {x} = f x

data NotNeither a b = Left a | Right b | Both a b

public export
Frex : (a : Algebra CommutativeSemigroup) -> (x : Type) ->
    Ord x => Frex a (const x)
Frex a x = MkFrex
  { extension = MkExtension
      { algebra = MkAlgebra
          { carrier = const $ NotNeither
              (a.carrier Carrier)
              ((FreeOver x).carrier Carrier)
          , semVect = \Plus =>
              let (+) := \u,v => a.semVect Plus [u,v]
                  U   := NonEmpty.union
              in \case
              [Left  x  , Left  y  ] => Left (x + y)
              [Left  x  , Right   y] => Both x y
              [Left  x  , Both  y z] => Both (x + y) z
              [Right   x, Left  y  ] => Both y x
              [Right   x, Right   y] => Right  (x `U` y)
              [Right   x, Both  y z] => Both y (x `U` z)
              [Both  x z, Left  y  ] => Both (x + y) z
              [Both  x z, Right   y] => Both x (z `U` y)
              [Both  x z, Both  y w] => Both (x + y) (z `U` w)
          }
      , homo = IMPLICIT (\s =>
                 a.carrier s ->
                 NotNeither
                   (a .carrier Carrier)
                   ((FreeOver x).carrier Carrier))
             $ \Carrier,i => Commutative.Left i
      , vars = \x => Right (singleton x)
      }
  , universal = \ext' =>
    let (+) := \u,v => a.semVect Plus [u,v]
        (++) := \u,v => ext'.algebra.semVect Plus [u,v]
        B : Type
        B = ext'.algebra.carrier Carrier
        addMultiple : (i : Nat) -> (0 isSucc : IsSucc i) -> B -> B
        addMultiple (S 0) ItIsSucc y = y
        addMultiple (S (S k)) ItIsSucc y =
          y ++ (addMultiple (S k) ItIsSucc y)
        lft := \y => ext'.homo y
        rgt := \y => List1.foldl1 (++)
                $ map (\(x, n `Element` k) =>
                addMultiple n k (ext'.vars x)) $ toList1 y
    in IMPLICIT (\s =>
          NotNeither
             (a .carrier Carrier)
             (NonEmptyBag x) ->
             (ext' .algebra) .carrier s)
      $ \Carrier => \case
      Left  y   => lft y
      Right   y => rgt y
      Both  y z => lft y ++ rgt z
  }
