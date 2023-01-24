module MultiFrexlet.Semigroup

import public MultiFrexlet.SingleSorted
import public Data.Vect
import public Data.Vect.Quantifiers
import Multifrex

namespace Signature
  public export
  data Ops = Prod

  public export
  Monoid : Signature
  Monoid = MkSignature SingleSorted
    { op = Ops
    , arity = \case
        Prod => MkArity [Carrier, Carrier] Carrier
    }

namespace Nat.Additive
  public export
  Nat : Algebra Monoid
  Nat = MkAlgebra
    { carrier = const Nat
    , semVect = \case
        Prod => \[x,y] => x + y
    }

namespace Nat.Multiplicative
  public export
  Nat : Algebra Monoid
  Nat = MkAlgebra
    { carrier = const Nat
    , semVect = \case
        Prod => \[x,y] => x * y
    }

namespace FreeChar
  public export
  FreeChar : Algebra Monoid
  FreeChar = MkAlgebra
    { carrier = const String
    , semVect = \case
        Prod => \[x,y] => x ++ y
    }

namespace Free
  public export
  FreeOver : Type -> Algebra Monoid
  FreeOver a = MkAlgebra
    { carrier = const $ List a
    , semVect = \case
        Prod => \[x,y] => x ++ y
    }
