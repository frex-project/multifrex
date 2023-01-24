module MultiFrexlet.Monoid

import public MultiFrexlet.SingleSorted
import public Data.Vect
import public Data.Vect.Quantifiers
import Multifrex

namespace Signature
  public export
  data Ops = Prod | Unit

  public export
  Monoid : Signature
  Monoid = MkSignature SingleSorted
    { op = Ops
    , arity = \case
        Prod => MkArity [Carrier, Carrier] Carrier
        Unit => MkArity []                 Carrier
    }

namespace Nat.Additive
  public export
  Nat : Algebra Monoid
  Nat = MkAlgebra
    { carrier = const Nat
    , semVect = \case
        Prod => \[x,y] => x + y
        Unit => \[]    => the Nat 0
    }

namespace Nat.Multiplicative
  public export
  Nat : Algebra Monoid
  Nat = MkAlgebra
    { carrier = const Nat
    , semVect = \case
        Prod => \[x,y] => x * y
        Unit => \[]    => the Nat 1
    }

namespace FreeChar
  public export
  FreeChar : Algebra Monoid
  FreeChar = MkAlgebra
    { carrier = const String
    , semVect = \case
        Prod => \[x,y] => x ++ y
        Unit => \[]    => ""
    }

namespace Free
  public export
  FreeOver : Type -> Algebra Monoid
  FreeOver a = MkAlgebra
    { carrier = const $ List a
    , semVect = \case
        Prod => \[x,y] => x ++ y
        Unit => \[]    => []
    }
