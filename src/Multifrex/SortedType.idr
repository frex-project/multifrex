module Multifrex.SortedType

import Multifrex.Signature

public export
SortedType : Type -> Type
SortedType sort = sort -> Type
