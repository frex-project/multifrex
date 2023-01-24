module Multifrex.SortedType

import Multifrex.Signature

public export
SortedType : Type -> Type
SortedType sort = sort -> Type

infix 2 ~>

public export
(~>) : {sort : Type} -> (src, tgt : SortedType sort) -> Type
src ~> tgt = {s : sort} -> src s -> tgt s
