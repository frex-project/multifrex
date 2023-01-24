module Data.List.Separated

public export
data Sep : List a -> (a -> a -> Type) -> Type where
  Nil : Sep [x] p
  (::) : forall p . p x y ->
    Sep (y :: xs) p -> Sep (x :: y :: xs) p

public export
data SnocSep : SnocList a -> (a -> a -> Type) -> Type where
  Lin : SnocSep [< x] p
  (:<) : forall p .
    SnocSep (xs :< y) p ->
    p y x ->
    SnocSep (xs :< y :< x) p

public export
(<>>) : SnocSep (sx :< x) p -> Sep (y :: ys) p ->
  p x y -> Sep (sx <>> x :: y :: ys) p
([<] <>> seps) prf = prf :: seps
((ssep :< sep) <>> seps) prf = (ssep <>> prf :: seps) sep

public export
(<><) : SnocSep (sx :< x) p -> Sep (y :: ys) p ->
  p x y -> SnocSep (sx :< x :< y <>< ys) p
(ssep <>< []) prf = ssep :< prf
(ssep <>< (sep :: seps)) prf = (ssep :< prf <>< seps) sep
