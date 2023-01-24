module Data.Bag

import Data.SortedMap

import Data.Nat
import Data.List
import Data.DPair

export
Bag : (a : Type) -> Ord a => Type
Bag a = SortedMap a (Subset Nat IsSucc)
parameters {0 a : Type} {auto ord : Ord a}
  export
  singleton : a -> Bag a
  singleton x = SortedMap.singleton x (Element 1 ItIsSucc)

  export
  empty : Bag a
  empty = SortedMap.empty

  export
  union : (xs,ys : Bag a) -> Bag a
  union = mergeWith $ \(x `Element` prf1), (y `Element` prf2) =>
    (x + y `Element` case prf1 of ItIsSucc => ItIsSucc)

  export
  Union : List (Bag a) -> Bag a
  Union = foldl union Bag.empty

  export
  fold : (b ->
     (i : Nat) -> (0 isSucc : IsSucc i) -> a -> b) -> b ->
     Bag a -> b
  fold f y0 = foldl (\y,(x, k `Element` prf) =>
    f y k prf x) y0 . SortedMap.toList

export
(Ord a, Show a) => Show (Bag a) where
  show xs = """
    ⟅\{fold (\y,k,_,x =>
       let xShow = case k of
             1 => show x
             _ => "\{show k} * \{show x}"
       in if y == ""
       then xShow
       else "\{y}, \{xShow}"
       ) "" xs
      }⟆
    """
