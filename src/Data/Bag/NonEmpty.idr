module Data.Bag.NonEmpty

import Data.SortedMap

import Data.Nat
import Data.List

import Data.Nat
import Data.List
import Data.DPair

import Data.Bag
import Data.List1

-- UNSAFE implementation, data abstraction ought to help

export
NonEmptyBag : (a : Type) -> Ord a => Type
NonEmptyBag a = SortedMap a (Subset Nat IsSucc)
parameters {0 a : Type} {auto ord : Ord a}
  export
  singleton : a -> NonEmptyBag a
  singleton x = SortedMap.singleton x (Element 1 ItIsSucc)

  export
  union : (xs,ys : NonEmptyBag a) -> NonEmptyBag a
  union = mergeWith $ \(x `Element` prf1), (y `Element` prf2) =>
    (x + y `Element` case prf1 of ItIsSucc => ItIsSucc)

  export
  union' : (xs : NonEmptyBag a) ->
           (ys : Bag         a) -> NonEmptyBag a
  union' xs ys = xs `Bag.union` ys


  export
  Union : List (NonEmptyBag a) -> NonEmptyBag a
  Union = foldl NonEmpty.union SortedMap.empty

  export
  toList1 : NonEmptyBag a -> List1 (a, Nat `Subset` IsSucc)
  toList1 xs = case SortedMap.toList xs of
    [] => believe_me ()
    (y :: ys) => y ::: ys

export
(Ord a, Show a) => Show (NonEmptyBag a) where
  show xs = """
    ⟅\{Bag.fold (\y,k,_,x =>
       let xShow = case k of
             1 => show x
             _ => "\{show k} * \{show x}"
       in if y == ""
       then xShow
       else "\{y}, \{xShow}"
       ) "" xs
      }⟆
    """
