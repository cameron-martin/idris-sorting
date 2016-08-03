module Sort

import Decidable.Order

import Data.Vect

%default total

data IsSorted : (to : e -> e -> Type) -> (xs : Vect n e) -> Type where
  IsSortedZero : IsSorted to Nil
  IsSortedOne : {x : e} -> IsSorted to (x::Nil)
  IsSortedMany : (Ordered e to) => {x : e} -> {y : e} -> {ys : Vect n'' e} ->
                 {auto prf : to x y} -> IsSorted to (y :: ys) -> IsSorted to (x :: y :: ys)

data Forall : (e -> Type) -> (xs : Vect n e) -> Type where
  ForallNone : Forall p []
  ForallAnd : p x -> Forall p xs -> Forall p (x :: xs)

data Contains : Vect n e -> e -> Type where
  Here : Contains (x :: _) x
  There : Contains xs y -> Contains (x :: xs) y


Subset : Vect n e -> Vect m e -> Type
Subset xs ys = Forall (Contains ys) xs

Permutation : Vect n e -> Vect m e -> Type
Permutation xs ys = (Subset xs ys, Subset ys xs)

tailSorted : Ordered e to => IsSorted to (x :: y :: xs) -> IsSorted to (y :: xs)
tailSorted (IsSortedMany x) = x

equalityImpliesOrder : (Ordered e to) => x = y -> to x y
equalityImpliesOrder {y} xEqY = rewrite xEqY in (reflexive y)

abc : Ordered e to => x = y -> IsSorted to (y :: xs) -> IsSorted to (x :: y :: xs)
abc {to} equal tailSorted = IsSortedMany {to} {prf=equalityImpliesOrder equal} tailSorted

abc2 : Ordered e to => to y x -> (x = y -> Void) -> IsSorted to (x :: y :: xs) -> Void
abc2 {to} {x} {y} prf' xNeqY (IsSortedMany {prf} _) = xNeqY (antisymmetric {po=to} x y prf prf')

decideSorted : (Ordered e to, DecEq e) => (xs : Vect n e) -> Dec (IsSorted to xs)
decideSorted [] = Yes IsSortedZero
decideSorted (x :: []) = Yes (IsSortedOne)
decideSorted {to} (x :: y :: xs) = case (decideSorted {to} (y :: xs), order {to} x y, decEq x y) of
                                     (Yes sorted, Left  order, _           ) => Yes (IsSortedMany {prf=order} sorted)
                                     (Yes sorted, Right order, Yes equal   ) => Yes (abc equal sorted)
                                     (Yes _,      Right order, No notEqual ) => No  (abc2 order notEqual)
                                     (No prf1,    _,           _           ) => No  (prf1 . tailSorted)


insert : (Ordered e to) => (a : e) -> (xs : Vect n e) -> (sorted : IsSorted to xs) -> (ys : Vect (S n) e ** (IsSorted to ys, Permutation (a :: xs) ys))
insert a [] IsSortedZero = ([a] ** (IsSortedOne, ForallAnd Here ForallNone, ForallAnd Here ForallNone))
insert {to} a (x :: []) IsSortedOne = case order {to} a x of
                                      (Left prf) => ([a, x] ** (IsSortedMany IsSortedOne,
                                                    ForallAnd Here (ForallAnd (There Here) ForallNone),
                                                    ForallAnd Here (ForallAnd (There Here) ForallNone)))
                                      (Right prf) => ([x, a] ** (IsSortedMany IsSortedOne,
                                                     ForallAnd (There Here) (ForallAnd Here ForallNone),
                                                     ForallAnd (There Here) (ForallAnd Here ForallNone)))
insert a (x :: (y :: ys)) (IsSortedMany z) = ?insert_rhs_3
-- insert a [] IsSortedZero = ([a] ** IsSortedOne)
-- insert a (x :: []) IsSortedOne = ([x, x] ** IsSortedMany IsSortedOne)
-- insert a (x :: (x' :: xs)) prf = ?insert_rhs_3


insertionSort : (Ordered e to) => (xs : Vect n e) -> (ys : Vect n e ** IsSorted to ys)
insertionSort [] = ([] ** IsSortedZero)
insertionSort (x :: []) = ([x] ** IsSortedOne)
insertionSort (x :: (y :: xs)) = ?insertionSort_rhs_3

sorted : IsSorted LTE [the Nat 1, 2, 3]
sorted = IsSortedMany (IsSortedMany (IsSortedOne))

sort : Ordered e to => Vect n e -> (xs : Vect n e ** IsSorted to xs)
sort [] = ([] ** IsSortedZero)
sort (x :: []) = ([x] ** IsSortedOne)
sort {to} (x :: y :: xs) with (sort {to} xs)
  sort (x :: y :: xs) | (a ** pf) = ?sort_rhs_3_rhs_1


-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
