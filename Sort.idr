module Sort

import Decidable.Order

import Data.Vect

data IsSorted : (xs : Vect n e) -> Type where
  IsSortedZero : IsSorted Nil
  IsSortedOne : (x : e) -> IsSorted (x::Nil)
  IsSortedMany : (Ordered e to) => (x : e) -> { y : e } -> { ys : Vect n'' e } ->
                 { auto prf : to x y } -> IsSorted (y :: ys) -> IsSorted (x :: y :: ys)

tailSorted : Ordered e to => IsSorted (x :: (y :: xs)) -> IsSorted (y :: xs)
tailSorted (IsSortedMany x y) = y

equalityImpliesOrder : (Ordered e to) => x = y -> to x y
equalityImpliesOrder {x} Refl = reflexive x

abc : Ordered e to => to y x -> x = y -> IsSorted (y :: xs) -> IsSorted (x :: (y :: xs))
abc {to} {x} prf prf2 prf1 = IsSortedMany {to} {prf=equalityImpliesOrder prf2} x prf1

abc2 : Ordered e to => (prf : to y x) -> ((x = y) -> Void) -> (prf1 : IsSorted (y :: xs)) -> IsSorted (x :: (y :: xs)) -> Void
abc2 prf a prf1 = ?abc2_rhs

decideSorted : (Ordered e to, DecEq e) => (xs : Vect n e) -> Dec (IsSorted xs)
decideSorted [] = Yes IsSortedZero
decideSorted (x :: []) = Yes (IsSortedOne x)
decideSorted {to} (x :: (y :: xs)) = case (decideSorted {to} (y :: xs), order {to} x y, decEq x y) of
                                     (Yes prf1, Left prf, _) => Yes (IsSortedMany {prf} x prf1)
                                     (Yes prf1, Right prf, Yes a) => Yes (abc prf a prf1)
                                     (Yes prf1, Right prf, No a) => No (abc2 prf a prf1)
                                     (No prf1, _, a) => No (prf1 . tailSorted {to})

sorted : IsSorted [the Nat 1, 2, 3]
sorted = IsSortedMany {to=LTE} 1 (IsSortedMany {to=LTE} 2 (IsSortedOne 3))

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
