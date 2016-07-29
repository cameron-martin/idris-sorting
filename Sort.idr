module Sort

import Decidable.Order

import Data.Vect

%default total

data IsSorted : (to : e -> e -> Type) -> (xs : Vect n e) -> Type where
  IsSortedZero : IsSorted to Nil
  IsSortedOne : (x : e) -> IsSorted to (x::Nil)
  IsSortedMany : (Ordered e to) => (x : e) -> {y : e} -> {ys : Vect n'' e} ->
                 {auto prf : to x y} -> IsSorted to (y :: ys) -> IsSorted to (x :: y :: ys)

tailSorted : Ordered e to => IsSorted to (x :: y :: xs) -> IsSorted to (y :: xs)
tailSorted (IsSortedMany _ x) = x

equalityImpliesOrder : (Ordered e to) => x = y -> to x y
equalityImpliesOrder {x} Refl = reflexive x

abc : Ordered e to => x = y -> IsSorted to (y :: xs) -> IsSorted to (x :: y :: xs)
abc {to} {x} equal tailSorted = IsSortedMany {to} {prf=equalityImpliesOrder equal} x tailSorted

abc2 : Ordered e to => to y x -> (x = y -> Void) -> IsSorted to (x :: y :: xs) -> Void
abc2 {to} {x} {y} prf' xNeqY (IsSortedMany {prf} _ _) = xNeqY (antisymmetric {po=to} x y prf prf')

decideSorted : (Ordered e to, DecEq e) => (xs : Vect n e) -> Dec (IsSorted to xs)
decideSorted [] = Yes IsSortedZero
decideSorted (x :: []) = Yes (IsSortedOne x)
decideSorted {to} (x :: y :: xs) = case (decideSorted {to} (y :: xs), order {to} x y, decEq x y) of
                                     (Yes sorted, Left  order, _           ) => Yes (IsSortedMany {prf=order} x sorted)
                                     (Yes sorted, Right order, Yes equal   ) => Yes (abc equal sorted)
                                     (Yes _,      Right order, No notEqual ) => No  (abc2 order notEqual)
                                     (No prf1,    _,           _           ) => No  (prf1 . tailSorted)



sorted : IsSorted LTE [the Nat 1, 2, 3]
sorted = IsSortedMany 1 (IsSortedMany 2 (IsSortedOne 3))

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
