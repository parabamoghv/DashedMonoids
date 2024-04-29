import Mathlib
--import DashedMonoids.Interval
--open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

--Properties of Lists that are not in MathLib


universe u v w


variable {S: Type _}

variable {i n m: Nat}

namespace List




def up_List {X:Set S}(L:List X):List S:=by
  induction' L with head _ tail_h
  case nil=> exact []
  case cons=> exact (head.1)::tail_h

theorem ListOne_neq_ListNil (a:S):[a]≠ []:=by
  simp only [ne_eq, not_false_eq_true]

theorem ListOneOrMore_neq_ListNil (a:S)(L:List S):a::L≠ []:= by
  simp only [ne_eq, not_false_eq_true]

theorem ListTwoOrMore_neq_ListNil (a b:S)(L:List S):a::b::L≠ []:=by
  simp only [ne_eq, not_false_eq_true]

theorem ListTwoOrMore_neq_ListOne (a b:S)(L:List S):∀ x:S, a::b::L≠ [x]:=by
  simp only [ne_eq, cons.injEq, and_false, not_false_eq_true, implies_true]
