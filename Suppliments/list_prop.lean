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


section ListUp

def up_List {X:Set S}(L:List X):List S:=by
  induction' L with head _ tail_h
  case nil=> exact []
  case cons=> exact (head.1)::tail_h

lemma up_List_cons {X:Set S}(head:X)(L:List X):up_List (head::L) = head.1::up_List L:= by
  rw[up_List]
  --simp
  rw[up_List]

lemma up_List_ne0 {X :Set S}(L:List X):L≠ []→ up_List L ≠ []:=by
  intro Lne
  induction' L with head tail _
  case nil=>
    contradiction
  case cons=>
    rw[up_List_cons]
    simp only [ne_eq, not_false_eq_true]


def up_Set {X Y:Set S}(XsubY:X⊆ Y)(x:X):Y:=by
  use x.1
  exact XsubY x.2

lemma up_Set_inj {X Y:Set S}(XsubY:X⊆ Y)(x y:X):up_Set XsubY x = up_Set XsubY y → x=y:=by
  intro hxy
  rw[up_Set] at hxy
  rw[up_Set] at hxy
  simp only [Subtype.mk.injEq] at hxy
  ext
  exact hxy

def up_List_Set {X Y:Set S}(XsubY: X⊆ Y)(L:List X):List Y:= by
  induction' L with head _ tail_h
  case nil=> exact []
  case cons=>
    exact (up_Set XsubY head)::tail_h


lemma up_List_Set_cons{X Y: Set S}(XsubY:X ⊆ Y )(head:X)(L:List X):up_List_Set XsubY (head::L)=(up_Set XsubY head)::(up_List_Set XsubY L):= by
  rw[up_List_Set]
  simp
  rw[up_List_Set]


lemma up_List_Set_ne0 {X Y:Set S}(XsubY:X⊆ Y)(L:List X):L≠ []→ up_List_Set XsubY L ≠ []:=by
  intro Lne
  induction' L with head tail _
  case nil=>
    contradiction
  case cons=>
    rw[up_List_Set_cons]
    simp only [ne_eq, not_false_eq_true]

lemma up_List_Set_inj {X Y:Set S}(XsubY:X⊆ Y):∀ (L P:List X),up_List_Set XsubY L = up_List_Set XsubY P → L=P:=by
  intro L
  induction' L with head tail tail_h

  case nil=>
    intro P
    intro hLP

    rw[up_List_Set] at hLP
    simp at hLP
    by_contra Pne
    have PneSymm:P≠ []:=by
      intro h
      exact Pne h.symm
    have h:= up_List_Set_ne0 XsubY P PneSymm
    exact h hLP.symm
  case cons=>
    intro P hLP

    induction' P with headP tailP _
    case nil=>
      rw[up_List_Set_cons XsubY head tail] at hLP
      nth_rewrite 2 [up_List_Set] at hLP
      simp at hLP
    case cons=>
      rw[up_List_Set_cons XsubY head tail] at hLP
      rw[up_List_Set_cons XsubY headP tailP] at hLP
      simp only [cons.injEq] at hLP
      --have hLP1:=up_Set_inj XsubY head headP hLP.1
      rw[up_Set_inj XsubY head headP hLP.1]
      simp only [cons.injEq, true_and]
      exact tail_h tailP hLP.2



theorem up_List_eq_up_List_Set {X Y:Set S}(XsubY:X⊆ Y)(L:List X):up_List L = up_List (up_List_Set XsubY L):= by
  induction' L with head tail tail_h
  case nil=>
    rw[up_List]
    simp
    rw[up_List_Set]
    simp
    rw[up_List]
  case cons=>
    rw[up_List_cons]
    rw[up_List_Set_cons]
    rw[up_List_cons]
    rw[tail_h]
    simp only [cons.injEq, and_true]
    rw[up_Set]

end ListUp

theorem ListOne_neq_ListNil (a:S):[a]≠ []:=by
  simp only [ne_eq, not_false_eq_true]

theorem ListOneOrMore_neq_ListNil (a:S)(L:List S):a::L≠ []:= by
  simp only [ne_eq, not_false_eq_true]

theorem ListTwoOrMore_neq_ListNil (a b:S)(L:List S):a::b::L≠ []:=by
  simp only [ne_eq, not_false_eq_true]

theorem ListTwoOrMore_neq_ListOne (a b:S)(L:List S):∀ x:S, a::b::L≠ [x]:=by
  simp only [ne_eq, cons.injEq, and_false, not_false_eq_true, implies_true]


end List

namespace Set

variable {S:Type _}

theorem Union_assoc {X Y Z:Set S}:X∪ (Y∪ Z)=(X∪ Y)∪ Z:=by
  ext x
  constructor
  case mp=>
    rintro (hX|(hY|hZ))
    case inl=>
      left
      left
      exact hX
    case inr.inl=>
      left
      right
      exact hY
    case inr.inr=>
      right
      exact hZ
  case mpr=>
    rintro ((hX|hY)|hZ)
    case inl.inl=>
      left
      exact hX
    case inl.inr=>
      right
      left
      exact hY
    case inr=>
      right
      right
      exact hZ

end Set

namespace Nat

variable {M P:Type _}
variable {X:Set M}

theorem strong_induction {P : Nat → Prop} (n:Nat) (h : ∀ (m:Nat), (∀ k < m, P k) → P m) : P n:= by
  induction' n with n hn
  case zero=>
    specialize h zero
    have h1:∀ k < zero, P k:=by
      simp only [zero_eq, not_lt_zero', IsEmpty.forall_iff, forall_const]
    specialize h h1
    exact h
  case succ=>

  sorry



def le_elements (L:M→ Nat) (n:Nat):Set M := {x:M| L x<n}

def eq_elements (L:M→ Nat) (n:Nat):Set M:= {x:M| L x = n}

def strong_induction1 (L : M→ Nat)(n:Nat): (h:(n:Nat)→ (eq_elements L n → P)→ (eq_elements L (succ n)→ P) )→ (eq_elements L n → P)  :=by
  rintro h
  induction' n with n hn
  case zero=>
    specialize h zero

    sorry
  case succ=>
    specialize h n hn
    exact h

def func (L:M→ Nat)(h:(n:Nat)→ (eq_elements L n → P)→ (eq_elements L (succ n)→ P) ):M→ P:=by
  intro x
  have ans:= @strong_induction1 M P L (L x) h ⟨x, rfl ⟩
  exact ans



end Nat
