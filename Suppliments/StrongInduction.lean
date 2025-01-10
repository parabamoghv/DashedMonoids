import Mathlib
--import DashedMonoids.Interval
--open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

--Properties of Lists that are not in MathLib


universe u v w


--Induction and strong induction that eliminates to type


namespace Nat

section Slice

@[simp]
def Slice {X:Type _}(Len : X → Nat) (n:Nat):Set X:={x:X| Len x = n}

@[simp]
def SliceLe {X:Type _} (Len: X→ Nat)(n:Nat):Set X:={x:X| Len x<n}

@[simp]
def SliceLeq {X:Type _} (Len:X→ Nat)(n:Nat):Set X:=SliceLe Len n ∪ Slice Len n

theorem SliceLe0 {X:Type _} (Len: X→ Nat):SliceLe Len 0 = {}:=by
  ext x
  constructor
  case mp=>
    intro xh
    simp only [SliceLe, not_lt_zero', Set.setOf_false, Set.mem_empty_iff_false] at xh
  case mpr=>
    simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff]

def EmptyFunSlice {X Y:Type _} (Len: X→ Nat):SliceLe Len 0→ Y:=by
  rw[ SliceLe0]
  rintro ⟨ x, xh⟩
  --exfalso
  simp at xh

theorem SliceLeq0 {X:Type _} (Len: X→ Nat):SliceLeq Len 0 = Slice Len 0:=by
  ext x
  constructor
  case mp=>
    rintro (a|b)
    case inl=>
      simp at a
    case inr=>
      exact b
  case mpr=>
    intro xh
    right
    exact xh

theorem SliceLeqSuccn_eq_SliceLeqn_cup_SliceSuccn {X:Type _} (Len: X→ Nat) (n:Nat):SliceLeq Len (succ n) = SliceLeq Len  n ∪ Slice Len (succ n):=by
  ext x
  constructor
  case mp=>
    intro xh
    simp at xh
    cases xh
    case inl h=>
      left
      simp
      by_cases h1:Len x < n
      case pos=>
        left
        exact h1

      case neg=>
        right
        linarith

    case inr h=>
      simp
      right
      exact h

  case mpr=>
    intro xh
    simp at xh
    simp
    cases xh
    case inl h=>
      left
      cases h
      case inl h=>
        linarith
      case inr h=>
        linarith

    case inr h=>
      right
      exact h

def FunSliceLeqn_and_FunSliceSuccn_to_FunSliceLeqSuccn {X Y:Type _} (Len: X→ Nat) (n:Nat):(u: SliceLeq Len n→ Y) →  (v:Slice Len (succ n)→ Y)→ (SliceLeq Len (succ n) → Y):=by
  rintro u v ⟨x, xh ⟩
  rw[SliceLeqSuccn_eq_SliceLeqn_cup_SliceSuccn] at xh
  simp at xh
  by_cases h:Len x<  n
  case pos=>
    have ans:SliceLeq Len n:=by
      use x
      simp
      left
      exact h
    exact u ans
  case neg=>
    have h1:Len x = n ∨ Len x = succ n:=by
      cases xh
      case inl xh=>
        cases xh
        case inl xh=>
          exfalso
          exact h xh
        case inr xh=>
          left
          exact xh
      case inr xh=>
        right
        exact xh

    by_cases h: Len x= n
    case pos=>
      have ans:SliceLeq Len n:=by
        use x
        simp
        right
        exact h
      exact u ans

    case neg=>
      have h2:Len x=succ n:=by
        cases h1
        case inl xh=>
          exfalso
          exact h xh

        case inr xh=>
          exact xh

      have ans : Slice Len (succ n):=by
        use x
        simp
        exact h2

      exact v ans


theorem SliceLeqn_eq_SliceLeSuccn {X:Type _} (Len: X→ Nat) (n:Nat):SliceLeq Len n = SliceLe Len (succ n):=by
  ext x
  constructor
  case mp=>
    intro xh
    simp at xh
    simp
    cases xh
    case inl le=>
      linarith
    case inr eq=>
      linarith

  case mpr=>
    intro xh
    simp at xh
    simp
    by_cases h:Len x<n
    case pos=>
      left
      exact h
    case neg=>
      right
      linarith

def FunSliceLeqn_to_FunSliceLeSuccn {X Y:Type _} (Len: X→ Nat) (n:Nat):(SliceLeq Len n → Y) → ( SliceLe Len (succ n)→ Y):=by
  intro u
  rw[← SliceLeqn_eq_SliceLeSuccn Len n]
  exact u



def FunSliceLeSuccn_to_FunSliceLeqn {X Y:Type _} (Len: X→ Nat) (n:Nat):(SliceLe Len (succ n) → Y) → ( SliceLeq Len ( n)→ Y):=by
  intro u
  rw[SliceLeqn_eq_SliceLeSuccn Len n]
  exact u





structure Fun (X Y:Type _) where
  Len:X→ Nat
  u:X→ Y

structure BluePrint (X Y:Type _) where
  (Len:X→ Nat)
  (layers:(n:Nat)→ Slice Len n→ Y)

def Fun_to_BluePrint (X Y:Type _):(f:Fun X Y)→ (BluePrint X Y):=by
  rintro ⟨Len, u ⟩
  constructor
  case Len=>
    exact Len
  case layers=>
    rintro n ⟨x,_ ⟩
    exact u x


def BluePrint_to_Fun (X Y:Type _): (st:BluePrint X Y)→ Fun X Y:=by

  rintro ⟨Len, layers ⟩
  constructor
  case Len=>
    exact Len
  case u=>
    intro x
    exact layers (Len x) ⟨x, rfl ⟩


theorem Fun_to_BluePrint_to_Fun (X Y:Type _)(f:Fun X Y):BluePrint_to_Fun X Y (Fun_to_BluePrint X Y f)=f:= rfl

theorem BluePrint_to_Fun_to_BluePrint (X Y:Type)(st:BluePrint X Y):Fun_to_BluePrint X Y (BluePrint_to_Fun X Y st)=st:=by
  rw[BluePrint_to_Fun]
  simp
  rw[Fun_to_BluePrint]
  simp
  cases st
  case mk len layer=>
    simp
    ext n ⟨x,hx ⟩
    induction' hx
    simp

end Slice

section Induction

inductive empty:Type _ where


example {p q:Prop} :((p→ q))↔ (( ¬  p) ∨   q):=by
  constructor
  case mp=>
    intro h
    by_cases x:p
    case pos=>
      right
      exact h x
    case neg=>
      left
      exact x
  case mpr=>
    intro h t
    cases h
    case inl x=>
      by_contra _
      exact x t
    case inr x=>
      exact x


structure StrongInduction (X Y:Type _) where
  Len :X→ Nat
  Induct: ∀ (m:Nat), (SliceLe Len m→ Y)→ Slice Len (m)→ Y

def StrongInductionBaseCase (X Y:Type _) :(SIH:StrongInduction X Y)→ Slice SIH.Len 0 → Y:=by
  rintro ⟨Len, Induct ⟩
  exact Induct 0 (@EmptyFunSlice X Y Len)

structure StrongInductionLeq (X Y:Type _) where
  Len:X→ Nat
  Base:SliceLeq Len 0→ Y
  Induct: ∀ (m:Nat), (SliceLeq Len m→ Y)→ SliceLeq Len (succ m)→ Y

def StrongInduction_to_StrongInductionLeq (X Y:Type _):StrongInduction X Y → StrongInductionLeq X Y:=by
  rintro SIH
  constructor
  case Len=>
    exact SIH.Len
  case Base=>
    rw[SliceLeq0]
    exact StrongInductionBaseCase X Y SIH
  case Induct=>
    intro m u
    have v:=SIH.Induct (succ m) (FunSliceLeqn_to_FunSliceLeSuccn SIH.Len m u)
    have ans:=FunSliceLeqn_and_FunSliceSuccn_to_FunSliceLeqSuccn SIH.Len m u v
    exact ans

--Same as the usual induction
structure StrongInductionEq (X Y:Type _) where
  Len:X→ Nat
  Base:Slice Len 0→ Y
  Induct: ∀ (m:Nat), (Slice Len m→ Y)→ Slice Len (succ m)→ Y

def StrongInductionLeq_to_StrongInductionEq (X Y:Type _):StrongInductionLeq X Y → StrongInductionEq X Y:=by
  rintro SIH
  constructor
  case Len=>
    exact SIH.Len
  case Base=>
    rw[← SliceLeq0]
    --exact StrongInductionBaseCase X Y SIH
    exact SIH.Base

  case Induct=>
    intro m
    sorry




end Induction


end Nat


inductive NOT (A:Type _) :Type _
  | intro (h:A→ False) : NOT A

inductive AND (A B:Type _) :Type _
  | intro (a:A)(b:B) : AND A B

inductive OR (A B:Type _) :Type _
  | inl (a:A) : OR A B
  | inr (b:B) : OR A B

example (A B C:Type _)(f:A→ C)(g:B→ C): OR A B → C:=by
  rintro (a| b)
  case inl=>
    exact f a
  case inr=>
    exact g b

def inlOR (A B:Type _):A→ OR A B:= λ a=> OR.inl a

example (A B C:Type _)(u v:OR A B→ C):(∀ a:A, u  (OR.inl a) = v (OR.inl a))→ (∀ b:B, u (OR.inr b) = v (OR.inr b)) → u = v:=by
  intro ha hb
  ext (a|b)
  case inl=>
    exact ha a
  case inr=>
    exact hb b

-- Define an inductive type for equivalence between two types
structure EQ (A B : Type) :=
(to_fun    : A → B)
(inv_fun   : B → A)
(left_inv  : ∀ x : A, inv_fun (to_fun x) = x)
(right_inv : ∀ y : B, to_fun (inv_fun y) = y)
