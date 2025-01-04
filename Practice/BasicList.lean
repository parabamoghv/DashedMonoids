import Mathlib
--open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

variable {S: Type _}{M: Type _}[Monoid M]

variable {i n m: Nat}

#check Set.univ
#check id S
#check List S
#check List.append

example (a b: List S):List S:= by
  exact a++b

instance ListMonoid: Monoid (List S) where
  mul x y:= x++y
  mul_assoc := List.append_assoc
  one := []
  mul_one := List.append_nil
  one_mul := List.nil_append




def Lift (f:S→ M):List S→ M:= by
  intro x
  match x with
  | [] => exact 1
  | a :: l => exact (f a) * ((Lift f) l)


def Lift1 (f:S→ M):List S→ M:= by
  intro x
  induction' x with a L hL
  exact 1

  exact (f a)*hL

def muls (U:List M):M:= Lift id U

def muls_coe {X: Set M}(U: List X):M:= Lift (fun x => x.1) U

  --have f:X→ M:= fun x => x.1


structure fact (x:M) where
  U: List M
  muls_eq: muls U = x

--structure factS (x: M) (S:Set M) extends fact x where

structure factS1 (x: M)(S:Set M) where
  U: List M
  muls_eq: muls U = x
  in_S : ∀ a∈ U, a∈ S

structure factS (x: M)(S:Set M) where
  U: List S
  muls_eq: muls_coe U = x


#check Set.univ



def isGenerator (S:Set M):= ∀ x:M, ∃ _:factS x S, True

def isMultInd (S:Set M):= ∀ x:M, ∀ f g: factS x S, f=g

def isBasis (S:Set M):= (isGenerator S)∧ (isMultInd S)

example :isGenerator (Set.univ : Set M):= by
  intro x
  constructor
  case w=>
    constructor
    case U=>
    --  have h:x∈ Set.univ:= by
    --    exact trivial
      exact [⟨ x, trivial⟩ ]
    case muls_eq=>
      rw[muls_coe]
      rw[Lift]
      simp
      --rw[Lift]
      exact mul_one x
  case h=>
    exact trivial
--variable {a:S}

def MonBasis :Set (List S):= {[a]| a:S}

lemma MonBasisMem (x:( MonBasis:Set (List S))):∃a:S, [a]=x:=by
  --rcases x with ⟨a, ha ⟩
  --rw[MonBasis] at ha
  --simp at ha
  --simp
  exact x.2




theorem MonBasis_isGenerator : isGenerator (MonBasis:Set (List S)):= by
  intro x
  constructor
  case w=>
    constructor
    case U=>
      induction' x with a L hL
      exact []
      have h: [a]∈ MonBasis:= by
        rw[MonBasis]
        simp only [Set.mem_setOf_eq, List.cons.injEq, and_true, exists_eq]
      exact ⟨ [a], h⟩ ::hL
    case muls_eq=>
      rw[muls_coe]
      induction' x with x hx cx
      rw[Lift]
      exact rfl
      simp
      rw[Lift]
      simp
      rw[cx]
      rfl
  case h=>
    exact trivial


lemma isMultInd_nil (U: List (MonBasis: Set (List S)))(h:muls_coe U=[]):U=[]:=by
  induction' U with a L hL
  exact rfl
  rw[muls_coe] at h
  rw[Lift] at h
  sorry


theorem MonBasis_isMultInd : isMultInd (MonBasis: Set (List S)):= by
  intro x
  intro ⟨U, mU⟩  ⟨V, mV⟩
  induction' x with a L hL
  sorry
  sorry
