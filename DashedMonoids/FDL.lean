import Mathlib
import DashedMonoids.ListProp
import DashedMonoids.StrongInduction
--open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

--To import files from this folder use DashedMonoids.filename. To import files from a new folder, first update lakefile.lean

--Basis file will have basic definitions. Universal property of DMon.
--Make freeDashedCriteria file
--Make monoid file with
--Interval file will define an interval and its properties
--Make Bracketing file that will have bracketing
--Make DashAssignmen file
--Make Dashed words file

#check Classical.choose
#check Classical.choose_spec

--universe u v w
#check List.ListTwoOrMore_neq_ListOne


--variable {S: Type _}

--variable {i n m: Nat}

section TypeLogic

namespace TypeLogic

inductive NOT (A:Type _) :Type _
  | intro (h:A→ False) : NOT A

inductive AND (A B:Type _) :Type _
  | intro (a:A)(b:B) : AND A B

inductive OR (A B:Type _) :Type _
  | inl (a:A) : OR A B
  | inr (b:B) : OR A B

def UP_exists_OR {A B C: Type _} (f:A→ C) (g:B→ C): OR A B → C:=
  fun x=> match x with
  | OR.inl a => f a
  | OR.inr b => g b

theorem UP_exists_OR_prop {A B C: Type _} (f:A→ C) (g:B→ C):(∀ a:A, UP_exists_OR f g (OR.inl a) = f a)∧ (∀ b:B, UP_exists_OR f g (OR.inr b) = g b):=by
  constructor
  case left=>
    intro a
    rw[UP_exists_OR]
  case right=>
    intro b
    rw[UP_exists_OR]
  -- rintro (a| b)
  -- case inl=>
  --   exact f a
  -- case inr=>
  --   exact g b

theorem UP_exists_OR_left {A B C: Type _} (f:A→ C) (g:B→ C):(∀ a:A, UP_exists_OR f g (OR.inl a) = f a):=by
  intro a
  rw[UP_exists_OR]

theorem UP_exists_OR_right {A B C: Type _} (f:A→ C) (g:B→ C):(∀ b:B, UP_exists_OR f g (OR.inr b) = g b):=by
    intro b
    rw[UP_exists_OR]
  -- rintro (a| b)
  -- case inl=>
  --   exact f a
  -- case inr=>
  --   exact g b


def inlOR (A B:Type _):A→ OR A B:= λ a=> OR.inl a

def inrOR (A B:Type _):B→ OR A B:= λ b=> OR.inr b

def isInj {A B:Type _} (f:A→ B):= ∀ x y:A, f x = f y → x= y

theorem UP_unique_OR {A B C:Type _}(u v:OR A B→ C):(∀ a:A, u  (OR.inl a) = v (OR.inl a))→ (∀ b:B, u (OR.inr b) = v (OR.inr b)) → u = v:=by
  intro ha hb
  ext (a|b)
  case inl=>
    exact ha a
  case inr=>
    exact hb b

example (A B:Type _) (a:A)(b:B):OR.inl a  ≠  OR.inr b:=by
  intro h
  cases h

-- Define an inductive type for equivalence between two types
structure EQ (A B : Type) :=
(to_fun    : A → B)
(inv_fun   : B → A)
(left_inv  : ∀ x : A, inv_fun (to_fun x) = x)
(right_inv : ∀ y : B, to_fun (inv_fun y) = y)


end TypeLogic

end TypeLogic

namespace DashedMonoid

--This file should have basic definitions/results about Dashed Monoids. Definitions: DMon, Dash, k-dashes, m-multiplication, GenSets wrt dash and mul, Ind wrt dash



-----------------------------------------------------------
---------------Definition of Dashed-Monoids---------------
-----------------------------------------------------------

section Defn


--Dashed-monoid "DMon" is a monoid with unary operation "dash" such that 1' = 1
class DMon (M:Type _) extends Monoid M where
  dash : M → M
  unit_dash : dash 1 = 1

end Defn


section Examples
--Examples of dashed monoids: Monoids, Group, Natural Numbers


variable {M:Type _}[stM:DMon M]


--A Monoid can be a dashed monoid with dash equal to id
def Mon_to_DMon :DMon M where
  dash := id
  unit_dash:= rfl

--Natural numbers are dashed-monoids with the dash equal to id
instance Nat_DMon:DMon Nat where
  dash := id
  unit_dash := by exact rfl

--A group can be a dashed monoid with dash equal to inv.
def Group_to_DMon (G:Type _)[st:Group G]: DMon G:= by
  constructor
  case dash => exact st.inv
  case unit_dash => exact inv_one

end Examples


section BasicProperties

variable {M:Type _}[stM:DMon M]
variable {N:Type _}[stN:DMon N]

section Dashes
--Definitions and properties regarding dashes

--Structure behind dash-generated set
@[ext]
structure Free_dash (X:Type _) where
  val : X
  num : Nat

--Define k-dash inductively
def eval_dash {X:Type _} (inc: X→ M) :Free_dash X → M:= λ ⟨val, dashes ⟩ => match dashes with
  | Nat.zero =>  inc val
  | Nat.succ dashes =>  stM.dash (eval_dash inc ⟨ val, dashes⟩ )


structure Hom_dash  (f:M→ N) where
  cond {X:Type _} (inc:X→ M): eval_dash (f ∘  inc) = f ∘ (eval_dash inc)


--Taking dash of an element k times
-- def dash_k (k:Nat)(x:M):M:=by
--   match k with
--   | Nat.zero => exact x
--   | Nat.succ k => exact stM.dash (dash_k k x)

--alternate definition
-- def dash_k_ (k:Nat)(x:M):M:=by
--   induction' k with _ hk
--   case zero => exact x
--   case succ => exact stM.dash hk

def coeval_dash {X:Type _} (k:Nat) :X→ Free_dash X:=by
  intro x
  constructor
  case val=>
    exact x
  case num=>
    exact k

--Taking zero dashes is same as id: x⁰ = x
theorem dash_0 {X:Type _} (inc :X→ M):∀ x:X, (eval_dash inc (coeval_dash 0 x)) = inc x:=by
  intro x
  rw[coeval_dash]
  rw[eval_dash]


-- theorem dash_zero (x:M):dash_k 0 x = x:=by
--   exact rfl

--Taking one dash is same as dash: x¹ = x'


theorem dash_1 {X:Type _} (inc :X→ M):∀ x:X, (eval_dash inc (coeval_dash 1 x)) = stM.dash (inc x):=by
  intro x
  rw[coeval_dash]
  rw[eval_dash]
  rw[eval_dash]


-- theorem dash_one (x:M):dash_k 1 x = stM.dash x:= by
--   exact rfl

def take_dash {X:Type _} (k:Nat) :Free_dash X→ Free_dash X:=by
  intro ⟨val, num ⟩
  constructor
  case val=>
    exact val
  case num=>
    exact num+k

--Taking k+r dash is same as dash_r of dash_k: xᵏ⁺ʳ = (xᵏ)ʳ

theorem dash_k {X:Type _} (k r:Nat):∀ x:X, take_dash r ( (coeval_dash k x)) = coeval_dash (k+r) x:=by
  intro x
  rw[coeval_dash]
  rw[take_dash]
  rw[coeval_dash]

#check id

example (f:M→ N) (st:Hom_dash f):∀ x:M, f (stM.dash x) = stN.dash (f x):=by
  intro x
  have cond:=st.cond id
  simp at cond
  rw[← dash_1]
  rw[cond]
  simp
  rw[dash_1]
  simp

example (f:M→ N)(hom: ∀ x:M, f (stM.dash x) = stN.dash (f x)):Hom_dash f:=by
  constructor
  case cond=>
    intro X inc
    ext x
    rcases x with ⟨val, num ⟩
    case mk=>
      simp
      induction' num with n hn
      case zero=>
        rw[eval_dash]
        rw[eval_dash]
        simp
      case succ =>
        rw[eval_dash]
        rw[hn]
        rw[eval_dash]
        rw[hom]


end Dashes

section M_pos


--Underlying set of dashed monoid without the unit
def M_pos :Set M:= Set.univ \ {1}


end M_pos



section Basis_dash

--Set generated by the dash operation
def Gen_dash_set {X:Type _}(inc:X→ M):Set M:= by
  intro z
  exact ∃ p:Free_dash X,  eval_dash inc p = z

--Structure given by dash basis
structure Basis_dash {X:Type _} (inc :X→ M) where
  --to fun : Gen_dash X→ M:= eval_dash inc
  inv_fun : M→ Free_dash X
  left_inv  : ∀ x : Free_dash X, inv_fun (eval_dash inc x) = x
  right_inv : ∀ y : M, eval_dash inc (inv_fun y) = y ∨ y=1

--Composite elements of Gen_dash
def GenPP_dash (X:Type _):Free_dash X→ Prop:= fun p=> p.num≠ 0

structure FreeP_dash (X:Type _) where
  val : X
  num : Nat
  num_pos: num ≠ 0

def FreeP_dash_to_Free_dash (X:Type _):FreeP_dash X→ Free_dash X:=  by
  rintro ⟨val, num, _ ⟩
  exact ⟨val, num ⟩

def evalP_dash {X:Type _} (inc:X→ M):FreeP_dash X → M:= (eval_dash inc)∘ (FreeP_dash_to_Free_dash X)

--Structrure of dash generating set
structure GenSet_dash {X:Type _} (inc :X→ M) where
  --to fun : Gen_dash X→ M:= dash_k inc
  inv_fun : M→ Free_dash X
  --left_inv  : ∀ x : Gen_dash X, inv_fun (dash_k inc x) = x
  right_inv : ∀ y : M, eval_dash inc (inv_fun y) = y ∨ y=1

--Structrure of dash indepent set
structure Indp_dash {X:Type _} (inc :X→ M) where
  --to fun : Gen_dash X→ M:= dash_k inc
  --inv_fun : M→ Gen_dash X
  left_inv  : ∀ p q: Free_dash X,  (eval_dash inc p) = (eval_dash inc q) →  p = q
  --right_inv : ∀ y : M, dash_k inc (inv_fun y) = y ∨ y=1

theorem Indp_dash_to_inc_inj {X:Type _}(inc:X→ M) (Indp: Indp_dash inc):∀ x y:X, inc x = inc y → x=y:=by
  intro x y hxy
  have h:(eval_dash inc (coeval_dash 0 x)) = (eval_dash inc (coeval_dash 0 y)):= by
    rw[dash_0]
    rw[dash_0]
    exact hxy
  have g:=Indp.left_inv (coeval_dash 0 x) (coeval_dash 0 y) h
  cases g
  exact rfl


end Basis_dash

section Gen_dash_properties

--If X is mul indep then gen X = X sqcup genP x

variable (X:Type _)

def Gen_dash_to_GenP_dash_OR :Free_dash X→ TypeLogic.OR X (FreeP_dash X):=by
  rintro ⟨val, num ⟩
  by_cases h:num=0
  case pos=>
    left
    exact val
  case neg=>
    right
    constructor
    case val=>
      exact val
    case num=>
      exact num
    case num_pos=>
      exact h

def GenP_dash_OR_to_Gen_dash : TypeLogic.OR X (FreeP_dash X)→ Free_dash X:=by
  rintro (x|⟨val, num, _ ⟩ )
  case inl=>
    constructor
    case val=>
      exact x
    case num=>
      exact 0

  case inr=>
    constructor
    case val=>
      exact val
    case num=>
      exact num


def EQ_Gen_dash_GenP_dash_OR : TypeLogic.EQ (Free_dash X) (TypeLogic.OR X (FreeP_dash X)):=by
  constructor
  case to_fun=>
    exact Gen_dash_to_GenP_dash_OR X
  case inv_fun=>
    exact GenP_dash_OR_to_Gen_dash X
  case left_inv=>
    intro x
    rw[Gen_dash_to_GenP_dash_OR]
    by_cases h:x.num=0
    case pos=>
      simp
      rw[h]
      simp
      rw[GenP_dash_OR_to_Gen_dash]
      simp
      rw[← h]
    case neg=>
      simp
      rw[GenP_dash_OR_to_Gen_dash]
      --simp
      simp[h]

  case right_inv =>
    rintro (x|p)
    case inl =>
      rw[GenP_dash_OR_to_Gen_dash]
      simp
      rw[Gen_dash_to_GenP_dash_OR]
      simp

    case inr =>
      rw[GenP_dash_OR_to_Gen_dash]
      simp
      rw[Gen_dash_to_GenP_dash_OR]
      simp
      by_cases h:p.num=0
      case pos=>
        simp[h]
        exact p.num_pos h
      case neg=>
        simp[h]


--if X is dash independent then X ∩ GenP X is empty
example {X:Type _}(inc:X→ M)(Indp:Indp_dash inc):TypeLogic.isInj (TypeLogic.UP_exists_OR (inc) ( (eval_dash inc)∘  (FreeP_dash_to_Free_dash X))):=by
  rintro (x1|⟨val1, num1, num_pos1 ⟩ ) (x2|⟨val2, num2, num_pos2 ⟩ )  hxy
  case inl.inl=>
    simp
    rw[TypeLogic.UP_exists_OR_left] at hxy
    rw[TypeLogic.UP_exists_OR_left] at hxy
    exact Indp_dash_to_inc_inj inc Indp x1 x2 hxy

  case inr=>
    simp
    rw[TypeLogic.UP_exists_OR_left] at hxy
    rw[TypeLogic.UP_exists_OR_right] at hxy
    simp at hxy
    rw[FreeP_dash_to_Free_dash] at hxy
    rw[← dash_0 inc] at hxy
    have h:=Indp.left_inv ((FreeP_dash.casesOn { val := val1, num := num1, num_pos := num_pos1 } fun val num num_pos ↦
      { val := val, num := num })) (coeval_dash 0 x2)  hxy
    simp at h
    rw[coeval_dash] at h
    simp at h
    exact num_pos1 h.2

  case inr  =>
    simp
    rw[TypeLogic.UP_exists_OR_right] at hxy
    rw[TypeLogic.UP_exists_OR_right] at hxy
    simp at hxy
    rw[FreeP_dash_to_Free_dash] at hxy
    rw[FreeP_dash_to_Free_dash] at hxy
    simp at hxy
    have h:= Indp.left_inv { val := val1, num := num1 } { val := val2, num := num2 } hxy
    simp only [Free_dash.mk.injEq] at h
    exact h

  case inl=>
    simp
    rw[TypeLogic.UP_exists_OR_left] at hxy
    rw[TypeLogic.UP_exists_OR_right] at hxy
    simp at hxy
    rw[FreeP_dash_to_Free_dash] at hxy
    simp at hxy
    rw[← dash_0 inc] at hxy
    have h:= Indp.left_inv (coeval_dash 0 x1) ({ val := val2, num := num2 }) hxy
    rw[coeval_dash] at h
    simp at h
    exact num_pos2 h.2.symm




def Free_dash_to_Free_dash {X Y:Type _}(f:X→ Y):Free_dash X→ Free_dash Y:=fun ⟨a, b ⟩ => ⟨f a, b ⟩

theorem Free_dash_to_Free_dash_prop {X Y:Type _}(f:X→ Y)(inc:Y→ M):∀ p:Free_dash X, eval_dash (inc∘ f) p = eval_dash inc (Free_dash_to_Free_dash f p):=by
  rintro ⟨ val, num⟩
  rw[Free_dash_to_Free_dash]
  simp
  induction' num with num hnum
  case zero=>
    rw[eval_dash]
    rw[eval_dash]
    simp
  case succ=>
    rw[eval_dash]
    rw[eval_dash]
    rw[hnum]

lemma Indp_dash_sub {X Y:Type _}(f:X→ Y)(inj_f:TypeLogic.isInj f)(inc:Y→ M):(Indp:Indp_dash inc)→ Indp_dash ( inc∘ f):= by
  intro indp
  constructor
  intro p q hpq
  cases indp
  case left_inv h=>
    specialize h  (Free_dash_to_Free_dash f p) (Free_dash_to_Free_dash f q)
    rw[Free_dash_to_Free_dash_prop] at hpq
    rw[Free_dash_to_Free_dash_prop] at hpq
    specialize h hpq
    rw[Free_dash_to_Free_dash] at h
    rw[Free_dash_to_Free_dash] at h
    simp at h
    rcases h with ⟨ l, r⟩
    specialize inj_f p.val q.val l
    ext
    exact inj_f
    exact r





def to_GenP_dash_cup {X Y:Type _}:FreeP_dash (TypeLogic.OR X Y)→ TypeLogic.OR (FreeP_dash X) (FreeP_dash Y):=by
  rintro ⟨(x|y), num, num_pos ⟩
  case inl=>
    exact TypeLogic.OR.inl {val:=x, num:=num, num_pos:=num_pos}
  case inr=>
    exact TypeLogic.OR.inr {val:=y, num:=num, num_pos:=num_pos}

def inv_GenP_dash_cup {X Y:Type _}: TypeLogic.OR (FreeP_dash X) (FreeP_dash Y)→ FreeP_dash (TypeLogic.OR X Y):=by
  rintro (⟨x, num, num_pos ⟩ | ⟨y, num, num_pos ⟩ )
  case inl=>
    constructor
    case val=>
      exact TypeLogic.OR.inl x
    case num=>
      exact num
    case num_pos=>
      exact num_pos

  case inr=>
    constructor
    case  val=>
      exact TypeLogic.OR.inr y
    case num=>
      exact num
    case num_pos=>
      exact num_pos


lemma dash_GenP_cup {X Y:Set M}:FreeP_dash (X∪ Y) = (GenP_dash X)∪ (GenP_dash Y):= by
  ext x
  constructor
  case mp=>
    rintro ⟨k,⟨k_ne_0,⟨a,ha ⟩  ⟩  ⟩
    rcases a with ⟨ a, (aX|aY)⟩
    case inl=>
      left
      use k
      constructor
      case left=>
        exact k_ne_0
      case right=>
        use ⟨a, aX ⟩
    case inr=>
      right
      use k
      constructor
      case left=>
        exact k_ne_0
      case right=>
        use ⟨a, aY ⟩
  case mpr=>
    rintro (⟨k,⟨k_ne_0,⟨a,ha ⟩  ⟩  ⟩ |⟨k,⟨k_ne_0,⟨a,ha ⟩  ⟩  ⟩)
    case inl=>
      use k
      constructor
      case left=>
        exact k_ne_0
      case right=>
        constructor
        case w=>
          constructor
          case val=>
            exact a.1
          case property=>
            left
            exact a.2
        case h=>
          exact ha
    case inr=>
      use k
      constructor
      case left=>
        exact k_ne_0
      case right=>
        constructor
        case w=>
          constructor
          case val=>
            exact a.1
          case property=>
            right
            exact a.2
        case h=>
          exact ha


lemma dash_GenP_disjoint {X Y Z:Set M}:(is_Indp_dash Z)→ (X⊆ Z)→ (Y⊆ Z)→ (X∩ Y =∅ )→ (GenP_dash X)∩ (GenP_dash Y)=∅ := by
  intro IndpZ XsubZ YsubZ Disj
  ext x
  constructor
  case mp=>
    rintro ⟨⟨r, ⟨_,⟨a,ha ⟩ ⟩ ⟩ ,⟨k, ⟨_,⟨b,hb ⟩ ⟩ ⟩ ⟩
    specialize IndpZ r ⟨a.1, XsubZ a.2 ⟩
    specialize IndpZ k ⟨b.1, YsubZ b.2⟩
    have h1:dash_k r a.1= dash_k k b.1:= by
      rw[ha]
      rw[← hb]
    specialize IndpZ h1
    have IndpZ:=IndpZ.2
    simp at IndpZ
    have h2:a.1∈ X∩ Y :=by
      constructor
      case left=>
        exact a.2
      case right=>
        rw[IndpZ]
        exact b.2
    rw[Disj] at h2
    exact h2
  case mpr=>
    simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, IsEmpty.forall_iff]



end Gen_dash_properties

section Mul
--Definitions and properties regarding dashes

--Structure behind dash-generated set
@[ext]
structure Free_mul (X:Type _) where
  L : List X

--Define k-dash inductively
def eval_mul {X:Type _} (inc: X→ M) :Free_mul X → M:= λ ⟨L ⟩ => match L with
  | [] =>  1
  | head::tail =>  (inc head)*(eval_mul inc {L:=tail})


structure Hom_mul (f:M→ N) where
  cond {X:Type _ }(inc :X→ M) :  eval_mul (f∘  inc) = f∘ eval_mul inc

theorem mul_0 {X:Type _} (inc: X→ M):eval_mul inc {L:=[]} = 1:=by
  rw[eval_mul]

theorem mul_1 {X:Type _} (inc: X→ M):∀ x:X, eval_mul inc {L:=[x]} = inc x:=by
  intro x
  rw[eval_mul]
  rw[eval_mul]
  simp only [mul_one]


theorem mul_2 {X:Type _} (inc: X→ M):∀ x y:X, eval_mul inc {L:=[x, y]} = (inc x)*(inc y):=by
  intro x y
  rw[eval_mul]
  rw[eval_mul]
  rw[eval_mul]
  simp only [mul_one]

example  (f:M→ N) (st:Hom_mul f):∀ x y:M, (f x) * (f y) = f (x*y):=
  by
  intro x y
  have h:=st.cond id
  simp at h
  rw[← mul_2]
  have h1:x*y = eval_mul id {L:=[x, y]}:=by
    rw[mul_2]
    simp only [id_eq]
  rw[h1]
  rw[h]
  simp only [Function.comp_apply]


example (f:M→ N)(one:f 1 = 1)(hom:∀ x y, (f x)*(f y)=f (x*y)):Hom_mul f:=by
  constructor
  case cond=>
    intro X inc
    ext L
    induction' L with L
    induction' L with head tail tail_h
    case nil=>
      rw[eval_mul]
      simp only [Function.comp_apply]
      rw[eval_mul]
      rw[one]
    case cons=>
      rw[eval_mul]
      simp
      rw[eval_mul]
      rw[tail_h]
      simp
      rw[hom]

end Mul


section Basis_mul

--Set generated by the dash operation
def Gen_mul_set {X:Type _}(inc:X→ M):Set M:= by
  intro z
  exact ∃ p:Gen_mul X,  mul_L inc p = z

--Structure given by dash basis
structure Basis_mul {X:Type _} (inc :X→ M) where
  --to fun : Gen_mul X→ M:= mul_L inc
  inv_fun : M→ Gen_mul X
  left_inv  : ∀ x : Gen_mul X, inv_fun (mul_L inc x) = x
  right_inv : ∀ y : M, mul_L inc (inv_fun y) = y

--Composite elements of Gen_dash
def GenPP_mul (X:Type _):Gen_mul X→ Prop:= fun p=> p.L≠ []∧ ∀ x:X, p.L≠ [x]

structure GenP_mul (X:Type _) where
  L : List X
  L_pos: L ≠ []∧ ∀ x:X, L≠ [x]

def GenP_mul_to_Gen_mul (X:Type _):GenP_mul X→ Gen_mul X:=  by
  rintro ⟨L, _, _ ⟩
  exact ⟨L ⟩

--def dashP_k {X:Type _} (inc:X→ M):GenP_dash X → M:=by
--   intro

--Structrure of dash generating set
structure GenSet_mul {X:Type _} (inc :X→ M) where
  --to fun : Gen_mul X→ M:= mul_k inc
  inv_fun : M→ Gen_mul X
  --left_inv  : ∀ x : Gen_dash X, inv_fun (dash_k inc x) = x
  right_inv : ∀ y : M, mul_L inc (inv_fun y) = y

--Structrure of dash indepent set
structure Indp_mul {X:Type _} (inc :X→ M) where
  --to fun : Gen_dash X→ M:= dash_k inc
  --inv_fun : M→ Gen_dash X
  left_inv  : ∀ p q: Gen_mul X,  (mul_L inc p) = (mul_L inc q) →  p = q
  --right_inv : ∀ y : M, dash_k inc (inv_fun y) = y ∨ y=1

theorem Indp_mul_to_inc_inj {X:Type _}(inc:X→ M) (Indp: Indp_mul inc):∀ x y:X, inc x = inc y → x=y:=by
  intro x y hxy
  rcases Indp with ⟨ h⟩
  specialize h {L:=[x]} {L:=[y]}
  rw[← mul_1 inc] at hxy
  rw[← mul_1 inc] at hxy
  specialize h hxy
  simp only [Gen_mul.mk.injEq, List.cons.injEq, and_true] at h
  exact h



end Basis_mul



section FreeDMon_like

variable {M:Type _}[stM:DMon M]
variable {N:Type _}[stN:DMon N]


section Definition


structure FreeDMon_like (M:Type)[DMon M] where
  length: M→ ℕ
  length_I_0: length 1 = 0
  length_I_0_if:∀ x:M, (length x = 0 → x=1)
  dash_length :Hom_dash length
  mul_length :Hom_mul length

  basis: Type _
  inc_basis:basis → M
  mul_basis: Type _
  inc_mul_basis: mul_basis→ M
  dash_basis:Type _
  inc_dash_basis:dash_basis→ M
  mul_basis_is_mul_basis: Basis_mul inc_mul_basis
  dash_basis_is_dash_basis: Basis_dash inc_dash_basis

  basis_cond_mul_basis_union: TypeLogic.EQ mul_basis (TypeLogic.OR basis  (FreeP_dash dash_basis))
  --basis_cond_mul_basis_disjoint: basis ∩ GenP_dash dash_basis = {}
  basis_cond_dash_basis_union: TypeLogic.EQ dash_basis ( TypeLogic.OR basis ( GenP_mul mul_basis))
  --basis_cond_dash_basis_disjoint: basis ∩ GenP_mul mul_basis = {}


def mul_compos (FDL: FreeDMon_like M):Type _:=GenP_mul FDL.mul_basis

end Definition


variable {FDL: FreeDMon_like M}


section UniProperty

variable {u: FDL.basis→ N}

def u_Sinf1 : Gen_dash FDL.basis → N  :=  by
  rintro p
  exact dash_k u p


noncomputable def u_Sinf: Gen_dash FDL.basis → N:=by
  intro x
  rcases x with ⟨x, prop ⟩
  have k:= Classical.choose prop
  --have h:=
  have y:= Classical.choose (Classical.choose_spec prop)
  exact  dash_k k (u y)


--variable (v: Nat.StrongInduction N M)

def SI:Nat.StrongInduction FDL.mul_basis N:=  by
  constructor
  case Len=>
    exact FDL.length ∘  (FDL.inc_mul_basis)
  case Induct=>
    rintro m hm ⟨x, hx ⟩
    simp at hx
    rcases FDL.basis_cond_mul_basis_union with ⟨f,inv_f, l_inv, r_inv ⟩
    specialize l_inv x
    specialize r_inv (f x)
    rcases FDL.basis_cond_dash_basis_union with ⟨g,inv_g, l_inv_g, r_inv_g ⟩


    rcases f x with (y|⟨val, num,_ ⟩  )
    case inl=>
      exact u y
    case mk.mk.mk.inr=>
      --have qq:=FDL.dash_length FDL.inc_dash_basis y
      rcases g val with (z|z)
      case inl=>
        exact u z
      case inr=>




      sorry

#check Quotient
#check Quot

inductive PrimDMon (X:Type _) where
  | nil : PrimDMon X
  | mul (x y:PrimDMon X) : PrimDMon X
  | dash (x: PrimDMon X) : PrimDMon X


def rel_unit_dash (X:Type):PrimDMon X → PrimDMon X→ Prop:=by
  intro x y
  exact x=PrimDMon.nil ∧ y=PrimDMon.dash PrimDMon.nil

def PrimDMon_quot_unit (X:Type _):= Quot (rel_unit_dash X)

def rel_mul (X:Type):PrimDMon_quot_unit X → PrimDMon_quot_unit X → Prop:=by
  intro x y
  exact ∃ a b c:PrimDMon X, x= Quot.mk (rel_unit_dash X) (PrimDMon.mul a (PrimDMon.mul b c)) ∧ y= Quot.mk (rel_unit_dash X) (PrimDMon.mul (PrimDMon.mul a b) c)

def DMonInd (X:Type _):=Quot (rel_mul X)



inductive stDMon (X:Type _) where
  | inc (x:X) : stDMon X
  | mul (L:List (stDMon X)) :stDMon X
  | dash (val:stDMon X) (num:Nat) : stDMon X




def induce {X:Type _} (f:X→ M):stDMon X → M:=by
  intro x
  match x with
  | stDMon.inc a =>
      exact f a
  | stDMon.mul L =>
      -- exact induce f (stDMon.mul L)
      match L with
      | [] =>
          exact 1
      | a::P =>
          exact (induce f a)*(induce f (stDMon.mul P))
  | stDMon.dash val num =>
      match num with
      | 0 =>
          exact induce f val
      | n+1 =>
          exact stM.dash (induce f (stDMon.dash val n))

def st_unit (X:Type _):stDMon X:= stDMon.mul []

def st_mul (X:Type _):stDMon X → stDMon X → stDMon X:=  by
  intro a b
  exact stDMon.mul [a, b]

def st_dash (X:Type _):stDMon X → stDMon X:=by
  intro x
  exact stDMon.dash x 1

def rel1 (X:Type _):stDMon X → stDMon X→ Prop:= by
  intro x y
  exact stDMon.mul [x] = y

def rel2 (X:Type _):stDMon X → List (stDMon X):= by
  intro x
  match x with
  | stDMon.inc a=> exact [stDMon.inc a]
  | stDMon.mul L=>
                  match L with
                  | [] => exact []
                  | a::P => exact ((rel2 X) a) ++(rel2 X (stDMon.mul P))

  | stDMon.dash val num =>
      match num with
      | 0 => exact (rel2 X) val
      | _+1 =>
          match val with
          | stDMon.inc a => exact [stDMon.dash (stDMon.mul [stDMon.inc a]) num]
          | stDMon.mul L =>
              match L with
              | [] => exact []
              | a::P => exact [stDMon.dash (stDMon.mul (((rel2 X) a) ++(rel2 X (stDMon.mul P)))) num]
          | stDMon.dash val2 num2 =>
              exact [stDMon.dash (stDMon.mul ((rel2 X) val2)) (num+num2)]



def rel_image {A B:Type _}(f:A→ B):A→ A→Prop:=by
  intro x y
  exact f x = f y

instance Rel_Im {A B:Type} (f:A→ B): Setoid (A) where
  r:= fun x  y => f x= f y
  iseqv := by
    constructor
    case refl=>
      exact fun x=> rfl
    case symm=> --exact fun x y h => h.symm
      intro x y h
      exact h.symm
    case trans=>
      intro x y z hxy hyz
      exact hxy.trans hyz

def Im {A B:Type _}(f:A→ B):= Quotient (Rel_Im f)

def fn {A B:Type _}(f:A→ B): A→ Im f:=by
  intro a
  --rw[Im]
  exact ⟦a⟧

def Lift {A B C:Type _}(f :A→ B)(g:A→ C)(eq:∀ a b:A, f a= f b → g a = g b): Im f → C:=by
  --intro x
  --rw[Im] at x
  apply @Quotient.lift A C (Rel_Im f) g
  exact eq

  --have h:=@Quotient.lift A B (Rel_Im f) f


def image.proj {A B C:Type _} (f:A→ B)(g:A→ C):image f → C:= by
  rintro ⟨ a⟩
  exact g a

def image.unique {A B C:Type _} (f:A→ B):(h1 h2:image f→ C)→ (∀ a:A, h1 (image.mk a) = h2 (image.mk a))→ (h1=h2 ):= by
  intro h1 h2 hy
  ext ⟨ a⟩
  exact hy a

def DMON (X:Type _):=image (rel2 X)

def DMON_induce {X:Type _} (f:X→ M):DMON X → M:=by
  rintro ⟨ a⟩
  exact induce f a

structure MySet (X:Type _) where
  prop : X→ Prop


def MySet_to_Set {X:Type _}: (MySet X) → (Set X):= by
  rintro ⟨prop ⟩
  intro T
  exact prop T


def pure {X:Type _} :DMON (DMON X) → DMON X:=by

  rintro ⟨ x⟩
  constructor
  match x with
  | stDMon.inc a=>
      rw[DMON] at a
      match a with
      | image.mk b=>
          exact b
  | stDMon.mul L =>
      rw[DMON] at L
      sorry
  | stDMon.dash val num => sorry


def inc {X:Type _}:X→ DMON X:= by
  intro x
  constructor
  exact stDMon.inc x


theorem th2 {X:Type _} (x y:stDMon X):((rel2 X) x)++((rel2 X) y) = ((rel2 X) (stDMon.mul [x, y])):=by
  match x with
  | stDMon.inc a =>
      rw[rel2]
      rw[rel2]
      rw[rel2]
      rw[rel2]
      simp
      rw[rel2]

  | stDMon.mul L =>
      rw[rel2]
      rw[rel2]
      rw[rel2]
      simp

  | stDMon.dash val num =>
      rw[rel2]
      rw[rel2]
      rw[rel2]
      simp

theorem th1 {X:Type _} (x:stDMon X):(rel2 X) (stDMon.mul ((rel2 X) x)) =(rel2 X) x:= by
  match ((rel2 X) x) with
  | [] =>
    rw[rel2]
  | a::L =>
    rw[rel2]

    sorry


  -- match x with
  -- | stDMon.inc a =>
  --     rw[rel2]
  --     rw[rel2]
  --     rw[rel2]
  --     rw[rel2]
  --     simp
  -- | stDMon.mul L =>
  --     match L with
  --     | [] =>
  --         rw[rel2]
  --         rw[rel2]
  --     | a::L =>
  --         nth_rewrite 1 [rel2]
  --         nth_rewrite 1 [ rel2]

  --         rw[th2]
  --         rw[rel2]
  --         rw[← th2]
  --         sorry

  -- | stDMon.dash val num => sorry


example {X:Type _}(a:X):rel2 X (stDMon.dash (stDMon.mul []) 7) = []:=by
  rw[rel2]


example {X:Type _}(a:X)(n m:Nat):rel2 X (stDMon.dash (stDMon.dash (stDMon.inc a) n) m) = [(stDMon.dash (stDMon.mul [stDMon.inc a]) (n+m))]:=by
  match m with
  | 0 =>
    rw[rel2]
    simp
    match n with
    | 0 =>
      rw[rel2]
      rw[rel2]
      --this is okay
      simp
      sorry
    | n+1=>
      rw[rel2]

  | m+1 =>
    rw[rel2]
    rw[rel2]
    simp
    linarith

example {X:Type _}(a:X):rel2 X (stDMon.dash (stDMon.mul [stDMon.inc a]) 1) = [(stDMon.dash (stDMon.mul [stDMon.inc a]) 1)]:=by
  rw[rel2]
  rw[rel2]
  simp
  rw[rel2]


example {X:Type _}(a:X):rel2 X (stDMon.inc a) = [stDMon.inc a]:=by
  rw[rel2]


example {X:Type _}(a:X):rel2 X (stDMon.mul [(stDMon.inc a)]) = [stDMon.inc a]:=by
  rw[rel2]
  rw[rel2]
  rw[rel2]
  simp only [List.singleton_append]

example {X:Type _}(a:X):rel2 X (stDMon.mul [stDMon.inc a, stDMon.mul []]) = [stDMon.inc a]:=by
  rw[rel2]
  rw[rel2]
  rw[rel2]
  rw[rel2]
  simp

example {X:Type _}(a:X):rel2 X (stDMon.mul [stDMon.inc a, stDMon.mul [stDMon.inc a]]) = [stDMon.inc a, stDMon.inc a]:=by
  rw[rel2]
  rw[rel2]
  rw[rel2]
  rw[rel2]
  rw[rel2]
  --simp
  rw[rel2]
  rw[rel2]
  simp


def uG: (n:Nat)→(x:M)→ (x∈ FDL.mul_basis)→ (FDL.length x=n)→
N:=by
  intro n
  induction' n with n hn
  case zero=>

    sorry
  case succ=>

    sorry


def Nat_Pos: Set Nat:={n:Nat|n≠ 0}

def Sum_Nat:List Nat→ Nat:= fun L=> match L with
  | []=> 0
  | a::L=> a+Sum_Nat L

example (L:List Nat)(h:∀ x∈ L, x≠ 0)(h0:L≠ [])(h1:∀ n:Nat, L≠ [n]):∀ x∈ L, x< Sum_Nat L:=by
  intro x hx
  induction' L with head tail tail_h
  case nil=>
    simp at hx
  case cons=>
    rcases hx with (a|b)
    case head=>
      rw[Sum_Nat]
      simp
      have t_not_empty:tail≠ []:= by sorry
      have y_in_t:∃ y∈ tail,true:=by
        induction' tail with a t ht
        simp at t_not_empty
        use a
        simp
      rcases y_in_t with ⟨y, hy, _ ⟩
      specialize h y
  sorry

theorem thm (L:List Nat):(h:∀ x∈ L, x> 0)→ (h0:L≠ [])→ (h1:∀ n:Nat, L≠ [n])→ ∀ x∈ L, x< Sum_Nat L:= by
  intro h h0 h1
  match L with
  |[]=> simp
  |[a]=>  specialize h1 a
          exfalso
          simp at h1

  |[a, b]=> intro x hx
            rcases hx
            case head=>
              specialize h b
              have b_in:b∈ [a, b]:=  by
                simp only [List.mem_cons, List.mem_singleton,   or_true]
                simp only [List.not_mem_nil, or_false, or_true]
              specialize h b_in
              rw[Sum_Nat]
              rw[Sum_Nat]
              rw[Sum_Nat]
              simp
              linarith
            case tail g=>
              rcases g
              case head=>
                have a_in:a∈ [a, b]:= by
                  simp only [List.mem_cons, List.mem_singleton, true_or]
                specialize h a a_in
                rw[Sum_Nat]
                rw[Sum_Nat]
                rw[Sum_Nat]
                linarith

              case tail g=>
                rcases g

  | [a, b, c, d] => intro x hx
                    rcases hx
                    case head=>
                      have b_in:b∈ [a, b, c, d]:=by
                        simp
                      specialize h b b_in
                      rw[Sum_Nat]
                      rw[Sum_Nat]
                      linarith
                    case tail g=>
                      rcases g
                      case head=>
                        have a_in:a∈ [a, b, c, d]:=by
                          simp
                        specialize h a a_in
                        rw[Sum_Nat]
                        rw[Sum_Nat]
                        linarith

                      case tail g=>
                        rcases g
                        case head=>
                          have a_in:a∈ [a, b, c, d]:=by
                            simp
                          specialize h a a_in
                          rw[Sum_Nat]
                          rw[Sum_Nat]
                          rw[Sum_Nat]
                          linarith

                        case tail g=>
                          rcases g
                          case head=>
                            have a_in:a∈ [a, b, c, d]:=by
                              simp
                            specialize h a a_in
                            rw[Sum_Nat]
                            rw[Sum_Nat]
                            rw[Sum_Nat]
                            rw[Sum_Nat]
                            linarith

                          case tail g=>
                            rcases g

  | a::b::c::L =>   intro x hx
                    rcases hx
                    case head=>
                      have b_in:b∈ a::b::c::L:=by
                        simp only [List.mem_cons, true_or, or_true]
                      specialize h b b_in
                      rw[Sum_Nat]
                      rw[Sum_Nat]
                      linarith

                    case tail g=>
                      have th:= thm (b::c::L)
                      have thh:∀ x∈ b::c::L, x>0:=by
                        intro y hy
                        have thhy:y∈ a::b::c::L:=by
                          simp
                          simp at hy
                          rcases hy
                          case inl L=>
                            right
                            left

                            exact L
                          case inr R=>
                            right
                            right
                            exact R
                        exact h y thhy

                      specialize th thh

                      have th0:b::c::L≠ []:=by
                        simp

                      specialize th th0

                      have th1:∀ n:Nat, b::c::L≠ [n]:=by
                        intro n
                        simp only [ne_eq, List.cons.injEq, and_false, not_false_eq_true]

                      specialize th th1 x g
                      rw[Sum_Nat]
                      linarith
