import Mathlib
--open Finset
import Symm
set_option autoImplicit false
set_option maxHeartbeats 0

variable {S: Type _}

variable {i n m: Nat}

#check eqTrans

structure Mon_n (S:Type _)(n:Nat) where
  u:Nat→ Option S
  hsome: ∀ i<n, ∃ a:S, (u i = Option.some a)
  hnone: ∀ i≥ n, (u i=Option.none)

structure Mon1 (S:Type _) where
  n:Nat
  U:Mon_n S n

structure Mon (S:Type _) where
  n:Nat
  u:Nat → Option S
  hsome: ∀ i<n, ∃ a:S, (u i = Option.some a)
  hnone: ∀ i≥ n, (u i=Option.none)


theorem MonExt (U V:Mon S): U=V↔ U.u=V.u ∧ U.n=V.n:= by
  constructor
  intro h
  constructor
  exact congrArg Mon.u h
  exact congrArg Mon.n h
  rintro ⟨ hu, hn⟩
  rcases U with ⟨Uu, Un, Usome, Unone⟩
  rcases V with ⟨Vu, Vn, Vsome, Vnone⟩
  simp at hu
  simp at hn
  cases hu
  cases hn
  rfl


def mul (U V:Mon S):Mon S:= by
  constructor
  case u =>
    intro i
    by_cases i<U.n
    exact U.u i
    by_cases i<U.n+V.n
    exact V.u (i-U.n)
    exact Option.none
  case n =>
    exact U.n+V.n
  case hsome =>
    intro i hi
    by_cases h:i<U.n
    have ⟨ a, ha⟩ := U.hsome i h
    use a
    simp[h]
    exact ha

    have htemp: i≥ U.n:=  Nat.not_lt.mp h
    have hv:i-U.n<V.n:=  Nat.sub_lt_left_of_lt_add htemp hi
    have ⟨a, ha ⟩:= V.hsome (i-U.n) hv
    use a
    simp only [h, hi, dite_eq_ite, ite_true, ite_false]
    exact ha

  case hnone =>
    intro i hi
    have nhiu: ¬ i<U.n:= by linarith
    simp[nhiu]
    intro h
    exfalso
    linarith


def unit : Mon S:= by
  constructor
  case u =>
    intro
    exact Option.none
  case n =>
    exact 0
  case hsome =>
    intro i hi
    exfalso
    contradiction
  case hnone =>
    simp only [ge_iff_le, zero_le, forall_true_left, forall_const]



theorem unit_mul (U:Mon S):mul unit U = U:= by
  rcases U with ⟨n, u, hsome, hnone⟩
  rw[mul]
  rw[unit]
  rw[MonExt]
  constructor
  simp
  ext j x
  by_cases h:j<n
  simp only [h, ite_true, Option.mem_def]
  simp[h]
  have h:= hnone j (Nat.not_lt.mp h)
  rw[h]
  simp only [not_false_eq_true]
  simp only [zero_add]


theorem mul_unit (U:Mon S):mul U unit = U:= by
  rcases U with ⟨n, u, hsome, hnone⟩
  rw[mul]
  rw[unit]
  rw[MonExt]
  constructor
  simp
  ext j x
  by_cases h:j<n
  simp[h]
  simp[h]
  have h:= hnone j (Nat.not_lt.mp h)
  rw[h]
  simp
  simp

theorem mulWord_assoc (U V W:Mon S): mul (mul U V) W = mul U (mul V W):= by
  rcases U with ⟨Un, Uu, Usome, Unone ⟩
  rcases V with ⟨Vn, Vu, Vsome, Vnone ⟩
  rcases W with ⟨Wn, Wu, Wsome, Wnone ⟩
  rw[mul]
  rw[mul]
  rw[mul]
  rw[mul]
  rw[MonExt]
  constructor
  simp
  ext j x
  by_cases h1: j< Un
  have h2: j<Un+Vn:=  Nat.lt_add_right Vn h1
  simp[h2]
  simp[h1]

  by_cases h2:j<Un+Vn
  have h11: j≥ Un:=  Nat.not_lt.mp h1
  have h3:j<Un+(Vn+Wn):= by
    rw[← Nat.add_assoc]
    exact Nat.lt_add_right Wn h2
  have h4: j-Un<Vn:=  Nat.sub_lt_left_of_lt_add h11 h2
  simp[h2]
  simp[h1]
  simp[h3]
  simp[h4]

  simp[h2]
  by_cases h3:j<Un+Vn+Wn
  have h31:j<Un+(Vn+Wn):=by
    rw[← Nat.add_assoc]
    exact h3
  simp[h3]
  simp[h1]
  simp[h31]
  have h21:¬ j-Un<Vn:=by
    --have h22: j≥ Un+Vn:=  Nat.not_lt.mp h2
    have h23:j-Un≥ Vn:= Nat.le_sub_of_add_le' (Nat.not_lt.mp h2)
    linarith
  simp[h21]
  have h32:j-Un<Vn+Wn:=by
    --have h12: j≥ Un:=  Nat.not_lt.mp h1
    exact Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h1) h31
  simp[h32]
  --have h4:j-(Un+Vn)=j-Un-Vn:=by
  --  exact Nat.sub_add_eq j Un Vn
  rw[Nat.sub_add_eq j Un Vn]

  simp[h3]
  simp[h1]
  have h31:¬ j<Un+(Vn+Wn):= by
    rw[← add_assoc]
    exact h3
  simp[h31]

  simp
  rw[← Nat.add_assoc]


instance: Monoid (Mon S) where
  mul:= mul
  mul_assoc:= mulWord_assoc
  one:= unit
  one_mul:= unit_mul
  mul_one:= mul_unit



def Lsplit1 (U :Mon S)(hn:U.n>0):Mon S:= by
  rcases U with ⟨n, u, some, none ⟩
  simp only [gt_iff_lt] at hn
  specialize some 0 hn
  constructor
  case u=>
    intro i
    by_cases i<1
    exact u 0
    exact Option.none
  case n=>
    exact 1
  case hsome=>
    intro a ha
    have ha: a=0:=  Nat.lt_one_iff.mp ha
    rw[ha]
    exact some
  case hnone=>
    intro i hi
    simp[hi]
    intro h
    exfalso
    linarith

def Lsplit2 (U:Mon S)(hn:U.n>0):Mon S:= by
  rcases U with ⟨n, u, some, none ⟩
  simp only [gt_iff_lt] at hn
  constructor
  case u=>
    intro i
    exact u (i+1)
  case n=>
    exact n-1
  case hsome=>
    intro i hi
    have hi: i+1<n:=  Nat.add_lt_of_lt_sub hi
    exact some (i+1) hi
  case hnone=>
    intro i hi
    have hi: i+1≥ n:=  Nat.le_add_of_sub_le hi
    exact none (i+1) hi

theorem Lsplit_mul (U:Mon S)(hn:U.n>0):mul (Lsplit1 U hn) (Lsplit2 U hn)=U:=by
  rcases U with ⟨n, u, some, none ⟩
  simp at hn
  rw[Lsplit1]
  rw[Lsplit2]
  rw[mul]
  rw[MonExt]
  constructor
  simp
  ext i x
  by_cases h1: i=0
  simp[h1]
  simp[h1]
  have h11: 1+(n-1)=n:= Nat.add_sub_of_le hn
  by_cases h2:i<n
  rw[h11]
  simp[h2]
  have h12: i-1+1=i:=  Nat.succ_pred h1
  rw[h12]

  rw[h11]
  simp[h2]
  have h2:i≥ n:=  Nat.not_lt.mp h2
  specialize none i h2
  rw[none]
  simp only [not_false_eq_true]

  simp
  exact Nat.add_sub_of_le hn


def len (U:Mon S):Nat:=U.n


def mul_monoid_words {M:Type _}[Monoid M]:Mon1 M→ M:=by
  intro ⟨ n, U ⟩
  induction' n with n hn
  exact 1
  sorry
-- have h1:∀ i<n, ∃ a:M, u i= some a:= by
--   intro i hi
--   have h11: i<Nat.succ n:=  Nat.lt.step hi
--   exact f i h11
-- have h2:∀ i≥ n, u i= none:= by
--   intro i hi



example {M:Type}(unitM:M)(hn: ∀ n:Nat, (∀ U:Mon S, U.n=n→ M)→   (∀ V:Mon S, V.n=Nat.succ n→ M) ):Mon S→ M:= by
  intro ⟨n, u, f, g ⟩

  sorry
