import Mathlib
--import DashedMonoids.Interval
--open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

--Properties of Lists that are not in MathLib


universe u v w


--Induction and strong induction that eliminates to type


namespace Nat


structure Fun (X Y:Type _) where
  Len:X→ Nat
  u:X→ Y

example (X Y:Type _)(f g:Fun X Y):(f.Len=g.Len)→ (f.u=g.u)→ f=g:=by
  intro eqlen equ
  cases f
  cases g
  simp only [Fun.mk.injEq]
  constructor
  case left=>
    exact eqlen
  case right=>
    exact equ

def Slice (X:Type _)(Len:X→ Nat) (n:Nat) : Set X:={x| Len x = n}


structure BluePrint (X Y:Type _) where
  (Len:X→ Nat)
  (layers:(n:Nat)→ Slice X Len n→ Y)

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


structure Induct_eq (X Y:Type _)  where
  Len : X→ Nat
  Base: Slice X Len 0 → Y
  Induct: ∀ (m:Nat), (Slice X Len m→ Y)→ Slice X Len (succ m)→ Y

def Induct_eq_to_BluePrint (X Y:Type _):Induct_eq X Y → BluePrint X Y :=by
  rintro ⟨Len, Base, IH ⟩
  constructor
  case Len=>
    exact Len
  case layers=>
    intro n
    induction' n with n hn
    case zero=>
      exact Base
    case succ=>
      exact IH n hn

def BluePrint_to_Induct_eq (X Y:Type _):BluePrint X Y→ Induct_eq X Y:=by
  rintro ⟨Len, Layer ⟩
  constructor
  case Len=>
    exact Len
  case Base=>
    exact Layer 0
  case Induct=>
    intro m _
    exact Layer (succ m)

example (X Y:Type _)(st:BluePrint X Y):Induct_eq_to_BluePrint  X Y (BluePrint_to_Induct_eq X Y st) = st:=by
  rcases st with ⟨Len,layers ⟩
  rw[BluePrint_to_Induct_eq]
  simp
  rw[Induct_eq_to_BluePrint]
  simp
  ext n ⟨x, xh ⟩

  induction' n with n _
  simp
  simp

example (X Y:Type _)(ih:Induct_eq X Y):BluePrint_to_Induct_eq X Y (Induct_eq_to_BluePrint X Y ih) = ih:=by
  rw[BluePrint_to_Induct_eq]
  rw[Induct_eq_to_BluePrint]
  simp
  rcases ih with ⟨Len, Base, Induct ⟩
  simp
  ext n f x

  induction' n with n hn
  --may not be true
  simp
  sorry
  sorry


def SliceLeq (X:Type _)(Len:X→ Nat) (n:Nat) : Set X:={x| Len x ≤  n}

def SliceLeq_to_SliceLeq (X:Type _)(Len:X→ Nat)(n m:Nat)(leq:n≤ m):SliceLeq X Len n→ SliceLeq X Len m:=by
  rintro ⟨x, hx ⟩
  use x
  rw[SliceLeq] at hx
  rw[SliceLeq]
  simp only [Set.mem_setOf_eq]
  simp only [Set.mem_setOf_eq] at hx
  exact hx.trans leq

def Slice_to_SliceLeq (X:Type _)(Len:X→ Nat)(n :Nat):Slice X Len n→ SliceLeq X Len n:=by
  rintro ⟨x, hx ⟩
  rw[Slice] at hx
  simp only [Set.mem_setOf_eq] at hx
  use x
  rw[SliceLeq]
  simp only [Set.mem_setOf_eq]
  rw[hx]

example (X:Type _)(Len:X→ Nat) (n:Nat):SliceLeq X Len (succ n)=SliceLeq X Len n ∪ Slice X Len (succ n):=by
  ext x
  constructor
  case mp=>
    intro hx
    rw[SliceLeq] at hx
    simp at hx
    by_cases h:Len x≤ n
    case pos=>
      left
      rw[SliceLeq]
      simp
      exact h
    case neg=>
      have h:Len x=succ n:=by linarith
      right
      rw[Slice]
      simp
      exact h
  sorry

structure BluePrintLeq (X Y:Type _) where
  (Len:X→ Nat)
  (layers:(n:Nat)→ SliceLeq X Len n→ Y)
  --(cond: ∀ n:Nat, ∀ m:Nat, (leq: n≤ m)→ (x:SliceLeq X Len n)→ layers n x=(layers m (SliceLeq_to_SliceLeq X Len n m leq x) ))

def BluePrintLeq_to_BluePrint (X Y:Type _) :BluePrintLeq X Y→ BluePrint X Y:= by
  rintro ⟨Len,layers⟩
  constructor
  case Len=>
    exact Len
  case layers=>
    rintro n x
    exact layers n (Slice_to_SliceLeq X Len n x)


def BluePrint_to_BluePrintLeq (X Y:Type _) :BluePrint X Y→ BluePrintLeq X Y:= by
  rintro ⟨Len, Layers ⟩
  constructor
  case Len=>
    exact Len
  case layers=>
    rintro n ⟨x, _ ⟩
    exact Layers (Len x) ⟨x,rfl ⟩
  -- case cond=>
  --   intro n m leq
  --   intro x
  --   simp
  --   rw[SliceLeq_to_SliceLeq]

structure InductLeq (X Y:Type _)  where
  Len : X→ Nat
  Base: SliceLeq X Len 0 → Y
  Induct: ∀ (m:Nat), (SliceLeq X Len m→ Y)→ SliceLeq X Len (succ m)→ Y

def InductLeq_to_BluePrintLeq (X Y:Type _):InductLeq X Y → BluePrintLeq X Y:=by
  rintro ⟨Len, Base, Induct⟩
  constructor
  case Len=>
    exact Len
  case layers=>
    intro n
    induction' n with n hn
    case zero=>
      exact Base
    case succ=>
      exact Induct n hn


section UsualInduction

variable {X Y:Type _}
variable (Len: X→ Nat)

#check Set.univ

inductive EqGrade {Grade:Nat→ Type _}:(n:Nat)→ (m:Nat)→ (Grade n)→ (Grade m)→ Prop where
  | rfl (n:Nat) (x:Grade n): EqGrade n n x x

def Trans {Grade:Nat→ Type _}:(n:Nat)→ (m:Nat)→(eqnm:n=m)→  (Grade n)→  (Grade m):= by
  intro n  m eqnm x
  induction' eqnm
  exact x

theorem EqGrade_ext {Grade:Nat→ Type _}:(n:Nat)→ (m:Nat)→ (x:Grade n)→ (y:Grade m)→ (eqnm:n=m)→ (y=Trans n m eqnm x )→ (EqGrade n m x y):=by
  sorry

theorem EqGrade_rfl {Grade:Nat→ Type _} (n:Nat)(x:Grade n):EqGrade n n x x:=EqGrade.rfl n x

theorem EqGrade_symm {Grade:Nat→ Type _} (n:Nat)(m:Nat)(x:Grade n)(y:Grade m):(EqGrade n m x y) ↔ (EqGrade m n y x):=by
  constructor
  case mp=>
    intro h
    induction' h with h hn
    exact EqGrade.rfl n h
  case mpr=>
    intro h
    induction' h with h hn
    exact EqGrade.rfl m h

theorem EqGrade_trans {Grade:Nat→ Type _} (n m p:Nat)(x:Grade n)(y:Grade m)(z:Grade p):EqGrade n m x y→  EqGrade m p y z→ EqGrade n p x z:=by
  intro eqnm eqmp
  induction' eqnm with eqh
  exact eqmp

def EqFun {Grade:Nat→ Type _}(n:Nat) (m:Nat) (f:Grade n→ Y) (g:Grade m→ Y): Prop:= @EqGrade (fun n=> Grade n→ Y) n m f g

theorem EqFun_rfl {Grade:Nat→ Type _}(n:Nat)  (f:Grade n→ Y) :EqFun n n f f:=by
  apply EqGrade_rfl

example {Grade:Nat→ Type _}:(n:Nat)→ (m:Nat)→ (f:Grade n→ Y)→ (g:Grade m→ Y)→ EqFun n m f g→ n=m:=by
  intro n m f g eq
  induction' eq with _
  exact rfl




def leq_set (n:Nat) :Set X:= {x| Len x≤ n}

def le_set (n:Nat) :Set X:= {x| Len x< n}

def eq_set (n:Nat) : Set X:={x| Len x = n}

structure Slice_ (Len: X→ Nat) (n:Nat) where
  val:X
  eq: Len val = n

def EqSlice {Len:X→ Nat} {n m:Nat} (x :Slice_ Len n)(y:Slice_  Len m):Prop :=@EqGrade (fun n=> Slice_ Len n) n m x y

@[simp]
theorem EqSlice_rfl {Len:X→ Nat}{n :Nat}(P:Slice_ Len n):EqSlice P P:=by
  rw[EqSlice]
  exact EqGrade.rfl n P

@[simp]
theorem EqSlice_symm {Len:X→ Nat}{n m:Nat}(P:Slice_ Len n)(Q:Slice_ Len m):EqSlice P Q ↔ EqSlice Q P:=by

  --rw[EqSlice]
  --rw[EqSlice]
  exact EqGrade_symm n m P Q

@[simp]
theorem EqSlice_trans {Len:X→ Nat}{n m p:Nat}(P:Slice_ Len n)(Q: Slice_ Len m)(R:Slice_ Len p):EqSlice P Q→ EqSlice Q R→ EqSlice P R:=by
  exact EqGrade_trans n m p P Q R



def leq_fun (u:X → Y)(n:Nat):@leq_set X Len n → Y:=by
  rintro ⟨x, _ ⟩
  exact u x

def le_fun (u:X → Y)(n:Nat):@le_set X Len n → Y:=by
  rintro ⟨x, _ ⟩
  exact u x

def eq_fun (u:X → Y)(n:Nat):@eq_set X Len n → Y:=by
  rintro ⟨x, _ ⟩
  exact u x

def FunSlice (Len:X→ Nat)(n:Nat)(u:X→ Y):(Slice_ Len n) → Y :=by
  intro ⟨x, _ ⟩
  exact u x

def EqFunSlice {Len:X→ Nat}{n m:Nat}(f :Slice_ Len n → Y)(g:Slice_ Len m→ Y):Prop := EqFun n m  f g

theorem EqFunSlice_ext {Len:X→ Nat}{n m:Nat}(f :Slice_ Len n → Y)(g:Slice_ Len m→ Y):(n=m)→ (∀ x:Slice_ Len n,∀  y:Slice_ Len m, EqGrade n m x y→ @EqGrade (fun n:Nat=> (Y:Type u)) n m (f x) (g y))→ EqFun n m f g:=by
  intro eqnm h
  rw[EqFun]
  induction' eqnm with h
  apply EqGrade_ext
  rw[Trans]
  simp
  ext x
  specialize h x x (EqGrade.rfl n x)

  sorry
  rfl

theorem EqFunSlice_if (Len:X→ Nat)(n m:Nat)(u v:X→ Y):(n=m)→ (u=v)→ EqFun n m (FunSlice Len n u) (FunSlice Len m v):=by
  intro eqnm equv

  rw[eqnm]
  rw[equv]
  apply EqFun_rfl

-- theorem st_eq (Len:X→ Nat)(st:(n:Nat)→ (Slice_ Len n→ Y))(n m:Nat)(x:Slice_ Len n)(y:Slice_ Len m):(n=m)→ (EqSlice x y)→  (EqFun n m (st n) (st m))→ (@EqFun (fun n=> Y) n m (st n x) (st m y)):=by
--   intro eqnm eqxy

--   sorry


def Build (Len:X→ Nat)(st:(n:Nat)→ (Slice_ Len n→ Y)):X→ Y:=by
  intro x
  exact st (Len x) ⟨x, rfl ⟩

theorem Build_n (Len:X→ Nat)(st:(m:Nat)→ (Slice_ Len m→ Y))(n:Nat):EqFun n n  (FunSlice Len n (Build Len st))  (st n):=by
  rw[EqFun]

  apply EqFunSlice_ext
  simp
  intro x y eqxy
  rw[FunSlice]
  simp
  rw[Build]


  sorry


variable (bc: eq_set Len 0→ Y)
variable (ih:∀ (m:Nat), (eq_set Len m→ Y)→ eq_set Len (succ m)→ Y)



def Induct_help (n:Nat):eq_set Len n→ Y:=by
  induction' n with n hn
  case  zero=>
    exact bc
  case succ=>
    --specialize hn bc ih
    specialize ih (n) hn
    exact ih

theorem Induct_help0 :(@Induct_help X Y Len bc ih) 0 = bc:=by
  rw[Induct_help]
  simp only [rec_zero]


def build (h:(n:Nat)→ (eq_set Len n→ Y))(x:X):  Y:=by

  exact h (Len x) ⟨x,rfl ⟩

theorem buildn (h:(n:Nat)→ (eq_set Len n→ Y))(n:Nat)(x:X)(hx:x∈ eq_set Len n):@build X Y Len h x = h n ⟨x,hx ⟩ := by
  rw[build]
  --have hx:Len x =n:=by exact
  rw [eq_set] at hx
  --rw [hx]
  induction' hx
  simp


def Induct : X→ Y:=by
  intro  x
  exact @Induct_help X Y Len bc ih (Len x)  ⟨x,rfl ⟩


theorem hhh (x:X)(hx:Len x =0):@Induct X Y Len bc ih x = @Induct_help X Y Len bc ih (0)  ⟨x,hx ⟩:=by
  rw[Induct]
  rw[Induct_help]
  sorry
  -- induction hx
  -- rw[hx]
  -- sorry

theorem Induct0 (x:X)(hx:Len x =0): (@Induct X Y Len bc ih) x = bc ⟨x, hx ⟩ :=by
  rw[Induct]
  sorry
  -- induction hx
  -- rw  [ hx]
  -- sorry

end UsualInduction

end Nat
