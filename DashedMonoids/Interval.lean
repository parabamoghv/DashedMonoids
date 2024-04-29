import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0

universe u v w


variable {S: Type u}

variable {i n m p q: Nat}

namespace Interval

#check min n m
#check max n m

--This is necessary in defining L (head Bracketing). This needs understanding of multiset.
class Interval_as_finset (n:Nat) where
  Interval: Finset Nat
  sub_n: Interval.max ≤ n
  min_1: 1≤ Interval.min
  is_interval:∀ a b:Interval, (∀  i:Nat, a≤ i→ i≤ b → i∈ Interval)

class IntervalP_as_finset (n:Nat) where
  Interval: Finset Nat
  non_empty: ∃ x:Nat, x∈ Interval
  sub_n:Interval.max' non_empty ≤ n
  min_1:1≤ Interval.min' non_empty
  is_interval: ∀ a b:Interval, (∀ i:Nat, a≤ i→ i≤ b→ i∈ Interval)


example (Interval:Finset Nat):Finset Nat:=by
  rcases Interval with ⟨A, hA ⟩
  constructor
  case val=>
    sorry--m+A
  case nodup=>
    sorry
--Interval is an finite open closed sub-interval of {1, 2, ..., n} where start is the start point and end is the end point.
--(Start, End]⊆ [n]
class Interval (n:Nat) where
  Start:Nat
  End:Nat
  leq:Start≤ End
  sub_n:End≤ n

--IntervalP is not empty sub-intervals of [n]
@[ext]
class IntervalP (n:Nat) where
  Start:Nat
  End:Nat
  le:Start<End
  sub_n:End≤ n

--{i+1} as an interval of [n]
example (i:Nat)(le:i<n):IntervalP n where
  Start:=i
  End := i+1
  le:=by linarith
  sub_n:=by linarith

--For traditional equality we have case one type onto another. We define our own definition of equaliy with all the properties shown
structure IntervalP_Eq (A:IntervalP n)(B:IntervalP m):Prop where
  n_eq: n=m
  Start_eq: A.Start = B.Start
  End_eq: A.End = B.End

--Reflexive
theorem IntervalP_Eq_rfl {A:IntervalP n}:IntervalP_Eq A A:=by
  constructor
  case n_eq=>
    exact rfl
  case Start_eq=>
    exact rfl
  case End_eq =>
    exact rfl

--symmetry
theorem IntervalP_Eq_symm {A:IntervalP n}{B:IntervalP m}:IntervalP_Eq A B → IntervalP_Eq B A:= by
  intro h
  rcases h with ⟨hn, hStart, hEnd ⟩
  constructor
  case n_eq=>
    exact hn.symm
  case Start_eq=>
    exact hStart.symm
  case End_eq=>
    exact hEnd.symm


--transitivity
theorem IntervalP_Eq_trans {A:IntervalP n}{B:IntervalP m}{C:IntervalP p}:(IntervalP_Eq A B)→  (IntervalP_Eq B C)→ IntervalP_Eq A C:=by
  intro Left Right
  rcases Left with ⟨eqnm, eqABStart, eqABEnd⟩
  rcases Right with ⟨eqmp, eqBCStart, eqBCEnd⟩
  constructor
  case n_eq=>
    rw[eqnm]
    exact eqmp
  case Start_eq=>
    rw[eqABStart]
    exact eqBCStart
  case End_eq=>
    rw[eqABEnd]
    exact eqBCEnd


--Defines subsets in intervalP
instance :HasSubset (IntervalP n) where
  Subset:= by
    intro A B
    exact B.Start≤ A.Start ∧ A.End ≤ B.End



theorem subset_self (A:IntervalP n):A⊆ A:= by
  constructor
  case left=> rfl
  case right=> rfl

--Empty Intersection
def Disjoint (A B:IntervalP n):=(A.End≤ B.Start) ∨ (B.End≤ A.Start)


theorem Disjoint_comm {A B:IntervalP n}:(p:Disjoint A B)→ (Disjoint B A):=by
  --rw[EmptyInter]
  --rw[EmptyInter] at p
  intro p
  rcases p
  case inl h=>
    right
    exact h
  case inr h=>
    left
    exact h

-- class Inter (α : Type u) where
--   /-- `a ∩ b` is the intersection of`a` and `b`. -/
--   inter : α → α → α
-- /-- `a ∩ b` is the intersection of`a` and `b`. -/
-- infixl:70 " ∩ " => Inter.inter

end Interval

namespace BrSet

open Interval


--BrSet is a collection of subsets of IntervalP n
--BrSet n:= Set (IntervalP n)

--Equality for subsets of IntervalP
structure BrSet_Eq (D:Set (IntervalP n))(E:Set (IntervalP m)):Prop where
  D_Sub_E:∀ L:D, ∃ R:E, IntervalP_Eq L.1 R.1
  E_Sub_D:∀ R:E, ∃ L:D, IntervalP_Eq R.1 L.1

--refl
theorem BrSet_Eq_rfl {D:Set (IntervalP n)}:BrSet_Eq D D:= by
  constructor
  case D_Sub_E=>
    intro L
    use L
    exact (IntervalP_Eq_rfl )
  case E_Sub_D=>
    intro R
    use R
    exact IntervalP_Eq_rfl


--Symmetry
theorem BrSet_Eq_symm {D:Set (IntervalP n)}{E:Set (IntervalP m)}:BrSet_Eq D E → BrSet_Eq E D:=by
  intro h
  rcases h with ⟨ DSub, ESub⟩
  constructor
  case D_Sub_E=>
    exact ESub
  case E_Sub_D=>
    exact DSub

--Transitivity
theorem BrSet_Eq_trans {D:Set (IntervalP n)}{E:Set (IntervalP m)}{F:Set (IntervalP p)}:BrSet_Eq D E → BrSet_Eq E F→ BrSet_Eq D F:=by
  intro Left Right
  rcases Left with ⟨DSubE, ESubD ⟩
  rcases Right with ⟨ESubF, FSubE ⟩
  constructor
  case D_Sub_E=>
    intro LD
    specialize DSubE LD
    rcases DSubE with ⟨ LE  ,hLE⟩
    specialize ESubF LE
    rcases ESubF with ⟨LF, hLF ⟩
    use LF
    exact IntervalP_Eq_trans hLE hLF

  case E_Sub_D=>
    intro RF
    specialize FSubE RF
    rcases FSubE with ⟨ RE  ,hRE⟩
    specialize ESubD RE
    rcases ESubD with ⟨RD, hRD ⟩
    use RD
    exact IntervalP_Eq_trans hRE hRD

end BrSet

namespace Br

open Interval
open BrSet

--Br n is the collection of bracketings on n
class Br (n:Nat) where
  Bracket:Set (IntervalP n) --BrSet
  BrCond: ∀ A B: Bracket, Disjoint A.1 B.1 ∨ A.1⊆ B.1 ∨ B.1⊆ A.1 --Bracketing condition


structure Br_Eq (D:Br n)(E:Br m):Prop where
  eqnm: n=m
  eqBrSet: BrSet_Eq D.Bracket E.Bracket

theorem Br_Eq_rfl {D:Br n}:Br_Eq D D:= by
  constructor
  case eqnm=>
    rfl
  case eqBrSet=>
    exact BrSet_Eq_rfl

theorem Br_Eq_symm {D:Br n}{E:Br m}:Br_Eq D E → Br_Eq E D:= by
  rintro ⟨eqnm,eqDE ⟩
  constructor
  case eqnm=>
    exact eqnm.symm
  case eqBrSet=>
    exact BrSet_Eq_symm eqDE

theorem Br_Eq_trans {D:Br n}{E:Br m}{F:Br p}:Br_Eq D E → Br_Eq E F→ Br_Eq D F:= by
  rintro ⟨eqnm, eqDE ⟩  ⟨eqmp, eqEF ⟩
  constructor
  case eqnm=>
    rw[eqnm]
    exact eqmp
  case eqBrSet=>
    exact BrSet_Eq_trans eqDE eqEF

--An example of bracketing on n letters
def Range (n:Nat):Interval n where
  Start:=0
  End :=n
  leq:= by
    simp only [zero_le]
  sub_n:=by
    simp only [le_refl]

def RangeP (n:Nat)(n_pos:n>0):IntervalP n where
  Start:= 0
  End:= n
  le:=by exact n_pos
  sub_n:=by simp only [le_refl]



def BrRangePSet (n:Nat)(n_pos:n>0):Set (IntervalP n):={RangeP n n_pos}

theorem BrRangePSet_iff (n_pos:n>0)(A:BrRangePSet n n_pos):A=RangeP n n_pos:=by
  --dsimp[BrRangePSet] at A
  exact A.2


def BrRangeP (n:Nat)(n_pos:n>0):Br n where
  Bracket:= BrRangePSet n n_pos
  BrCond:= by
    intro A B
    right
    left
    have hA:=BrRangePSet_iff n_pos A
    have hB:=BrRangePSet_iff n_pos B
    rw[hB]
    rw[← hA]
    exact subset_self A.1

--BrSet_Empty of n
def BrSet_Empty (n:Nat): Set (IntervalP n):= ∅


--Empty D of [n]
def BrEmpty (n:Nat): Br n where
  Bracket:=∅
  BrCond:= by
    intro A B
    have h:=A.2
    exact h.elim

--unit=Empty D of [0]
def I_Br : Br 0 :=BrEmpty 0

--Empty D of [n=0] is unit
theorem BrEmpty_eq_I_Br  : Br_Eq (BrEmpty 0) I_Br:= by
  constructor
  case eqBrSet =>
    --exact BrSet_Eq_rfl
    constructor
    case D_Sub_E =>
      intro h
      exact h.2.elim
    case E_Sub_D =>
      intro h
      exact h.2.elim
  case eqnm=>
    rfl


end Br

namespace Interval
--Here we define shifts of Interval
open Interval
--open BrSet
--open Br
-----------------------------------------------------
----------------------------------------------------
------Work on Multiplication in bracketing----------

--If L is an intervalP n then L+m is an IntervalP n+m which is basically L viewd as interval in n+m
def IntervalP_Add (L:IntervalP n) (m:Nat):IntervalP (n+m) where
  Start:=L.Start
  End:=L.End
  le:=L.le
  sub_n:= by
    have h:L.End≤ n:=L.sub_n
    linarith


--L+0=L
theorem IntervalP_Add_zero: ∀  {L:IntervalP n},IntervalP_Eq (IntervalP_Add L 0) L:=by
  intro L
  constructor
  case n_eq=>
    exact Nat.add_zero n
  case Start_eq=>
    exact Nat.add_zero L.Start
  case End_eq=>
    exact Nat.add_zero L.End

--Interval L+m is less than n
theorem IntervalP_Add_leq:∀  (L:IntervalP n) (m:Nat),(IntervalP_Add L m).End≤ n:=by
  intro L _
  exact L.sub_n

--If L R are disjoint then so is L+m and R+m
theorem IntervalP_Add_Disjoint:∀  (L R:IntervalP n)(m:Nat),(h:Disjoint L R)→ Disjoint (IntervalP_Add L m) (IntervalP_Add R m):= by
  intro L R m h
  rcases h with (hl|hr)
  case inl=>
    left
    exact hl
  case inr=>
    right
    exact hr

--L ⊆ R implies L+m⊆ R+m
theorem IntervalP_Add_Sub: ∀ (L R: IntervalP n)(m:Nat), (h:L ⊆ R)→ (IntervalP_Add L m)⊆ (IntervalP_Add R m):= by
  rintro ⟨LSt, LEnd, _, _⟩  ⟨RSt, REnd, _,_ ⟩  m ⟨ LSubRSt, LSubREnd⟩
  rw[IntervalP_Add]
  rw[IntervalP_Add]
  simp
  simp at LSubRSt
  simp at LSubREnd
  constructor
  case left=>
    simp
    exact LSubRSt
  case right=>
    simp
    exact LSubREnd




--n+L is an interval in n+m which is shifted by n
def Add_IntervalP (n:Nat) (L:IntervalP m):IntervalP (n+m) where
  Start:=n+L.Start
  End:=n+L.End
  le:=by linarith[L.le]
  sub_n:= by
    have h:L.End≤ m:=L.sub_n
    linarith

--0+L=L
theorem zero_Add_IntervalP: ∀  (L:IntervalP n),IntervalP_Eq (Add_IntervalP 0 L) L:=by
  intro L
  constructor
  case n_eq=>
    exact Nat.zero_add n
  case Start_eq=>
    exact Nat.zero_add L.Start
  case End_eq=>
    exact Nat.zero_add L.End

--Interval n+L is bigger than n
theorem Add_IntervalP_geq: ∀  (n:Nat)(L:IntervalP m) ,(Add_IntervalP n L).Start≥  n:=by
  intro n L
  simp only [Add_IntervalP, ge_iff_le, le_add_iff_nonneg_right, zero_le]

--If L R are disjoint then so is n+L and n+R
theorem Add_IntervalP_Disjoint:∀ (n:Nat) (L R:IntervalP m),(h:Disjoint L R)→ Disjoint (Add_IntervalP n L) (Add_IntervalP n R):= by
  rintro n ⟨ LSt, LEnd, _ ,_⟩  ⟨RSt, REnd,_,_ ⟩  h
  rcases h with (hl|hr)
  case inl=>
    left
    simp at hl
    rw[Add_IntervalP]
    rw[Add_IntervalP]
    simp only [add_le_add_iff_left]
    exact hl
  case inr=>
    right
    simp at hr
    rw[Add_IntervalP]
    rw[Add_IntervalP]
    simp only [add_le_add_iff_left]
    exact hr

theorem Add_IntervalP_Sub:∀ (n:Nat) (L R:IntervalP m), (h:L ⊆ R)→ (Add_IntervalP n L)⊆ (Add_IntervalP n R):=by
  rintro n ⟨LSt, LEnd, _,_ ⟩ ⟨RSt, REnd, _,_ ⟩ ⟨ LSubRSt, LSubREnd⟩
  simp at LSubRSt
  simp at LSubREnd
  rw[Add_IntervalP]
  rw[Add_IntervalP]
  constructor
  case left=>
    simp only [add_le_add_iff_left]
    exact LSubRSt
  case right=>
    simp only [add_le_add_iff_left]
    exact LSubREnd

end Interval


namespace BrSet
open Interval
open Br

--D+m is D seen as subsets of n+m
def BrSet_Add (D:Set (IntervalP n))(m:Nat):Set (IntervalP (n+m)):= by
  intro M
  exact ∃ L:D, IntervalP_Add L.1 m = M

--D+0 = D
theorem BrSet_Add_zero :∀ (D: Set (IntervalP n)),BrSet_Eq (BrSet_Add D 0) D:= by
  intro D
  constructor
  case D_Sub_E=>
    rintro ⟨L, ⟨A,hAL ⟩  ⟩
    use A
    simp
    rw[← hAL]
    exact IntervalP_Add_zero
  case E_Sub_D=>
    rintro R
    --have R2:BrSet_Add D 0:=⟨(IntervalP_Add R.1 0), ⟨R, rfl ⟩  ⟩
    --have R1:BrSet_Add D 0:= by
    --  constructor
      -- case val=>
      --   exact (IntervalP_Add R.1 0)
      -- case property=>
      --   --simp only [Nat.add_zero]
      --   use R
    use ⟨(IntervalP_Add R.1 0), ⟨R, rfl ⟩  ⟩
    simp
    have h:IntervalP_Eq (IntervalP_Add R.1 0) R.1:= IntervalP_Add_zero
    have g:=  IntervalP_Eq_symm  h
    exact g

--Empty(n) + m =Empty(n+m)
theorem Empty_Add_BrSet {n m:Nat}:BrSet_Eq (BrSet_Add (BrSet_Empty n) m) (BrSet_Empty (n+m)):= by
  constructor
  case D_Sub_E=>
    rintro ⟨L,⟨⟨a,ha ⟩ , hAL ⟩  ⟩
    exact ha.elim
  case E_Sub_D=>
    rintro ⟨B, hB ⟩
    exact hB.elim

--Every A in D+m is less than n
theorem BrSet_Add_leq {D:Set (IntervalP n)}{m:Nat}:∀ A:(BrSet_Add D m), A.1.End≤ n:= by
  rintro ⟨⟨AStart, AEnd, ALe, Asubn⟩ , hA ⟩
  simp
  rcases hA with ⟨⟨L , LD⟩ , hL ⟩
  simp at hL
  have h:L.End≤ n:= IntervalP_Add_leq L m
  rcases L with ⟨LStart, LEnd, LLe, Lsubn⟩
  have h1:LEnd=AEnd:=by
    rw[IntervalP_Add] at hL
    simp at hL
    rcases hL
    exact rfl
  rw[← h1]
  exact h

--Every L R: D, if L disjoint R then L+m Disjoint R+m
theorem BrSet_Add_EmptyInter {D:Set (IntervalP n)}{m:Nat}:∀ (L R:D),(h: Disjoint L.1 R.1)→  Disjoint (IntervalP_Add L.1 m) (IntervalP_Add R.1 m):=by
  intro L R
  exact IntervalP_Add_Disjoint L.1 R.1 m




--n+D is shifted intervals
def Add_BrSet (n:Nat)(D:Set (IntervalP m)):Set (IntervalP (n+m)):= by
  intro M
  exact ∃ L:D, Add_IntervalP n L.1 = M


--0+D = D
theorem zero_Add_BrSet:∀  (E:Set (IntervalP m)),BrSet_Eq (Add_BrSet 0 E) E:= by
  intro E
  constructor
  case D_Sub_E=>
    rintro ⟨L,⟨A, hAL ⟩  ⟩
    use A
    simp
    rw[← hAL]
    apply zero_Add_IntervalP
  case E_Sub_D=>
    rintro R
    constructor
    case w=>
      constructor
      case val=>
        exact Add_IntervalP 0 R
      case property=>
        use R
    case h=>
      simp
      apply  IntervalP_Eq_symm
      apply zero_Add_IntervalP


--Every A in n+D is more than n
theorem Add_BrSet_geq (n:Nat)(D:Set (IntervalP m)):∀ A:(Add_BrSet n D), A.1.Start≥ n:= by
  rintro ⟨⟨AStart, AEnd, _, _ ⟩, hA    ⟩
  simp
  rcases hA with ⟨⟨⟨ LStart,LEnd, _ ,_⟩ ,_ ⟩, hL⟩
  simp at hL
  rw[Add_IntervalP] at hL
  simp at hL

  have h:AStart= n+LStart:=by
    rcases hL
    exact rfl
  rw[h]
  simp only [le_add_iff_nonneg_right, zero_le]

--Every L R: E, if L disjoint R then n+L Disjoint n+R
theorem Add_BrSet_EmptyInter {n:Nat}{E:Set (IntervalP m)}:∀ (L R:E),(h: Disjoint L.1 R.1)→  Disjoint (Add_IntervalP n L.1) (Add_IntervalP n R.1):=by
  intro L R
  exact Add_IntervalP_Disjoint n L.1 R.1


theorem BrSet_Eq_Union {D E F:Set (IntervalP n)}: (eqDE: BrSet_Eq D E)→ BrSet_Eq (D ∪  F) (E ∪  F):=by
  intro h
  rcases h with ⟨DSub, ESub ⟩
  constructor
  case D_Sub_E =>
    rintro ⟨ L, (L_D|L_F)⟩
    case inl =>
      specialize DSub ⟨ L, L_D⟩
      rcases DSub with ⟨A, hA ⟩
      constructor
      case w=>
        constructor
        case val=>
          exact A.1
        case property=>
          left
          exact A.2
      case h=>
        exact hA
    case inr =>
      constructor
      case w=>
        constructor
        case val=>
          exact L
        case property=>
          right
          exact L_F
      case h=>
        exact IntervalP_Eq_rfl
  case E_Sub_D =>
    rintro ⟨ L, (L_D|L_F)⟩
    case inr =>
      constructor
      case w=>
        constructor
        case val=>
          exact L
        case property=>
          right
          exact L_F
      case h=>
        exact IntervalP_Eq_rfl
    case inl =>
      specialize ESub ⟨ L, L_D⟩
      rcases ESub with ⟨A, hA ⟩
      constructor
      case w=>
        constructor
        case val=>
          exact A.1
        case property=>
          left
          exact A.2
      case h=>
        exact hA

theorem BrSet_Empty_Union {E: Set (IntervalP m)}:BrSet_Eq ((BrSet_Empty m) ∪ E) (E):= by
  constructor
  case D_Sub_E=>
    rintro ⟨L, (Em| inL) ⟩
    case inl=>
      exact Em.elim
    case inr=>
      use ⟨L, inL ⟩
      exact IntervalP_Eq_rfl
  case E_Sub_D =>
    rintro R
    constructor
    case w=>
      constructor
      case val=>
        exact R.1
      case property=>
        right
        exact R.2
    case h=>
      exact IntervalP_Eq_rfl


--D+n and n+E are disjoint
theorem BrSet_mul_Cond (D:Set (IntervalP n))(E: Set (IntervalP m))(A:BrSet_Add D m)(B:Add_BrSet n E):Disjoint A.1 B.1:= by
  --constructor
  left
  have h1:=BrSet_Add_leq A
  have h2:=Add_BrSet_geq n E B
  linarith




theorem BrSet_mul_CondLeft (D:Br n)(A B:BrSet_Add D.1 m):Disjoint A.1 B.1 ∨ A.1⊆ B.1 ∨ B.1⊆ A.1:= by
  rcases A.2 with ⟨L, hAL ⟩
  rcases B.2 with ⟨R, hBR ⟩
  rcases D.BrCond L R
  case inl EmptyLR=>
    left
    have h: Disjoint (IntervalP_Add L.1 m) (IntervalP_Add R.1 m):= BrSet_Add_EmptyInter L R EmptyLR
    rw[hAL] at h
    rw[hBR] at h
    exact h
  case inr SubOSub=>
    rcases SubOSub
    case inl h=>
      right
      left
      rw[ ← hAL]
      rw[← hBR]
      apply IntervalP_Add_Sub
      exact h
    case inr h=>
      right
      right
      rw[← hAL]
      rw[← hBR]
      apply IntervalP_Add_Sub
      exact h

theorem BrSet_mul_CondRight (D:Br m)(A B:Add_BrSet n D.1):Disjoint A.1 B.1 ∨ A.1⊆ B.1 ∨ B.1⊆ A.1:= by
  rcases A.2 with ⟨L, hAL ⟩
  rcases B.2 with ⟨R, hBR ⟩
  rcases D.BrCond L R
  case inl EmptyLR=>
    left
    have h: Disjoint (Add_IntervalP n L.1) (Add_IntervalP n R.1):= Add_BrSet_EmptyInter L R EmptyLR
    rw[hAL] at h
    rw[hBR] at h
    exact h
  case inr SubOSub=>
    rcases SubOSub
    case inl h=>
      right
      left
      rw[ ← hAL]
      rw[← hBR]
      apply Add_IntervalP_Sub
      exact h
    case inr h=>
      right
      right
      rw[← hAL]
      rw[← hBR]
      apply Add_IntervalP_Sub
      exact h



def mul (D:Br n)(E:Br m):Br (n+m) where
  Bracket:= (BrSet_Add D.Bracket m)∪ (Add_BrSet n E.Bracket)
  BrCond:= by
    rintro A B
    cases A.2
    case inl hA=>
      cases B.2
      case inl hB =>
        have h:= BrSet_mul_CondLeft D ⟨A.1, hA⟩ ⟨B.1, hB ⟩
        exact h
      case inr hB =>
        have h:= BrSet_mul_Cond D.1 E.1 ⟨ A.1, hA⟩ ⟨B.1, hB ⟩
        left
        exact h

    case inr hA=>
      cases B.2
      case inl hB=>
        have h:= BrSet_mul_Cond D.1 E.1 ⟨B.1, hB ⟩ ⟨A.1, hA ⟩
        left
        exact Disjoint_comm  h


      case inr hB=>
        have h:= BrSet_mul_CondRight E ⟨A.1, hA ⟩ ⟨B.1, hB ⟩
        exact h

instance: HMul (Br n) (Br m) (Br (n+m))  where
  hMul:= mul


theorem mul_BrSet (D:Br n)(E:Br m): (mul D E).Bracket = (BrSet_Add D.1 m)∪ (Add_BrSet n E.1):= by
  rfl


--I*E=E
theorem unit_mul (E:Br m):Br_Eq (mul I_Br E) E:=by
  constructor
  case eqnm=>
    exact Nat.zero_add m
  case eqBrSet=>
    have h1:BrSet_Eq (Add_BrSet 0 E.1) E.1:=zero_Add_BrSet E.1
    have h2:BrSet_Eq ((BrSet_Empty (0+m))∪ (Add_BrSet 0 E.1)) (Add_BrSet 0 E.1):= BrSet_Empty_Union
    have h3:BrSet_Eq ((BrSet_Add I_Br.1 m)∪ (Add_BrSet 0 E.1)) ((BrSet_Empty (0+m))∪ (Add_BrSet 0 E.1)):= by
      apply BrSet_Eq_Union
      exact Empty_Add_BrSet

    apply BrSet_Eq_trans h3
    apply BrSet_Eq_trans h2
    apply BrSet_Eq_trans h1
    exact BrSet_Eq_rfl














-----------------
--------------Trial
variable {α :Type _}[Lattice α]

#check Finset.max'

def hasMaxL (n_pos:1≤ n)(D:Set (Interval n)):∃ a:Nat, (∃ L:D, (L.1.Start=0)∧ (L.1.End=a))∧ (∀ L:D, L.1.Start=0→ L.1.End≤ a):= by
  sorry


def isMax (mx:Nat) (A:Finset Nat)(bound:∃ n:Nat, ∀ a∈ A, a≤ n):= mx∈ A ∧ ∀ a∈ A, a≤ mx

theorem help (a:Nat):(lesn:a≤ Nat.succ n)→ (nesn:a≠ Nat.succ n)→ a≤ n:=by sorry

noncomputable def Max (n:Nat):∀ (A:Set Nat),(bounded:∀ a:A, a≤ n)→ Nat:=
  match n with
  |0=>by
    intro A bounded
    exact 0
  |1=> by
    intro A _
    exact 0
  |n+1=>by
    intro A_sn bounded_sn
    if maxsn:Nat.succ n∈ A_sn then
      exact Nat.succ n
    else
      have A_n:∀ a:A_sn, a≤ n:= by
        intro a
        by_cases aeqsn: a=Nat.succ n
        case pos=>
          by_contra _
          apply maxsn
          rw[← aeqsn]
          exact a.2
        case neg=>
          apply help a (bounded_sn a) aeqsn
      exact Max n A_sn A_n



def Union {D:Set (Set Nat)}: Set Nat:= {x:Nat|∃ L:D, x∈ L.1 }

example  (g:({1}ᶜ: Set Nat) → Nat):  Nat → Nat  :=
  by
  intro x
  if hx: x=1 then
    exact 0
  else
    exact g ⟨x, hx⟩


--------------
--------------End trial
