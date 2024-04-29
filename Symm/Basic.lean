import Mathlib
--open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

variable {S: Type _}

variable {i n m: Nat}


--range n = {0, 1, ⋯ , n-1}
@[simp]
def range (n:Nat) := Finset.range n

-- Closed Open
@[simp]
def Ico (n m:Nat) := Finset.Ico n m

-- Open Open
@[simp]
def Ioo (n m:Nat) := Finset.Ioo n m

-- Open Closed
@[simp]
def Ioc (n m:Nat) := Finset.Ioc n m

-- Closed Closed
@[simp]
def Icc (n m:Nat) := Finset.Icc n m



@[simp]
theorem mem_range : i∈ range n ↔ i<n := by
  simp only [range, Finset.mem_range]

@[simp]
theorem mem_Icc : i ∈ Icc n m ↔ n ≤ i ∧ i ≤ m :=
  LocallyFiniteOrder.finset_mem_Icc n m i

@[simp]
theorem mem_Ico : i ∈ Ico n m ↔ n ≤ i ∧ i < m :=
  LocallyFiniteOrder.finset_mem_Ico n m i

@[simp]
theorem mem_Ioc : i ∈ Ioc n m ↔ n < i ∧ i ≤ m :=
  LocallyFiniteOrder.finset_mem_Ioc n m i

@[simp]
theorem mem_Ioo : i ∈ Ioo n m ↔ n < i ∧ i < m :=
  LocallyFiniteOrder.finset_mem_Ioo n m i

--Useful to create macro <<h: i<n>> : range n
def range_mem1 (hn: i<n):range n:= by
  use i
  simp only [mem_range]
  --rw[range]
  --rw[Finset.mem_range]
  --simp only [mem_range]
  exact hn

--end Word



notation:1000 "<<" le:1000 ">>" => range_mem1 le


def eqTransLe (eqnm:n=m)(hn:i< n):(i < m):=by
  rw[← eqnm]
  exact hn


--EqTrans: n=m and i<n then i in range m

def eqTrans  (eqnm: n=m)(hn:i< n):range m:=
  by
  exact << (eqTransLe eqnm hn) >>
  --exact range_mem (eqTransProp eqnm hn)
  --constructor
  --case mk.val =>
  --  exact i
  --case mk.property =>
    --exact eqTransProp eqnm hn

notation:1000 "<<" eq:1000 "," a:1000 ">>" => eqTrans eq a


def eqTransWord (eqnm: m=n)(u: range n→ S):range m → S:= by
  intro a
  rcases a with ⟨i, hn ⟩
  simp only [mem_range] at hn
  exact  u (<< (eqnm), hn>>)

notation:1000 "<<" eqnm:1000 "," u:1000 ">>" => eqTransWord eqnm u



def Lsplit (n_pos:n>0)(u:range n→ S):  (S)× (range (n-1)→ S):=by
  constructor
  exact u (<<n_pos>>)
  intro ⟨i, hn ⟩
  simp only [range, ge_iff_le, Finset.mem_range] at hn
  have h: i+1<n:= by
    exact Nat.add_lt_of_lt_sub hn
  exact u (<<h>>)

def Lsplit1 (n_pos:n>0)(u:range n→ S): range 1→ S:= by
  intro
  exact u (<<n_pos>>)

def Lsplit2 (n_pos:n>0)(u:range n→ S): range (n-1)→ S:= by
  intro ⟨i, hn ⟩
  simp only [range, ge_iff_le, Finset.mem_range] at hn
  have h: i+1<n:= by
    exact Nat.add_lt_of_lt_sub hn
  exact u (<<h>>)

def Rsplit (n_pos:n>0)(u:range n→ S):  (range (n-1)→ S)× S:=by
  constructor
  intro ⟨i, hn ⟩
  simp only [range, ge_iff_le, Finset.mem_range] at hn
  have h: i<n:= by
    exact Nat.lt_of_lt_pred hn
  exact u (<<h>>)
  have h:n-1<n:= by
    refine Nat.sub_lt n_pos ?_
    exact Nat.one_pos
  exact u (<<h>>)

def Rsplit1 (n_pos:n>0)(u:range n→ S): range (n-1)→ S:=  (Rsplit n_pos u).1

def Rsplit2 (n_pos:n>0)(u:range n→ S): range (1)→ S:= by
  intro
  exact (Rsplit n_pos u).2



def mulWord (u: range n→ S)(v:range m→ S):range (n+m)→ S:= by
  rintro ⟨ i, hnm⟩
  simp only [mem_range] at hnm
  if hn:i< n then
    exact u (<< hn>>)
  else
    have todoprop: i-n< m:= by
      linarith[Nat.sub_add_cancel (Nat.not_lt.mp hn)]
    exact v (<< todoprop>>) --<< todoprop>> = ⟨i-n, todoprop ⟩

example (n_pos:n>0):1+(n-1)=n:= Nat.add_sub_of_le n_pos


theorem mulWordEq {n m p i: Nat}(hip:i<p)(nmpeq: n+m=p)(u:range n→ S)(v:range m→ S)(w:range p→ S)(hiu:(h1:i<n) → u (<<h1>>)=w (<<hip>>))(hiv: (h2:i-n<m)→ v (<<h2>>)=w (<<hip>>)) : (mulWord u v) = (<<nmpeq, w>>):= by

  sorry


-- theorem Lsplit_mul (n_pos:n>0)(u:range n→ S):mulFun (Lsplit1 n_pos u) (Lsplit2 n_pos u) = <<(Nat.add_sub_of_le n_pos).symm
-- , u>>:= by
--   ext ⟨ i, hi⟩
--   by_cases h:i=0
--   rw[mulFun]
--   simp only [h, zero_lt_one, ge_iff_le, zero_le, tsub_eq_zero_of_le, dite_true, range]
--   --rw[Lsplit1]
--   rfl
--   rw[mulFun]
--   simp[h]
--   rw[Lsplit2]
--   simp
--   sorry
--   sorry
