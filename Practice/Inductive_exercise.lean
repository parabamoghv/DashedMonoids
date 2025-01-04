import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0


namespace Hidden
variable (α β γ: Type _)

inductive Option (α : Type _) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type _) where
  | mk : α → Inhabited α

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)


example (f:α→ Option β) (g: β→ Option γ):α → Option γ:= by
  intro x
  exact match (f x) with
  | Option.none => Option.none
  | Option.some y => g y

end Hidden

example : Inhabited Nat := Inhabited.mk Nat.zero

example : Inhabited Bool := Inhabited.mk Bool.true

namespace Hidden
inductive Prod (α : Type _) (β : Type _)
  | mk : α → β → Prod α β
def fst {α : Type _} {β : Type _} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type _} {β : Type _} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b
end Hidden

def swap {α : Type _} {β : Type _} (p : Prod α β) : Prod β α :=
  match p with
  | Prod.mk a b => Prod.mk b a



def isEven (n:Nat):=(n/2)*2=n

example: isEven 2:= by
  rw[isEven]



def isOdd (n:Nat):= ¬ isEven n

example : isOdd 3:= by
  rw[isOdd]
  intro h
  rw[isEven] at h
  --have h1: 3/2*2=2:= by exact rfl
  --rw[h1] at h
  contradiction

def col (n:Nat):Nat:=
  if (n/2)*2=n then
    n/2
  else
    3*n+1

def col1 (n: Nat):Nat:= by
  by_cases  (n/2)*2=n
  exact n/2
  exact 3*n+1

example: col1 6 = 3:= by
  rw[col1]
  apply ite_true 3 0

example: col1 5 = 16:= by
  rw[col1]
  apply ite_false 0 16


example: col (6)=3:= by
  rw[col]
  have h:isEven 6:=by rfl
  rw[h]
  apply ite_true 3 0



example: col (3)=10:=by
  rw[col]
  exact ite_false 1 10
