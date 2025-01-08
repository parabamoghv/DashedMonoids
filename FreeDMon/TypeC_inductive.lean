import Mathlib
--import DashedMonoids.ListProp
--import DashedMonoids.StrongInduction
import FreeDMon.as_inductive
--open Finset
set_option autoImplicit false
set_option maxHeartbeats 0


#check List.reverse
#check Nat
#eval 1+1


inductive TypeC (S:Type _)
  | base_I : TypeC S
  | cons_S (head:S) (tail:TypeC S) : TypeC S
  | cons_DashS (head:S) (kp:Nat) (tail:TypeC S) : TypeC S

namespace TypeC

def TypeC_aux (S:Type _):= List (S× Nat)

def toFun_aux {S:Type _} : TypeC S → TypeC_aux S := by
    intro x
    match x with
    | base_I => exact []
    | cons_S head tail => exact (head, 0) :: toFun_aux (tail)
    | cons_DashS head kp tail => exact (head, kp+1) :: toFun_aux (tail)


def invFun_aux {S: Type _} : TypeC_aux S → TypeC S:= by
    intro x
    match x with
    | [] => exact base_I
    | (head, k)::L =>
        match k with
        | 0 =>
            exact cons_S head (invFun_aux (L))
        | n+1 =>
            exact cons_DashS head n (invFun_aux (L))


theorem left_inv {S:Type _} : ∀ x: TypeC S, invFun_aux (toFun_aux (x)) = x:= by
    intro x
    match x with
    | base_I =>
        rw[toFun_aux]
        rw[invFun_aux]
    | cons_S head tail =>
        rw[toFun_aux]
        rw[invFun_aux]
        simp
        rw[left_inv]

    | cons_DashS head kp tail =>
        rw[toFun_aux]
        rw[invFun_aux]
        simp
        rw[left_inv]


theorem right_inv {S:Type _} : ∀ x: TypeC_aux S, toFun_aux (invFun_aux (x)) = x:= by
    intro x
    match x with
    | [] =>
        rw[invFun_aux]
        rw[toFun_aux]

    | (head, n)::L =>
        match n with
        | 0 =>
            rw[invFun_aux]
            rw[toFun_aux]
            rw[right_inv]

        | k+1 =>
            rw[invFun_aux]
            rw[toFun_aux]
            simp
            rw[right_inv]

--Need to define mul and swap

--def TypeC {S:Type _}:= List (S× Nat)

def mul {S:Type _}:TypeC S → TypeC S → TypeC S:= by
    intro x y
    match x with
    | base_I =>
        exact y
    | cons_S head tail =>
        exact cons_S (head) (mul tail y)
    | cons_DashS head kp tail =>
        exact cons_DashS (head) (kp) (mul tail y)


def swap {S:Type _} : TypeC S → TypeC S := by
    intro x
    match x with
    | base_I =>
        exact base_I
    | cons_S head tail =>
        exact mul (tail) (cons_S head base_I)
    | cons_DashS head kp tail =>
        exact mul (tail) (cons_DashS head kp base_I)


def incTypeC {S:Type _}: TypeC S  →  (FDMon S):= by
  intro x
  match x with
  | base_I =>
    exact FDMon.I
  | cons_S head tail =>
    exact FDMon.mul (FDMon.incS head) (incTypeC tail)
  | cons_DashS head kp tail =>
    exact FDMon.mul (FDMon.incDashS (DashS.base head kp)) (incTypeC tail)

def projTypeC {S:Type _} : (FDMon S) → (TypeC S):= by
  intro x
  match x with
  | FDMon.I =>
      exact base_I
  | FDMon.incS  (a: S) =>
      exact cons_S a (base_I)
  | FDMon.incDashS (y: DashS S) =>
      match y with
      | DashS.base a k=>
          exact cons_DashS a k base_I

  | FDMon.incDashMulG  (y: DashMulG S) =>
      match y with
      | DashMulG.cons_MulS a kp =>
          match kp with
          | 0 =>
              exact  swap (projTypeC (FDMon.incMulS (a))) --take swap


          | n+1 =>
              exact  swap (projTypeC (FDMon.incDashMulG (DashMulG.cons_MulS (a) (n)))) --Take swap

      | DashMulG.cons_EMulDashH a kp =>
          match kp with
          | 0 =>
              exact swap (projTypeC (FDMon.incEMulDashH (a))) --take swap
          | n+1 =>
              exact swap (projTypeC (FDMon.incDashMulG (DashMulG.cons_EMulDashH (a) (n)))) --Take swap


  | FDMon.incMulS  (y: MulS S) =>
    match y with
    | MulS.base a b =>
      exact cons_S a (cons_S (b) (base_I))
    | MulS.cons a L =>
      exact cons_S a (projTypeC (FDMon.incMulS L))

  | FDMon.incEMulDashH  (y: EMulDashH S) =>

    sorry


end TypeC



-- inductive TypeB (S:Type _)
--   | base_I : TypeB S
--   | cons_S (head:S) (tail:TypeB S) : TypeB S  -- head is a
--   | cons_DashS (head:S)  (tail:TypeB S) : TypeB S -- head is a'

def TypeB (S:Type _) := List (S× Bool)

namespace TypeB

-- def incTypeB_to_TypeC {S:Type _} : TypeB S → TypeC S := by
--   intro x
--   match x with
--   | base_I => exact TypeC.base_I
--   | cons_S a y =>
--       exact TypeC.cons_S a (incTypeB_to_TypeC (y))
--   | cons_DashS a y =>
--       exact TypeC.cons_DashS (a) (0) (incTypeB_to_TypeC (y))


#check FreeGroup

def incTypeB_to_TypeC {S:Type} : TypeB S → TypeC S := by
    intro x
    match x with
    | [] => exact TypeC.base_I
    | (a, sgn)::L =>
        match sgn with
        | true =>
            exact TypeC.cons_S a (incTypeB_to_TypeC (L))

        | false =>
            exact TypeC.cons_DashS a 0 (incTypeB_to_TypeC (L))

end TypeB
