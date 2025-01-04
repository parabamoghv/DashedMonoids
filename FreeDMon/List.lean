import Mathlib
-- import DashedMonoids.ListProp
-- import DashedMonoids.StrongInduction
--open Finset
set_option autoImplicit false
set_option maxHeartbeats 0


inductive EMPTY :Type _ where

def EMPTY_fun (A:Type _) : EMPTY → A := by
    intro h
    rcases h

def NOT (A:Type _) : Type _ := A → EMPTY

example :NOT Nat → EMPTY := by
    intro f
    exact f 0

example :EMPTY → NOT Nat := by

  intro x _
  exact x

example {A:Type _}: A → NOT (NOT A):= by
  intro a
  rw[NOT]
  intro f
  exact f a

example {A:Type _}: NOT (NOT EMPTY) → EMPTY := by
  intro f
  exact f (EMPTY_fun EMPTY)

example {A B:Type _} (f:A→ B) :NOT (B) → NOT A := by
    intro g a
    exact g (f (a))

inductive AND (A B :Type _) : Type _ where
  | intro (a : A) (b : B) : AND A B

inductive OR (A B: Type _) : Type _ where
  | inl (a : A) : OR A B
  | inr (b : B) : OR A B


example {A B:Type _}:  OR (NOT A) (NOT B) →  NOT (AND A B) := by
    intro f g
    match g with
    | AND.intro a b =>
        match f with
        | OR.inl a1 =>
            exact a1 a
        | OR.inr b1 =>
            exact b1 b
