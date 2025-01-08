import Lake
open Lake DSL

package «Symm» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «Symm» where
  -- add any library configuration options here

--@[default_target]
lean_lib «DashedMonoids» where

lean_lib DashedMonoids.Basic
lean_lib DashedMonoids.Interval

@[default_target]
lean_lib «FreeDMon» where

lean_lib FreeDMon.as_inudctive
lean_lib FreeDMon.TypeC_inductive
lean_lib FreeDMon.list_prop

lean_lib «Suppliments» where

lean_lib Suppliments.list_prop
lean_lib Suppliments.Interval
