import Mathlib
import FreeDMon.Basic
--open Finset
set_option autoImplicit false
set_option maxHeartbeats 0


universe v u

namespace CategoryTheory

/-- Auxiliary structure to carry only the data fields of (and provide notation for)
`MonoidalCategory`. -/
class SSCatGrpStruct (C : Type u) [DMonStruct: DMon C] [𝒞 : Category.{v} C] where
  /-- curried tensor product of objects -/
  tensorObj : C → C → C := DMonStruct.mul
  /-- left whiskering for morphisms -/
  whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : tensorObj X Y₁ ⟶ tensorObj X Y₂
  /-- right whiskering for morphisms -/
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : tensorObj X₁ Y ⟶ tensorObj X₂ Y
  /-- Tensor product of identity maps is the identity: `(𝟙 X₁ ⊗ 𝟙 X₂) = 𝟙 (X₁ ⊗ X₂)` -/
  -- By default, it is defined in terms of whiskerings.
  tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
    whiskerRight f X₂ ≫ whiskerLeft Y₁ g
  /-- The tensor unity in the monoidal structure `𝟙_ C` -/
  tensorUnit : C := DMonStruct.one
  /-  The negator on objects -/
  negatorObj : C → C := DMonStruct.dash
  /-- The left cancellation isomorphism `X'  ⊗ X ≃ I` -/
  cancellationLeft : ∀ X : C, tensorObj (negatorObj X) X ≅ tensorUnit
    /-- The right cancellation isomorphism `I ≃ X ⊗ X'` -/
  cancellationRight : ∀ X : C, tensorUnit ≅ tensorObj X (negatorObj X)

namespace SSCatGrp

export SSCatGrpStruct
  (tensorObj whiskerLeft whiskerRight tensorHom tensorUnit negatorObj cancellationLeft cancellationRight)

end SSCatGrp

namespace SSCatGrp

/-- Notation for `tensorObj`, the tensor product of objects in a monoidal category -/
scoped infixr:70 " ⊗ " => SSCatGrpStruct.tensorObj

/-- Notation for the `whiskerLeft` operator of monoidal categories -/
scoped infixr:81 " ◁ " => SSCatGrpStruct.whiskerLeft

/-- Notation for the `whiskerRight` operator of monoidal categories -/
scoped infixl:81 " ▷ " => SSCatGrpStruct.whiskerRight

/-- Notation for `tensorHom`, the tensor product of morphisms in a monoidal category -/
scoped infixr:70 " ⊗ " => SSCatGrpStruct.tensorHom

/-- Notation for `tensorUnit`, the two-sided identity of `⊗` -/
scoped notation "𝟙_ " C:max => (SSCatGrpStruct.tensorUnit : C)

/-- Notation for `negatorObj`, the negator of objects in a categorical group -/
scoped notation " D " => SSCatGrpStruct.negatorObj


open Lean PrettyPrinter.Delaborator SubExpr in
/-- Used to ensure that `𝟙_` notation is used, as the ascription makes this not automatic. -/
@[delab app.CategoryTheory.CatGrpStruct.tensorUnit]
def delabTensorUnit : Delab := whenPPOption getPPNotation <| withOverApp 3 do
  let e ← getExpr
  guard <| e.isAppOfArity ``MonoidalCategoryStruct.tensorUnit 3
  let C ← withNaryArg 0 delab
  `(𝟙_ $C)

/-- Notation for the `cancellationLeft`: `X' ⊗ X ≃ 𝟙` -/
scoped notation "ε_" => SSCatGrpStruct.cancellationLeft

/-- Notation for the `cancellationRight`: `𝟙 ≃ X ⊗ X' ` -/
scoped notation "η_" => SSCatGrpStruct.cancellationRight


end SSCatGrp


open SSCatGrp

/--
In a CatGrp, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product is strictly associative on objects, and morphisms. The negator is not inverse of an object with respect to `⊗`  but there is a
specified left cancellation, `ε_X  : X' ⊗ X ≅ 𝟙_C` and there is a specified right cancellation, `η_X : 𝟙_C ≅ X ⊗ X'`. These cancellation isomorphisms satisfy cancellation conditions.

See <https://stacks.math.columbia.edu/tag/0FFK>.
-/
-- Porting note: The Mathport did not translate the temporary notation

class SSCatGrp (C : Type u) [DMonStruct: DMon C] [𝒞 : Category.{v} C] extends SSCatGrpStruct C where
  tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) :
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by
      aesop_cat
  /-- Tensor product of identity maps is the identity: `(𝟙 X₁ ⊗ 𝟙 X₂) = 𝟙 (X₁ ⊗ X₂)` -/
  tensor_id : ∀ X₁ X₂ : C, 𝟙 X₁ ⊗ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂) := by aesop_cat
  /--
  Composition of tensor products is tensor product of compositions:
  `(f₁ ⊗ g₁) ∘ (f₂ ⊗ g₂) = (f₁ ∘ f₂) ⊗ (g₁ ⊗ g₂)`
  -/
  tensor_comp :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by
    aesop_cat
  whiskerLeft_id : ∀ (X Y : C), X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
    aesop_cat
  id_whiskerRight : ∀ (X Y : C), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
    aesop_cat
  /-- Naturality of the associator isomorphism: `(f₁ ⊗ f₂) ⊗ f₃ ≃ f₁ ⊗ (f₂ ⊗ f₃)` -/
  associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊗ f₂) ⊗ f₃)  =  (f₁ ⊗ (f₂ ⊗ f₃)) := by
    aesop_cat
  /--
  Naturality of the left unitor, commutativity of `𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y ⟶ Y` and `𝟙_ C ⊗ X ⟶ X ⟶ Y`
  -/
  leftUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), 𝟙_ _ ◁ f  =  f := by
    aesop_cat
  /--
  Naturality of the right unitor: commutativity of `X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C ⟶ Y` and `X ⊗ 𝟙_ C ⟶ X ⟶ Y`
  -/
  rightUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), f ▷ 𝟙_ _  =  f := by
    aesop_cat
  /--
  The cancellation condition
  -/
  cancellation_condition_1 :
    ∀ X : C,
      (η_ X).hom ▷ X ≫  X ◁ (ε_ X).hom =
        𝟙 X := by
    aesop_cat
  /--
  The cancellation_condition_2
  -/
  cancellation_condition_2 :
    ∀ X : C, D X ◁ (η_ X).hom ≫ (ε_ X).hom ▷ D X = 𝟙 (D X) := by
    aesop_cat

attribute [reassoc] SSCatGrp.tensorHom_def
attribute [reassoc, simp] MonoidalCategory.whiskerLeft_id
attribute [reassoc, simp] MonoidalCategory.id_whiskerRight
attribute [reassoc] MonoidalCategory.tensor_comp
attribute [simp] MonoidalCategory.tensor_comp
attribute [reassoc] MonoidalCategory.associator_naturality
attribute [reassoc] MonoidalCategory.leftUnitor_naturality
attribute [reassoc] MonoidalCategory.rightUnitor_naturality
attribute [reassoc (attr := simp)] MonoidalCategory.pentagon
attribute [reassoc (attr := simp)] MonoidalCategory.triangle
