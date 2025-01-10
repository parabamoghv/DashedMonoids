import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0



namespace MyCategoryTheory

/-
Goals:
Define category, functor, natural transformation
Define strict monoidal category, monoidal functor, monoidal natural transformation
Define free strict monoidal category
Define semi strict categorical group, catgrp functor, catgrp natural transformation
Define free semi strict categorical group
Show that a semi-strict categorical group is equivalent to a strict categorical group
-/


universe u

class CategoryStruct (obj: Type u ): Type (u+1) where
  /- Type of morphisms between given domain and codomain -/
  Hom : obj → obj → Sort (u+1) -- can be Type u
  /- Identity morphism for an object -/
  id (X: obj) : Hom X X
  /- Composition rule -/
  comp {X Y Z: obj} : (Hom X Y) → (Hom Y Z) → (Hom X Z)


/- Notation for hom type. Use f: X⟶ Y for X Y:obj  -/
infixr:10 " ⟶ " => CategoryStruct.Hom

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙" => CategoryStruct.id  -- type as \b1

/-- Notation for composition of morphisms in a category. -/
scoped infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

class Category (obj : Type u) extends CategoryStruct.{u} obj : Type (u+1) where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y),
    𝟙 X ≫ f = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y),
    f ≫ 𝟙 Y = f := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
    (f ≫ g) ≫ h = f ≫ g ≫ h :=
    by aesop_cat

/- Equalilty between homomorphisms is defined as equality between dependent type (Domain, Codomain, morphism: Domain ⟶ Codomain) -/
inductive MyHomEq {C:Type u}[catC: Category C](f:(X:C) × (Y:C) ×   (X ⟶ Y)) : ((X:C) ×  (Y:C) × (X⟶ Y)) → Prop
  | refl : MyHomEq f f

/- This defintion is for illustrative purpose, we can simply replace HomEq ⟨ A, B, f⟩  ⟨X, Y, g ⟩  with  ⟨ A, B, f⟩ = ⟨X, Y, g ⟩  -/

/- This definition is cumbersome to use. We will define the same equality using HEq -/


/- Equalilty between homomorphisms is defined as equality between domains, codomains, and heterogeneous equality between morphisms -/


def EqHom {C:Type u}[ Category C] {W X Y Z: C} (f:W⟶ X)(g:Y⟶ Z):Prop := (W=Y)∧  (X= Z) ∧ (HEq f g)

/- EqHom is reflexive -/
example  {C:Type u}[ Category C]{X Y:C} (f:X⟶ Y)  : EqHom f f := ⟨rfl, rfl, HEq.rfl ⟩

/- EqHom is symmetric -/
example {C:Type u}[Category C]{W X Y Z : C} (f: W⟶ X) (g:Y⟶ Z) : ( EqHom f g) → (EqHom g f) := fun ⟨eqDomain, eqCodomain, eqHom ⟩  =>  ⟨eqDomain.symm, eqCodomain.symm, eqHom.symm ⟩

/- EqHom is transitive -/
example {C:Type u}[Category C]{a b c x y z : C} (f: a⟶ x) (g:b⟶ y)(h:c⟶ z) : ( EqHom f g) → (EqHom g h) → (EqHom f h)  := by
  intro ⟨eqDomain_fg, eqCodomain_fg, eqHom_fg ⟩ ⟨eqDomain_gh, eqCodomain_gh, eqHom_gh ⟩
  exact ⟨eqDomain_fg.trans eqDomain_gh, eqCodomain_fg.trans eqCodomain_gh, eqHom_fg.trans eqHom_gh ⟩

/- An example -/
example {C:Type u}[catC: Category C] {X Y: C}(f:X⟶ Y): (A:C) × (B:C) ×  (A⟶ B) := by
  constructor
  case fst =>
    exact  X
  case snd =>
    constructor
    case fst =>
      exact Y
    case snd =>
      exact f

/- EqHom is same as the previous equality -/
example {C:Type u}[catC: Category C] {w x y z: C}(f:w ⟶ x)(g:y ⟶ z):  (⟨ w, x, f⟩ : ((X: C) × (Y: C) × (X⟶ Y))   ) = ( ⟨ y, z, g⟩ ) ↔ EqHom f g := by
  constructor
  case mp=>

    rintro ⟨ ⟩
    rw[EqHom]
    simp only [heq_eq_eq, and_self]

  case mpr=>
    intro ⟨eqC, eqD, eqHom ⟩
    subst eqC
    subst eqD
    --simp only [heq_eq_eq] at eqHom
    subst eqHom
    exact rfl

/- If f and g have same domain and codomain then EqHom f g is same as f=g -/
example {C:Type u}[catC: Category C] {X Y: C}(f g:X⟶ Y): f=g ↔ EqHom f g := by
  constructor
  case mp=>
    intro eqfg
    rw[EqHom]
    simp only [heq_eq_eq, true_and, eqfg]

  case mpr=>
    intro ⟨_, _, eqfg ⟩
    rw[heq_eq_eq] at eqfg
    exact eqfg


/- Product category C× D -/
instance ProdCat (C D:Type u)[catC : Category C][catD: Category D]: Category (C × D) where
  Hom X Y := (X.1 ⟶   Y.1) × (X.2 ⟶ Y.2)

  id X := (𝟙 X.1, 𝟙 X.2)

  comp := by
    intro X Y Z f g
    exact ((f.1) ≫ (g.1), (f.2) ≫  (g.2))

  id_comp := by
    intro X Y f
    simp
    rw[catC.id_comp]
    rw[catD.id_comp]
    simp only [Prod.mk.eta]

  comp_id := by
    intro X Y f
    simp
    rw[catC.comp_id]
    rw[catD.comp_id]
    simp only [Prod.mk.eta]

  assoc := by
    intro W X Y Z f g h
    simp only [Prod.mk.injEq]
    constructor
    case left=>
      apply catC.assoc
    case right=>
      exact catD.assoc f.2 g.2 h.2



class FunctorStruct {C D: Type u} [catC: Category C] [catD: Category D] (f:C→ D) : Type (u) where
  /- Functor on morphisms -/
  onHom {X Y: C} : (X ⟶ Y) → ( (f X) ⟶ (f Y))


class Functor {C D: Type u} [catC: Category C] [catD: Category D] (f:C→ D) extends FunctorStruct.{u} f : Type u where
  /- Functor on identity is identity -/
  id {X : C} : onHom (𝟙 X) = 𝟙 (f X)

  /- Functor respects composition -/
  comp {X Y Z: C} (f : X⟶ Y) (g: Y⟶ Z) : onHom (f ≫ g ) = (onHom f) ≫ (onHom g)


/- Instance of identity functor -/
instance IdFunctor (C:Type u)[catC: Category C] : Functor (id: C→ C)  where
  /- Identity on f is f -/
  onHom f := f


  id := by
    intro x
    simp only [id_eq]

  comp := by
    intro X Y Z f g
    simp

/- Composition of functors is a functor -/
theorem FunctorComp {C D E: Type u}[catC : Category C][catD:Category D][catE: Category E](F:C→ D)(G:D→ E)[functorF: Functor F][functorG : Functor G] : Functor (G∘ F) where
  onHom f:= functorG.onHom ( functorF.onHom f)

  id := by
    intro X
    simp only [Function.comp_apply]
    rw[functorF.id]
    rw[functorG.id]

  comp := by
    intro X Y Z f g
    simp
    rw[functorF.comp]
    rw[functorG.comp]

/- Constant functor  X=> A  -/
instance FunctorConst {C D: Type u}[catC : Category C][catD:Category D](A: D): Functor (fun (_:C) => A) where
  onHom _:= 𝟙 A

  id := by
    intro _
    simp only

  comp := by
    intro X Y Z f g
    simp only
    rw[catD.comp_id ]

/- Functor product F × G -/
instance ProdFunctor {A B C D: Type u}[catA: Category A][catB: Category B][catC: Category C][catA: Category D](F:A→ B)(G:C→ D)[functorF : Functor F][functorG : Functor G]: @Functor.{u} (A× C) (B× D) (ProdCat A C) (ProdCat B D) (fun ((x, y): A × C) => ((F x, G y):B × D)) where
  onHom := by
    intro X Y f
    constructor
    case fst=>
      simp
      exact functorF.onHom f.1
    case snd=>
      simp
      exact functorG.onHom f.2

  id := by
    intro (x, y)
    simp only [id_eq]
    -- have h: (𝟙 (x, y)) = (𝟙 x, 𝟙 y):= by
    --   simp[ProdCat]
    simp[ProdCat]
    constructor
    case left=>
      rw[functorF.id]
    case right=>
      rw[functorG.id]


  comp := by
    intro X Y Z f g
    simp[ProdCat]
    constructor
    case left=>
      rw[functorF.comp]
    case right=>
      rw[functorG.comp]

/- Triangle functor X => (X, X) -/
instance TriangleFunctor {C:Type u}[catC : Category C] : @Functor.{u} (C) (C× C) (catC) (ProdCat C C) (fun (X:C) => ((X, X):C× C)) where
  onHom := by
    intro X Y f
    constructor
    case fst =>
      --simp
      exact f
    case snd =>
      exact f

  id := by
    intro X
    simp[ProdCat]

  comp := by
    intro X Y Z f g
    simp[ProdCat]


/- Multiplication on left functor X => A ⊗ X -/
instance FunctorLeftTensor {C:Type u}[catC: Category C](tensor: (C× C) → C)[functorTensor: Functor tensor](A:C): Functor ( fun (X:C) => (tensor (A, X): C)) where
  onHom := by
    intro X Y f
    apply functorTensor.onHom
    simp[ProdCat]
    constructor
    case fst =>
      exact 𝟙 A
    case snd =>
      exact f

  id := by
    intro X
    apply functorTensor.id

  comp := by
    intro X Y Z f g
    simp[ProdCat]
    rw[← functorTensor.comp]
    simp[ProdCat]
    rw[catC.comp_id]






/- Natural Transformation between functors F G -/
class NatTrans {C D:Type u}{F G:C→ D}[catC: Category C][catD: Category D][funF : Functor F][funG : Functor G](onObj: (X:C)→ (F X ⟶ G X)): Type u where
  /- Naturality condition -/
  Naturality {X Y: C} (f:X⟶ Y) : (funF.onHom f) ≫ (onObj Y) = (onObj X) ≫ (funG.onHom f)

/- Id natural transformation on objects -/
example {C D:Type u}(F :C→ D)[catD: Category D] : (X:C) → (F X ⟶ F X) := by
  intro X
  exact 𝟙 (F X)

/- Identity natural transformation -/
instance IdNatTrans  {C D:Type u}(F :C→ D)[catC: Category C][catD: Category D][functorF:Functor F]  : NatTrans (fun (X:C) => 𝟙 (F X))  := by
  constructor
  intro X Y f
  --rw[IdNatTransStruct]
  --rw[IdNatTransStruct]
  rw[catD.comp_id]
  rw[catD.id_comp]





/- Attempts at defining Strict Monoidal Category -/


-- class StMonCat (C: Type u) (Tensor: (C× C) → C)[catC : Category C][monC:Monoid C] [functorTensor : Functor Tensor ] where
--   Tensor_eq_mul (x y:C) : Tensor (x, y) = monC.mul x y
--   Left_unity {x y:C} (f:x⟶ y) : HomEq ⟨ Tensor (monC.one, x), Tensor (monC.one, y), functorTensor.onHom  ((𝟙 monC.one, f): (monC.one, x) ⟶ (monC.one, y))⟩  ⟨x, y, f ⟩
--   Right_unity {x y :C} (f:x⟶ y) : HomEq ⟨ Tensor ( x, monC.one), Tensor ( y, monC.one), functorTensor.onHom  (( f, 𝟙 monC.one): (x, monC.one) ⟶ ( y, monC.one))⟩  ⟨x, y, f ⟩
--   Assoc {a b c x y z:C} (f:a⟶ x)(g:b⟶ y) (h:c⟶ z): HomEq ⟨Tensor (a, Tensor (b, c)), Tensor (x, Tensor (y, z)), functorTensor.onHom (f, functorTensor.onHom (g, h)) ⟩ ⟨Tensor (Tensor (a, b), c), Tensor (Tensor (x, y), z), functorTensor.onHom (functorTensor.onHom (f, g), h) ⟩





-- class MyStMonCat (C: Type u) [catC : Category C][monC:Monoid C]  where
--   Tensor : Functor ((fun ((x, y):C× C) => monC.mul x y))
--   Left_unity {x y:C} (f:x⟶ y) : HomEq ⟨  ( monC.mul monC.one x),  (monC.mul monC.one  y), Tensor.onHom  ((𝟙 monC.one, f): (monC.one, x) ⟶ (monC.one, y))⟩  ⟨x, y, f ⟩
--   Right_unity {x y :C} (f:x⟶ y) : HomEq ⟨  (monC.mul x monC.one),  (monC.mul y monC.one), Tensor.onHom  (( f, 𝟙 monC.one): (x, monC.one) ⟶ ( y, monC.one))⟩  ⟨x, y, f ⟩
--   Assoc {a b c x y z:C} (f:a⟶ x)(g:b⟶ y) (h:c⟶ z): HomEq ⟨monC.mul a (monC.mul b c), monC.mul x (monC.mul y z), Tensor.onHom ((f, Tensor.onHom ((g, h): (b, c)⟶ (y, z))) : (a, monC.mul b c) ⟶ (x, monC.mul y z) ) ⟩  ⟨monC.mul (monC.mul a b) c, monC.mul (monC.mul x y) z, Tensor.onHom ((Tensor.onHom ((f, g): (a, b)⟶ (x, y)), h) : (monC.mul a b, c) ⟶ (monC.mul x y, z) ) ⟩




/- A strict monoidal category is a category C with objects of C forming a monoid. The following conditions are satisfied -/
class StMonCat (C: Type u) extends Monoid C, Category C  where
  /- The multiplication in the monoid is a functor -/
  tensor : Functor ((fun ((x, y):C× C) => mul x y))

  /- For a morphism f, 𝟙_I ⊗ f = f -/
  left_unity {x y:C} (f:x⟶ y) : EqHom (tensor.onHom  ((𝟙 one, f): (one, x) ⟶ (one, y))) f

  /- For a morphism f, f ⊗ 𝟙_I = f -/
  right_unity {x y:C} (f:x⟶ y) : EqHom (tensor.onHom  (( f, 𝟙 one): (x, one) ⟶ ( y, one))) f

  /- For morphisms f g h, f ⊗ (g ⊗ h) = (f ⊗ g) ⊗ h -/
  associativity {a b c x y z:C} (f:a⟶ x)(g:b⟶ y) (h:c⟶ z): EqHom (tensor.onHom ((f, tensor.onHom ((g, h): (b, c)⟶ (y, z))) : (a, mul b c) ⟶ (x, mul y z) )) (tensor.onHom ((tensor.onHom ((f, g): (a, b)⟶ (x, y)), h) : (mul a b, c) ⟶ (mul x y, z) ))


/- (Monoidal) Functor between strict monoidal categories is a functor with following data -/
class FunctorStMonCat {C D:Type u}(F:C→ D)[mcatC: StMonCat C][mcatD: StMonCat D] extends Functor F where
  /- Morphism F_0 : J ⟶ F I -/
  on_unit : mcatD.one ⟶ F (mcatC.one)

  /- For objects x y in C, there are morphisms F_2(x, y) = F(x) ⊗ F(y) ⟶ F(x ⊗ y) -/
  on_tensor (x y:C) : mcatD.mul (F x) (F y) ⟶ F (mcatC.mul x y)

  /- left unity condition: For an object x in C, F_2(I, x) ∘ (F_0 ⊗ 𝟙_(F x)) = 𝟙_(F x)  -/
  cond_left_unity (x: C) :
    EqHom
    ( (mcatD.tensor.onHom ( (on_unit, 𝟙 (F x) ) : (mcatD.one, F x) ⟶ (F (mcatC.one), F x) ) ) ≫ on_tensor mcatC.one x    )
    (𝟙 (F x)  )

  /- right unity condition: For an object x in C, F_2(I, x) ∘ (F_0 ⊗ 𝟙_(F x)) = 𝟙_(F x)  -/
  cond_right_unity (x: C) :
    EqHom
    ( (mcatD.tensor.onHom ( (𝟙 (F x), on_unit ) : (F x, mcatD.one) ⟶ (F x, F (mcatC.one)) ) ) ≫ on_tensor  x mcatC.one )
    ( 𝟙 (F x) )

  /- Associativity condition: For objects x y z in C,
          F_2(x, y ⊗ z ) ∘ (𝟙_(F x) ⊗ F_2(y, z)) = F_2(x ⊗ y ) ∘ (F_2(x, y) ⊗ 𝟙_(F z))  -/
  cond_associativity (x y z : C) :
    EqHom
    ( (mcatD.tensor.onHom ((𝟙 (F x), on_tensor y z): (F x, mcatD.mul (F y) (F z)) ⟶ (F x, F (mcatC.mul y z)) ))        ≫    (on_tensor x (mcatC.mul y z)) )

    ( (mcatD.tensor.onHom ((on_tensor x y, 𝟙 (F z)): (mcatD.mul (F x) (F y), (F z)) ⟶ (F (mcatC.mul x y), F z) ))        ≫    (on_tensor (mcatC.mul x y) z)  )


-- inductive Singleton : Type u where
--   | point : Singleton

-- inductive Empty : Type u where




example {S:Type u}(x:List S) : Type u := {x' : List S // x' = x}

example {S:Type u}(x:List S) : List S := x++x


/- List S can be made into a category as follows -/
instance FreeStMonCat (S:Type u) : Category (List S) where
  /- Morphisms from x to y are singleton {[]} if x=y else empty -/
  Hom := by
    intro x y
    exact {x' : List S // x' = [] ∧ x = y}

  /- Since x=x, id_x will be [] -/
  id := by
    intro x
    --simp
    use []


  /- From above only morphisms are id_x = [], thus composition is of id_x -/
  comp := by
    intro x y z ⟨_, _, prop2x ⟩ ⟨_, _, prop2y ⟩
    use []
    constructor
    case left=>
      exact rfl
    case right=>
      rw[prop2x]
      --rw[← prop1y]
      rw[prop2y]


  /- All morphisms are identity, thus the conditions are followed -/
  id_comp := by
    intro x y ⟨val, pro1, pro2 ⟩
    simp
    rw[pro1]


  comp_id := by
    intro x y ⟨val, prop1, prop2 ⟩
    simp
    rw[prop1]

  assoc := by
    intro w x y z ⟨valf, prop1f, prop2f ⟩ ⟨valg, prop1g, prop2g ⟩ ⟨_, _, prop2h ⟩
    simp


def cat_thin (C: Type u) [Category C] := {x y :C} → (f g:x⟶ y) → f= g



theorem FreeStMonCat_is_thin_aux {S:Type u}{x y:List S} (f g:x⟶ y) : f =g := by
  rcases f with ⟨valf, prop1f, prop2f ⟩
  rcases g with ⟨valg, prop1g, prop2g ⟩
  simp[prop1f, prop1g]

example {S:Type u}(x y:List S)(f:x⟶ y) : Σ  (A : List S × List S), A.1⟶ A.2 := by
  constructor
  case fst=>
    exact (x, y)
  case snd=>
    exact f

example {S:Type u} {w x y z:List S} (f:w⟶ x)(g:y⟶ z) :
  (w=y)∧ (x=z)
  ↔
  (⟨(w, x), f  ⟩ : Σ  (A : List S × List S), A.1⟶ A.2 ) = (⟨(y, z), g  ⟩ : Σ  (A : List S × List S), A.1⟶ A.2 ) := by

  constructor
  case mp =>
    intro ⟨eq1, eq2 ⟩
    simp[eq1, eq2]
    subst eq1
    subst eq2
    simp
    apply FreeStMonCat_is_thin_aux

  case mpr =>
    rintro ⟨_ , _⟩
    simp only [and_self]

theorem FreeStMonCat_is_thin {S: Type u} {w x y z: List S} (f:w⟶ x)(g:y ⟶ z) :
  (w=y)∧ (x=z)
  ↔
  EqHom f g := by

  constructor
  case mp=>
    intro ⟨eq1, eq2 ⟩
    rw[EqHom]
    simp[eq1, eq2]
    subst eq1
    subst eq2
    rw[heq_eq_eq]
    exact FreeStMonCat_is_thin_aux f g

  case mpr=>
    rintro ⟨ eq1,eq2, _⟩
    exact ⟨eq1, eq2 ⟩

theorem FreeStMonCat_is_thin.mp {S: Type u} {w x y z: List S} (f:w⟶ x)(g:y ⟶ z) :
  (w=y)∧ (x=z)
  →
  EqHom f g := by

  intro hyp
  rw[← (FreeStMonCat_is_thin f g)]
  exact hyp

example {S:Type u} {w x y z:List S} (f:w⟶ x)(g:y⟶ z) :
  (w=y)∧ (x=z)
  ↔
  (⟨w, x, f  ⟩ : (X:List S) × (Y:List S)× (X⟶ Y) ) = (⟨y, z, g  ⟩  ) := by

  constructor
  case mp =>
    intro ⟨eq1, eq2 ⟩
    simp[eq1, eq2]
    subst eq1
    subst eq2
    simp
    apply FreeStMonCat_is_thin_aux

  case mpr =>
    rintro ⟨_ , _⟩
    simp only [and_self]



instance tensor_FreeStMonCat {S:Type u} : Functor (fun ((x, y):(List S)× (List S)) => x++y) where
  onHom := by
    intro ⟨x1, x2⟩  (y1, y2) (f1, f2)
    simp at f1
    simp at f2
    simp
    rcases f1 with ⟨val_f1, _ ,prop2_f1 ⟩
    rcases f2 with ⟨val_f2, _, prop2_f2 ⟩

    use []

    simp

    rw[prop2_f1]
    rw[prop2_f2]

  id := by
    intro _
    apply FreeStMonCat_is_thin_aux

  comp := by
    intro _ _ _ _ _
    apply FreeStMonCat_is_thin_aux


instance {S:Type u} : StMonCat (List S) where
  mul := List.append
  one := []
  one_mul := List.nil_append
  mul_one := List.append_nil
  mul_assoc := List.append_assoc

  tensor := tensor_FreeStMonCat

  left_unity := by
    intro x y f
    simp only [List.append_eq, List.nil_append, Sigma.mk.inj_iff, heq_eq_eq, true_and]

    apply FreeStMonCat_is_thin.mp
    simp

  right_unity := by
    intro x y f
    rw[← FreeStMonCat_is_thin]
    simp only [List.append_eq, List.append_nil, and_self]

  associativity := by
    intro a b c x y z f g h
    rw[← FreeStMonCat_is_thin]
    simp only [List.append_eq, List.append_assoc, and_self]





structure DMon (M:Type u) extends Monoid M where
  dash : M → M
  id_dash  : dash one = one


theorem something (T : Type u) (S : Set T) (x y : S) : x.val = y.val → x =y := by
  intro h
  rw[Subtype.mk.injEq]
  exact h


instance construction_cat_thin_struct (M N : Type u) [monM : Monoid M] (F: M → N) : CategoryStruct M where
  Hom := by
    intro X Y
    exact {x' : List M // (x' = []) ∧ (F X = F Y)}

  id := by
    intro X
    use []

  comp := by
    intro X Y Z ⟨f, hf, hfXY ⟩  ⟨g, hg, hgYZ ⟩
    use []
    simp only [true_and]
    rw[← hgYZ]
    exact hfXY

example (M N : Type u) [monM : Monoid M] (F: M → N) (X Y : M)  ( f g : (construction_cat_thin_struct M N F).Hom  X  Y)  : f =g :=by
  rcases f with ⟨valf, propf1, propf2⟩
  rcases g with ⟨valg, propg1, propg2 ⟩
  apply something
  simp
  rw[propg1]
  exact propf1

instance construction_cat_thin (M N : Type u) [monM : Monoid M] (F: M → N) : Category M where
  Hom := by
    intro X Y
    exact {x' : List M // (x' = []) ∧ (F X = F Y)}

  id := by
    intro X
    use []

  comp := by
    intro X Y Z ⟨f, hf, hfXY ⟩  ⟨g, hg, hgYZ ⟩
    use []
    simp only [true_and]
    rw[← hgYZ]
    exact hfXY

  id_comp := by
    intro X Y ⟨val, prop1, prop2 ⟩
    simp
    rw[prop1]

  comp_id := by
    intro X Y ⟨val, prop1, prop2 ⟩
    simp
    rw[prop1]

  assoc := by
    intro W X Y Z ⟨f, f_prop1, f_prop2 ⟩ ⟨g, g_prop1, g_prop2 ⟩ ⟨h, h_prop1, h_prop2 ⟩
    apply something
    --simp only [id_eq, eq_mpr_eq_cast]
    simp[f_prop1, f_prop2, g_prop1, g_prop2]
    subst f_prop1


    subst g_prop1
    subst h_prop1
    --simp
    sorry
