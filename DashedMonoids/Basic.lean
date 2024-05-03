import Mathlib
import DashedMonoids.ListProp
--open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

--To import files from this folder use DashedMonoids.filename. To import files from a new folder, first update lakefile.lean

--Basis file will have basic definitions. Universal property of DMon.
--Make freeDashedCriteria file
--Make monoid file with
--Interval file will define an interval and its properties
--Make Bracketing file that will have bracketing
--Make DashAssignmen file
--Make Dashed words file

#check Classical.choose
#check Classical.choose_spec

--universe u v w
#check List.ListTwoOrMore_neq_ListOne


--variable {S: Type _}

--variable {i n m: Nat}

namespace DashedMonoid

--This file should have basic definitions/results about Dashed Monoids. Definitions: DMon, Dash, k-dashes, m-multiplication, GenSets wrt dash and mul, Ind wrt dash



-----------------------------------------------------------
---------------Definition of Dashed-Monoids---------------
-----------------------------------------------------------

section Defn


--Dashed-monoid "DMon" is a monoid with unary operation "dash" such that 1' = 1
class DMon (M:Type _) extends Monoid M where
  dash : M → M
  unit_dash : dash 1 = 1

end Defn


section Examples
--Examples of dashed monoids: Monoids, Group, Natural Numbers


variable {M:Type _}[stM:DMon M]


--A Monoid can be a dashed monoid with dash equal to id
def Mon_to_DMon :DMon M where
  dash := id
  unit_dash:= rfl

--Natural numbers are dashed-monoids with the dash equal to id
instance Nat_DMon:DMon Nat where
  dash := id
  unit_dash := by exact rfl

--A group can be a dashed monoid with dash equal to inv.
def Group_to_DMon (G:Type _)[st:Group G]: DMon G:= by
  constructor
  case dash => exact st.inv
  case unit_dash => exact inv_one

end Examples


section BasicProperties

variable {M:Type _}[stM:DMon M]
variable {N:Type _}[stN:DMon N]

section Dashes
--Definitions and properties regarding dashes



--Taking dash of an element k times
def dash_k (k:Nat)(x:M):M:=by
  match k with
  | Nat.zero => exact x
  | Nat.succ k => exact stM.dash (dash_k k x)

--alternate definition
-- def dash_k_ (k:Nat)(x:M):M:=by
--   induction' k with _ hk
--   case zero => exact x
--   case succ => exact stM.dash hk



--Taking zero dashes is same as id: x⁰ = x
theorem dash_zero (x:M):dash_k 0 x = x:=by
  exact rfl

--Taking one dash is same as dash: x¹ = x'
theorem dash_one (x:M):dash_k 1 x = stM.dash x:= by
  exact rfl

--Taking k+1 dash is same as dash of dash_k: xᵏ⁺¹ = (xᵏ)'
theorem dash_dash_k (k:Nat)(x:M):dash_k (k+1) x = stM.dash (dash_k k x):= by
  rw[dash_k]
  -- simp only [dash_k, Nat.rec_add_one]

--Taking k+1 dash is same as dash_k of dash: xᵏ⁺¹ = (x')ᵏ
theorem dash_k_dash (k:Nat)(x:M) : dash_k (k+1) x= dash_k k (stM.dash x):=by
  rw[dash_k]
  induction' k with k hk
  case zero =>
    rw[dash_zero]
    rw[dash_zero]
  case succ =>
    rw[dash_dash_k]
    rw[dash_dash_k]
    rw[hk]


end Dashes

section M_pos


--Underlying set of dashed monoid without the unit
def M_pos :Set M:= Set.univ \ {1}


end M_pos



section Basis_dash
--Definitions of set generated by dash




--Set generated by the dash operation
def Gen_dash (X:Set M):Set M:= by
  intro z
  exact ∃ r:Nat, ∃ x:X, dash_k r x.1 = z

--Composite elements of Gen_dash
def GenP_dash (X:Set M):Set M:= by
  intro z
  exact ∃ r:Nat, r≠ 0 ∧ ∃ x:X, dash_k r x.1=z

def is_GenSet_dash (X:Set M):Prop:= Gen_dash X = M_pos

def is_Indp_dash (X:Set M):Prop:= ∀  r:Nat, ∀  x:X, ∀  k:Nat, ∀ y:X, (dash_k r x.1 = dash_k k y.1)→ (r=k ∧ x=y)

def is_Basis_dash (X:Set M):Prop:= is_GenSet_dash X ∧ is_Indp_dash X

end Basis_dash


section Mul

--Taking mul of an of an list
def mul_L_ (L:List M):M:=by
  induction' L with head _ tail_h
  case nil => exact 1
  case cons => exact head*tail_h

def mul_L (L:List M):M:= by
  match L with
  | [] => exact (1:M)
  | a::L => exact a*mul_L L


--Taking zero dashes is same as id
theorem mul_L_zero :mul_L  [] = 1:=by
  exact rfl

--Taking one mul is same as itself
theorem mul_L_one (x:M):mul_L [x] = x:= by
  rw[mul_L]
  rw[mul_L]
  simp only [mul_one]

--Taking two mul is same as mul
theorem mul_L_two (x y:M):mul_L [x, y] = x*y:= by
  rw[mul_L]
  rw[mul_L]
  rw[mul_L]
  simp only [mul_one]

--mul (x::L) = x * mul L
theorem mul_L_succ (x:M)(L: List M):mul_L (x::L) = x*(mul_L L):= by
  rw[mul_L]


-- Following function is in DashedMonoids/ListProp
-- For X⊆ M given L:List X it gives a List in M.
-- def to_List_M (X:Set M)(L:List X):List M:=by
--   induction' L with head _ tail_h
--   case nil=> exact []
--   case cons=> exact (head.1)::tail_h



theorem mul_L_one_on_subset (X:Set M)(x: X):mul_L (List.up_List  [x]) = x:= by
  have h:List.up_List  [x] = [x.1] :=by
    rw[List.up_List]
  rw[h]
  exact mul_L_one x.1

end Mul


section Basis_mul

def Gen_mul (X:Set M):Set M:= by
  intro z
  exact ∃ L:List X, L≠ [] ∧  mul_L (List.up_List L) = z


def mul_genP_X (X:Set M):Set M:= by
  intro z
  exact ∃ L:List X, (L≠ [] ∧ (∀ a:X, L≠ [a] )) ∧ (mul_L (List.up_List L) = z)

def is_mul_gen_set (X:Set M):Prop:= Gen_mul X = M_pos

def is_mul_indp_set (X:Set M):Prop:= ∀  L :List X, ∀ P:List X,  L≠ []→ P≠ []→ ((mul_L (List.up_List L)) = (mul_L (List.up_List  P))) → L=P


structure FreeDMon_like (M:Type)[DMon M] where
  basis: Set M
  mul_basis: Set M
  dash_basis:Set M
  mul_basis_is_mul_gen : is_mul_gen_set mul_basis
  mul_basis_is_mul_indp : is_mul_indp_set mul_basis
  dash_basis_is_mul_gen : is_GenSet_dash dash_basis
  dash_basis_is_dash_indp : is_Indp_dash dash_basis
  basis_cond_mul_basis_union: mul_basis = basis ∪ GenP_dash dash_basis
  basis_cond_mul_basis_disjoint: basis ∩ GenP_dash dash_basis = {}
  basis_cond_dash_basis_union: dash_basis = basis ∪ mul_genP_X mul_basis
  basis_cond_dash_basis_disjoint: basis ∩ mul_genP_X mul_basis = {}


def mul_compos (St: FreeDMon_like M):Set M:=GenP_dash St.dash_basis

--If X is mul indep then gen X = X sqcup genP x

variable (X:Set M)
lemma mul_gen_eq_cup_genP :Gen_mul X = X ∪ mul_genP_X X:= by
  ext x
  constructor
  case mp =>
    intro hx
    rcases hx with ⟨L, hL ⟩
    match L with
    | [] =>
        have hL1 := hL.1
        contradiction
    | [a] =>
        left
        have hL2 := hL.2
        have h:= mul_L_one_on_subset X a
        rw[h] at hL2
        rw[← hL2]
        exact a.2
    | a::b::L =>
        right
        constructor
        case w=>
          exact a::b::L
        case h=>
          constructor
          case left =>
              constructor
              case left=>
                  exact hL.1
              case right=>
                  exact List.ListTwoOrMore_neq_ListOne a b L
          case right =>
              exact hL.2
  case mpr =>
    rintro (hxL| hxR)
    case inl =>
      constructor
      case w=>
        exact [⟨ x, hxL⟩ ]
      case h=>
        constructor
        case left=>
          exact List.ListOne_neq_ListNil (⟨x, hxL⟩:X)
        case right=>
          exact mul_L_one_on_subset  X ⟨x, hxL ⟩
    case inr =>
      rcases hxR with ⟨L, hL ⟩
      constructor
      case w=>
        exact L
      case h=>
        constructor
        case left=>
          exact hL.1.1
        case right=>
          exact hL.2


lemma X_disjoint_GenP_mul (mul_indp: is_mul_indp_set X):X∩ mul_genP_X X = ∅:= by
  ext x
  constructor
  case mp=>
    rintro ⟨xinX, xinGenP ⟩
    rcases   xinGenP with ⟨L, hL ⟩
    --have contra:=mul_indp
    specialize mul_indp L [⟨ x, xinX⟩ ] hL.1.1
    specialize mul_indp (List.ListOne_neq_ListNil (⟨x, xinX ⟩ ))
    have h1:=  mul_L_one_on_subset X ⟨x, xinX ⟩
    have h2:mul_L (List.up_List L)=mul_L (List.up_List [⟨x, xinX ⟩ ]):= by
      rw[h1]
      exact hL.2
    specialize mul_indp h2
    --have hL:= hL.1.2
    --specialize hL ⟨x, xinX ⟩
    --simp only [Set.mem_empty_iff_false]
    exact hL.1.2 ⟨x, xinX ⟩  mul_indp
  case mpr=>
    simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, IsEmpty.forall_iff]

--for reference
-- def is_mul_indp_set (X:Set M):Prop:= ∀  L :List X, ∀ P:List X,  L≠ []→ P≠ []→ ((mul_L (List.up_List L)) = (mul_L (List.up_List  P))) → L=P

lemma mul_indp_sub {X Y:Set M}:(mul_indp:is_mul_indp_set X)→ Y⊆ X→ is_mul_indp_set Y:=sorry




lemma dash_gen_eq_cup_genP :Gen_dash X = X ∪ GenP_dash X:= by
  ext x
  constructor
  case mp=>
    rintro ⟨k,⟨a,ha⟩  ⟩
    by_cases k_zero:k=0
    case pos=>
      left
      rw[k_zero] at ha
      rw[dash_zero a.1] at ha
      rw[← ha]
      exact a.2
    case neg=>
      right
      constructor
      case w=>
        exact k
      case h=>
        constructor
        case left=>
          exact k_zero
        case right=>
          use a
  case mpr=>
    rintro (hx|⟨k,hk ⟩ )
    case inl=>
      constructor
      case w=>
        exact 0
      case h=>
        use ⟨x, hx ⟩
        exact dash_zero x
    case inr=>
      constructor
      case w=>
        exact k
      case h=>
        exact hk.2


lemma X_disjoint_GenP_dash (mul_indp: is_Indp_dash X):X∩ GenP_dash X = ∅:= by
  ext x
  constructor
  case mp=>
    rintro ⟨xinX, ⟨k,⟨ k_ne_0, ⟨a,ha⟩ ⟩ ⟩  ⟩
    specialize mul_indp 0 ⟨x, xinX ⟩ k a
    have h1:=dash_zero (x)
    rw[← h1] at ha
    specialize mul_indp ha.symm
    exact k_ne_0 mul_indp.1.symm
  case mpr=>
    simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, IsEmpty.forall_iff]

--for reference
-- def is_Indp_dash (X:Set M):Prop:= ∀  r:Nat, ∀  x:X, ∀  k:Nat, ∀ y:X, (dash_k r x.1 = dash_k k y.1)→ (r=k ∧ x=y)

lemma dash_indp_sub {X Y:Set M}:(dash_indp:is_Indp_dash X)→ Y⊆ X→ is_Indp_dash Y:=by
  intro dash_indp XsubY
  intro r x k y dash_eq
  specialize dash_indp r ⟨x.1, XsubY x.2 ⟩
  specialize dash_indp k ⟨y.1, XsubY y.2 ⟩
  specialize dash_indp dash_eq
  --simp at dash_indp
  constructor
  case left=>
    exact dash_indp.1
  case right=>
    have dash_indp := dash_indp.2
    simp only [Subtype.mk.injEq] at dash_indp
    ext
    exact dash_indp


example {X Y:Set M}:GenP_dash (X∪ Y) = (GenP_dash X)∪ (GenP_dash Y):= by
  ext x
  constructor
  case mp=>
    rintro ⟨k,⟨k_ne_0,⟨a,ha ⟩  ⟩  ⟩
    rcases a with ⟨ a, (aX|aY)⟩
    case inl=>
      left
      use k
      constructor
      case left=>
        exact k_ne_0
      case right=>
        use ⟨a, aX ⟩
    case inr=>
      right
      use k
      constructor
      case left=>
        exact k_ne_0
      case right=>
        use ⟨a, aY ⟩
  case mpr=>
    rintro (⟨k,⟨k_ne_0,⟨a,ha ⟩  ⟩  ⟩ |⟨k,⟨k_ne_0,⟨a,ha ⟩  ⟩  ⟩)
    case inl=>
      use k
      constructor
      case left=>
        exact k_ne_0
      case right=>
        constructor
        case w=>
          constructor
          case val=>
            exact a.1
          case property=>
            left
            exact a.2
        case h=>
          exact ha
    case inr=>
      use k
      constructor
      case left=>
        exact k_ne_0
      case right=>
        constructor
        case w=>
          constructor
          case val=>
            exact a.1
          case property=>
            right
            exact a.2
        case h=>
          exact ha


example {X Y Z:Set M}:(is_Indp_dash Z)→ (X⊆ Z)→ (Y⊆ Z)→ (X∩ Y =∅ )→ (GenP_dash X)∩ (GenP_dash Y)=∅ := by
  intro IndpZ XsubZ YsubZ Disj
  ext x
  constructor
  case mp=>
    rintro ⟨⟨r, ⟨_,⟨a,ha ⟩ ⟩ ⟩ ,⟨k, ⟨_,⟨b,hb ⟩ ⟩ ⟩ ⟩
    specialize IndpZ r ⟨a.1, XsubZ a.2 ⟩
    specialize IndpZ k ⟨b.1, YsubZ b.2⟩
    have h1:dash_k r a.1= dash_k k b.1:= by
      rw[ha]
      rw[← hb]
    specialize IndpZ h1
    have IndpZ:=IndpZ.2
    simp at IndpZ
    have h2:a.1∈ X∩ Y :=by
      constructor
      case left=>
        exact a.2
      case right=>
        rw[IndpZ]
        exact b.2
    rw[Disj] at h2
    exact h2
  case mpr=>
    simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, IsEmpty.forall_iff]

#check exists_unique_eq.elim
#check exists_unique_eq
#check ExistsUnique

example (p:M→ Prop)(h:ExistsUnique p):True:=by
  rcases h with ⟨_,_ ⟩
  sorry

noncomputable example {X:Set M}(Indp:is_Indp_dash X)(x:Gen_dash X):Nat:=by
  rcases x with ⟨x, prop  ⟩
  have n:= Classical.choose prop
  have h:= Classical.choose_spec prop
  exact n

def Count:List M→ Nat:= by
  intro L
  match L with
  | [] => exact 0
  | [a] => exact 2
  | a::b::L => exact 1+Count L


--Let X⊆ M and z∈ M. An X-dash-factorization of z is given by an x∈ X and k∈ ℕ such that k dashes of x = z.
structure dash_factor (X:Set M)(z:M) where
  k:Nat
  x:X
  dash_k_eq_x: dash_k k x.1 = z

--Let X⊆ M. The set generated by X under the dash operation is the set of all x^k where x∈ X.
structure dash_gen (X:Set M) where
  Gset:Set M
  Gfactor (z:Gset): dash_factor X z


--Let X⊆ M. The composite set generated by X under the dash operation is the set of all x^k where x∈ X and k is positive.
structure dash_gen_pos (X:Set M) where
  Gset:Set M
  Gfactor (z:Gset): dash_factor X z
  Gfactor_pos (z:Gset):(Gfactor z).k>0


-- def dash_gen_X (X:Set M):Set M:= by
--   intro x
--   exact ∃ ( y : X),  ∃ (k:Nat) , dash_k y.1 k = x

-- structure dash_gen_X1 (X:Set M) where
--   gen_set:Set M
--   gen_prop: ∀ x:M, ∃ ( y : X),  ∃ (k:Nat) , dash_k y.1 k = x





--A dash basis is a set X which uniquely generates M
--Defintion includes 1∈ M. This is not a good defintion, since this gives a contradiction
structure dash_basis1 (X:Set M) where
  to_factor (z:M): dash_factor X z
  unique (z:M) (f:dash_factor X z):f=to_factor z

def factor1 (X:Set M)(basis: dash_basis1 X):dash_factor X 1:=basis.to_factor 1

def factor2 (X:Set M)(basis: dash_basis1 X):dash_factor X 1:=by
  have h :=factor1 X basis
  rcases h with ⟨k, x, eq ⟩
  constructor
  case k=> exact k+1
  case x=> exact x
  case dash_k_eq_x=>
    rw[dash_dash_k ]
    rw[eq]
    exact DMon.unit_dash



theorem factor1_neq_factor2 (X:Set M)(basis: dash_basis1 X):factor1 X basis ≠ factor2 X basis:= by
  intro h
  have h1:(factor2 X basis).k=(factor1 X basis).k+1:= by
    rw[factor2]
  have h2:(factor2 X basis).k=(factor1 X basis).k:= by
    rw[h]
  linarith

theorem factor1_eq_factor2 (X:Set M)(basis: dash_basis1 X):factor1 X basis = factor2 X basis:= by
  have h1:=basis.unique 1 (factor1 X basis)
  have h2:=basis.unique 1 (factor2 X basis)
  rw[h1]
  rw[h2]

theorem basis_false (X:Set M)(basis: dash_basis1 X):False:= by
  have h:=  factor1_neq_factor2 X basis
  have nh:= factor1_eq_factor2 X basis
  exact h nh

-- structure dash_basis (X:Set M) where
--   X_pos : X⊆ DMon_pos
--   rep_y (x:M): X
--   rep_k (x: M):Nat
--   eq (x:M): dash_k (rep_y x).1 (rep_k x) = x

structure dash_basis (X:Set M) where
  to_factor (z:M): dash_factor X z
  unique (z:M_pos) (f:dash_factor X z):f=to_factor z.1


def dash_up_exists (X:Set M){basis:dash_basis X}(f: X→ N):M→ N:=by
  intro x
  have factor:=basis.to_factor x
  have k := factor.k
  have y:= factor.x
  exact dash_k k (f y)

@[ext]
structure DMonHom (M N:Type _)[stM:DMon M][stN:DMon N] where
  toFun : M→ N
  map_dash:∀ x:M, stN.dash (toFun x) = toFun (stM.dash x)

def dash_up_exists_DMonHom (N:Type _)[stN:DMon N](X:Set M){basis:dash_basis X}(f: X→ N):DMonHom M N where
  toFun:= by
    intro x
    have factor:=basis.to_factor x
    have k := factor.k
    have y:= factor.x
    exact dash_k k (f y)
  map_dash:=by
    intro x
    have factor:=basis.to_factor x
    simp
    sorry

theorem map_dash_k (f:DMonHom M N)(k:Nat)(x:M):dash_k k (f.toFun x)=f.toFun (dash_k k x):= by
  induction' k with k hk
  case zero=>
    apply dash_zero
  case succ=>
    rw[dash_dash_k]
    rw[dash_dash_k]
    rw[hk]
    rw[f.map_dash]




theorem up_unique (M N:Type _)[stM: DMon M][stN:DMon N](X:Set M){basis:dash_basis X}(f g: DMonHom M N)(hfg: ∀ x:X, f.toFun x=g.toFun x):f=g:=by
  ext x
  have f:=basis.to_factor x
  rcases f with ⟨k, y, y_dash⟩
  rw[← y_dash]
  rw[← map_dash_k]
  rw[← map_dash_k]
  rw[hfg]





def listCoe {X:Set M}(u:List X):List M:=by
  induction' u with head _ tail_out
  case nil => exact []
  case cons => exact head.1::tail_out


def mul_m (u:List M):M:= by
  induction' u with head _ tail_out
  case nil => exact 1
  case cons => exact head* tail_out

theorem mul_m_nil :mul_m []= 1:= rfl

theorem mul_m_one (x:M) : mul_m [x]=x:= by
  simp only [mul_m, mul_one]

theorem mul_m_two (x y:M): mul_m [x,y]=x*y:= by
  simp only [mul_m, mul_one]

structure mul_factor (X:Set M)(z: M) where
  u:List X
  prop: mul_m (listCoe u) = z

structure mul_basis (X:Set M) where
  to_factor (z:M): mul_factor X z
  unique (z:M_pos) (f:mul_factor X z.1):f=to_factor z.1

def Map_list {M N:Type _}(f:M→ N)(u:List M):List N:= by
  induction' u with head _ tail_out
  case nil=> exact []
  case cons=> exact (f head)::tail_out


def mul_up_exists (N:Type _)[stN:DMon N](X:Set M){basis:mul_basis X}(f: X→ N):M→ N:=by
  intro x
  have factor:=basis.to_factor x
  rcases factor with ⟨u, _⟩
  have fu:=Map_list f u
  exact mul_m fu

#check MonoidHom
