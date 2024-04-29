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


universe u v w

#check List.up_List


variable {S: Type _}

variable {i n m: Nat}

namespace DashedMonoid

--This file should have basic definitions/results about Dashed Monoids. Definitions: DMon, Dash, k-dashes, m-multiplication, GenSets wrt dash and mul, Ind wrt dash



--Dashed-monoid "DMon" is a monoid with unary operation "dash" such that 1' = 1
class DMon (M:Type _) extends Monoid M where
  dash : M → M
  unit_dash : dash 1 = 1


variable {M:Type _}[stM:DMon M]
variable {N:Type _}[stN:DMon N]


--A Monoid can be a dashed monoid with dash equla to id
def Mon_to_DMon :DMon M where
  dash := id
  unit_dash:= rfl

instance Nat_DMon:DMon Nat where
  dash := id
  unit_dash := by exact rfl

--A group can be a dashed monoid with dash equal to inv.
def Group_to_DMon (G:Type u)[st:Group G]: DMon G:= by
  constructor
  case dash => exact st.inv
  case unit_dash => exact inv_one

--Underlying set of dashed monoid without the unit
def M_pos :Set M:= Set.univ \ {1}


--Taking dash of an element k times
def dash_k (k:Nat)(x:M):M:=by
  induction' k with _ hk
  case zero => exact x
  case succ => exact stM.dash hk

--Taking zero dashes is same as id
theorem dash_zero (x:M):dash_k 0 x = x:=by
  exact rfl

--Taking one dash is same as dash
theorem dash_one (x:M):dash_k 1 x = stM.dash x:= by
  exact rfl

theorem dash_k_succ (k:Nat)(x:M):dash_k (k+1) x = stM.dash (dash_k k x):= by
  simp only [dash_k, Nat.rec_add_one]




def dash_gen_X (X:Set M):Set M:= by
  intro z
  exact ∃ r:Nat, ∃ x:X, dash_k r x.1 = z


def dash_genP_X (X:Set M):Set M:= by
  intro z
  exact ∃ r:Nat, r>0 ∧ ∃ x:X, dash_k r x.1=z

def is_dash_gen_set (X:Set M):Prop:= dash_gen_X X = M_pos

def is_dash_indp_set (X:Set M):Prop:= ∀  r:Nat, ∀  x:X, ∀  k:Nat, ∀ y:X, (dash_k r x.1 = dash_k k y.1)→ (r=k ∧ x=y)




--Taking mul of an of an list
def mul_L (L:List M):M:=by
  induction' L with head _ tail_h
  case nil => exact 1
  case cons => exact head*tail_h

--Taking zero dashes is same as id
theorem mul_L_zero :mul_L  [] = 1:=by
  exact rfl

--Taking one mul is same as itself
theorem mul_L_one (x:M):mul_L [x] = x:= by
  rw[mul_L]
  simp only [mul_one]

--Taking two mul is same as mul
theorem mul_L_two (x y:M):mul_L [x, y] = x*y:= by
  rw[mul_L]
  simp only [mul_one]

theorem mul_L_succ (x:M)(L: List M):mul_L (x::L) = x*(mul_L L):= by
  rw[mul_L]
  rw[mul_L]

-- def to_List_M (X:Set M)(L:List X):List M:=by
--   induction' L with head _ tail_h
--   case nil=> exact []
--   case cons=> exact (head.1)::tail_h

theorem mul_L_one_to_List_M (X:Set M)(x: X):mul_L (List.up_List  [x]) = x:= by
  have h:List.up_List  [x] = [x.1] :=by
    rw[List.up_List]
  rw[h]
  exact mul_L_one x.1

def mul_gen_X (X:Set M):Set M:= by
  intro z
  exact ∃ L:List X, L≠ [] ∧  mul_L (List.up_List L) = z


def mul_genP_X (X:Set M):Set M:= by
  intro z
  exact ∃ L:List X, (L≠ [] ∧ (∀ a:X, L≠ [a] )) ∧ (mul_L (List.up_List L) = z)

def is_mul_gen_set (X:Set M):Prop:= mul_gen_X X = M_pos

def is_mul_indp_set (X:Set M):Prop:= ∀  L :List X, ∀ P:List X,  L≠ []→ P≠ []→ ((mul_L (List.up_List L)) = (mul_L (List.up_List  P))) → L=P


structure FreeDMon_like (M:Type)[DMon M] where
  basis: Set M
  mul_basis: Set M
  dash_basis:Set M
  mul_basis_is_mul_gen : is_mul_gen_set mul_basis
  mul_basis_is_mul_indp : is_mul_indp_set mul_basis
  dash_basis_is_mul_gen : is_dash_gen_set dash_basis
  dash_basis_is_dash_indp : is_dash_indp_set dash_basis
  basis_cond_mul_basis_union: mul_basis = basis ∪ dash_genP_X dash_basis
  basis_cond_mul_basis_disjoint: basis ∩ dash_genP_X dash_basis = {}
  basis_cond_dash_basis_union: dash_basis = basis ∪ mul_genP_X mul_basis
  basis_cond_dash_basis_disjoint: basis ∩ mul_genP_X mul_basis = {}


def mul_compos (St: FreeDMon_like M):Set M:=dash_genP_X St.dash_basis

--If X is mul indep then gen X = X cup genP x

variable (X:Set M)
lemma mul_gen_eq_cup_genP (mul_idep: is_mul_indp_set X):mul_gen_X X = X ∪ mul_genP_X X:= by
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
        have hL2 := hL.2
        have h:= mul_L_one_to_List_M X a
        rw[h] at hL2
        left
        rw[← hL2]
        exact a.2
    | a::b::L => sorry
  case mpr =>

    sorry

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
    rw[dash_k_succ ]
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
structure DMonHom (M N:Type u)[stM:DMon M][stN:DMon N] where
  toFun : M→ N
  map_dash:∀ x:M, stN.dash (toFun x) = toFun (stM.dash x)

def dash_up_exists_DMonHom (N:Type u)[stN:DMon N](X:Set M){basis:dash_basis X}(f: X→ N):DMonHom M N where
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
    rw[dash_k_succ]
    rw[dash_k_succ]
    rw[hk]
    rw[f.map_dash]




theorem up_unique (M N:Type u)[stM: DMon M][stN:DMon N](X:Set M){basis:dash_basis X}(f g: DMonHom M N)(hfg: ∀ x:X, f.toFun x=g.toFun x):f=g:=by
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

def Map_list {M N:Type u}(f:M→ N)(u:List M):List N:= by
  induction' u with head _ tail_out
  case nil=> exact []
  case cons=> exact (f head)::tail_out


def mul_up_exists (N:Type u)[stN:DMon N](X:Set M){basis:mul_basis X}(f: X→ N):M→ N:=by
  intro x
  have factor:=basis.to_factor x
  rcases factor with ⟨u, _⟩
  have fu:=Map_list f u
  exact mul_m fu

#check MonoidHom
