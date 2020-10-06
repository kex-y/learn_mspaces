import topology.basic

namespace definitions

open set

variables {X : Type*} [topological_space X] 
variables {Y : Type*} [topological_space Y]

def is_continuous (f : X → Y) : Prop :=
  ∀ U : set Y, is_open U → is_open (f ⁻¹' U)

def is_continuous_at (f : X → Y) (x : X) : Prop :=
  ∀ U : set Y, f x ∈ U → is_open U → is_open (f ⁻¹' U)

structure topological_space_equiv 
(X Y) [topological_space X] [topological_space Y] extends X ≃ Y :=
(contin     : is_continuous to_fun)
(inv_contin : is_continuous inv_fun)
notation X ` ≃* ` Y := topological_space_equiv X Y

/- We define the notion of being closed and the closure similar to 
how we defined it for metric spaces: its complemnet is open and the 
smallest closed set containing the set. We will use mathlib's 
definition -/

/- We also define limit points for topological spaces similarly -/
def limit_points (U : set X) :=
  {x : X | ∀ U' : set X, is_open U' → x ∈ U' → U' ∩ U ≠ ∅}

/- The interior of a set U is defined to be the uninon of all open 
sets smaller than U thats open -/

/- A point x is an interior point of a set U if there exist an open 
set Nₓ, x ∈ Nₓ and Nₓ ⊆ U -/
def interior_points (U : set X) :=
  {x : X | ∃ (U' : set X) (h₀ : is_open U') (h₁ : U' ⊆ U), x ∈ U'}

/- We consider convergence in topological spaces. We say as sequence 
xₙ : ℕ → X converges to some x ∈ X iff. for all open U containing x, 
there exists some N ∈ ℕ, for all n ≥ N, xₙ ∈ U -/
def converge_to (x : ℕ → X) (l : X) := 
  ∀ (U : set X) (h : is_open U), l ∈ U → ∃ N : ℕ, ∀ n ≥ N, x n ∈ U

/- Creating a coercion between the a set of A to a set of X 
where A ⊆ X. -/
instance {A : set X} : has_coe (set A) (set X) :=
⟨λ S, subtype.val '' S⟩

/- We create the natrual definition of the subspace of a topological 
space with the subspace topology -/
instance {A : set X} : topological_space A := 
{ is_open := λ U, ∃ (V : set X) (H : is_open V), A ∩ V = U,
  is_open_univ := 
    begin
      refine ⟨univ, is_open_univ, _⟩,
      rw [univ_subtype, inter_univ],
      ext, split; intro ha,
      have : (⟨x, ha⟩ : A) ∈ ⋃ (x : X) (h : x ∈ A), ({⟨x, h⟩} : set A),
        finish,
      refine ⟨_, this, rfl⟩,
      rcases ha with ⟨x, hx, rfl⟩,
      rw mem_Union at hx,
      cases hx with i hi,
      rw mem_Union at hi,
      cases hi with ha hx,
      rw mem_singleton_iff at hx,
      rw hx, exact ha,
    end,
  is_open_inter := sorry,
  is_open_sUnion := sorry }

/- We define the natural mapping between a subspace to the whole space
(inclusion map) -/
def inclusion_map (A : set X) : A → X := λ x, x
notation `𝒾 ` A := inclusion_map A

/- A topological space is called Hausdorff iff. for all x, y in X, 
there exists U, V ⊆ X, such that x ∈ U, y ∈ V and U V are disjoint -/
def is_Hausdorff (X : Type*) [topological_space X] := 
∀ x y : X, x ≠ y → ∃ (U V : set X) (hU : is_open U) 
  (hV : is_open V) (hx : x ∈ U) (hy : y ∈ V), U ∩ V = ∅

attribute [reducible] limit_points interior_points is_Hausdorff

end definitions