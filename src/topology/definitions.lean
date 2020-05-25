import topology.basic

namespace definitions

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

/- A topological space is called Hausdorff iff. for all x, y in X, 
there exists U, V ⊆ X, such that x ∈ U, y ∈ V and U V are disjoint -/
def is_Hausdorff (X : Type*) [topological_space X] := 
∀ x y : X, x ≠ y → ∃ (U V : set X) (hU : is_open U) 
  (hV : is_open V) (hx : x ∈ U) (hy : y ∈ V), U ∩ V = ∅

attribute [reducible] limit_points interior_points is_Hausdorff

end definitions