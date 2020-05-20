import topology.metric_space.basic

variables {X : Type*} [metric_space X]
variables {Y : Type*} [metric_space Y]

namespace definitions

/- Definition of continuity on metric spaces -/
def is_continuous_at (f : X → Y) (a : X) := 
  ∀ ε > 0, ∃ δ > 0, ∀ x : X, dist x a < δ → dist (f x) (f a) < ε
def is_continuous (f : X → Y) := ∀ a : X, is_continuous_at f a

/- Definition of uniform continuity on metric spaces -/
def is_unif_continuous (f : X → Y) := 
  ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → dist (f x) (f y) < ε

/- Notion of boundedness on metric spaces -/
def is_bounded (S : set X) := S = ∅ ∨ ∃ x₀ ∈ S, ∃ k : ℝ, ∀ x ∈ S, dist x x₀ ≤ k
    
/- Definition of an open ball -/
def open_ball (x₀ : X) (r : ℝ) := {x : X | dist x₀ x < r}

/- Definition of being open -/
def is_open' (S : set X) := ∀ s ∈ S, ∃ (ε : ℝ) (hε : 0 < ε), open_ball s ε ⊆ S

/- Definition of being closed -/
def is_closed' (S : set X) := is_open' $ -S

/- Definition of the set of limit points -/
def limit_points (S : set X) := 
  {x : X | ∀ (ε : ℝ) (hε : 0 < ε), ∃ (y ∈ S) (h : x ≠ y), y ∈ open_ball x ε}

/- Definition of closure -/
def closure' (S : set X) := ⋂ (T : set X) (h₀ : S ⊆ T) (h₁ : is_closed' T), T

/- Definition of interior -/
def interior' (S : set X) := ⋃ (T : set X) (h₀ : T ⊆ S) (h₀ : is_open' T), T

/- Definition of boundary -/
def boundary (S : set X) := closure' S \ interior' S

attribute [reducible] open_ball limit_points closure' interior' boundary

def converge_to (s : ℕ → X) (x : X) := 
∀ (ε : ℝ) (hε : 0 < ε), ∃ N : ℕ, ∀ (n : ℕ) (hn : N ≤ n), dist x (s n) < ε 
notation s ` ⇒ ` x := converge_to s x

def cauchy (s : ℕ → X) :=
∀ (ε : ℝ) (hε : 0 < ε), ∃ N : ℕ, ∀ (n m : ℕ) (hn : N ≤ n) (hm : N ≤ m), dist (s n) (s m) < ε 

end definitions