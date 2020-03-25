import topology.metric_space.basic

variables {X : Type*} [metric_space X]
variables {Y : Type*} [metric_space Y]

/- Definition of continuity on metric spaces -/
def is_continuous_at (f : X → Y) (a : X) := ∀ ε > 0, ∃ δ > 0, ∀ x : X, dist x a < δ → dist (f x) (f a) < ε
def is_continuous (f : X → Y) := ∀ a : X, is_continuous_at f a

/- Definition of uniform continuity on metric spaces -/
def is_unif_continuous (f : X → Y) := ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → dist (f x) (f y) < ε

/- Notion of boundedness on metric spaces -/
def is_bounded (S : set X) := S = ∅ ∨ ∃ x₀ ∈ S, ∃ k : ℝ, ∀ x ∈ S, dist x x₀ ≤ k
