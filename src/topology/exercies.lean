import topology.theorems

/-
A topological space (X, 𝒯) consists of a non-empty set X 
together with a collection 𝒯 of subsets of X that satisfy 
- ∅ ∈ 𝒯, X ∈ 𝒯
- U, V ∈ 𝒯 → U ∩ V ∈ 𝒯 
- Uᵢ ∈ 𝒯 → ⋃ᵢ U ∈ 𝒯
Elements of 𝒯 are called open sets in (X, 𝒯) and 𝒯 is 
called a topology on X.

In Lean this is represented by:

structure topological_space (α : Type u) :=
(is_open        : set α → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀ t ∈ s, is_open t) → is_open (⋃₀ s))
-/

open definitions set

variables {X : Type*} [topological_space X]
variables {Y : Type*} [topological_space Y]

variables {f : X → Y} (hcontin : is_continuous f)

/- In this exercise, we prove that if the closure of U equals the closure of V 
and f is a continuous function, then the closure of f(U) equals the closure of 
f(V) -/

-- We first show that the image of the closure is smaller than the closure of the image
-- This was proven in theorem.lean

-- We then show that the closure of the image of the closure equals the closure of the image
theorem closure_of_map_of_closure_eq_closure_of_map {U : set X} 
(hcontin : is_continuous f) : closure (f '' closure U) = closure (f '' U) := 
le_antisymm 
  (λ x hx U' ⟨hU'₀, hU'₁⟩, 
    hx U' ⟨hU'₀, subset.trans (mapping.map_closure_le_closure_map hcontin) 
      (closed.closure_is_min hU'₁ hU'₀)⟩)
  (closed.closure_mono' $ image_subset f (closed.set_le_closure U))

-- With that, our question becomes trivial
theorem eq_closure_map_closure_eq {U V : set X} (heq : closure U = closure V) 
(hcontin : is_continuous f): 
closure (f '' U) = closure (f '' V) := 
by rw [← closure_of_map_of_closure_eq_closure_of_map hcontin, heq, 
      closure_of_map_of_closure_eq_closure_of_map hcontin]