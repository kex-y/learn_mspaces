import topology.basic

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
(is_open       : set α → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))
-/