import topology.definitions metric_spaces.theorems

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

variables {X : Type*} [topological_space X]

open definitions set

/- We'll prove the axiom left out in Lean's version - ∅ is open -/
theorem empty_is_open : is_open (∅ : set X) :=
begin
  rw ←sUnion_empty, apply is_open_sUnion, intros _ h,
  exfalso, exact h
end

/-
If X is a topological space, then U ⊆ X is open iff for all x ∈ U,
there exists an open set Nₓ with x ∈ Nₓ and Nₓ ⊆ U
-/
-- The forward direction is trivial enough
lemma has_smaller_of_open {U : set X} (h : is_open U) : 
∀ x ∈ U, ∃ (Nₓ : set X) (h₀ : is_open Nₓ), x ∈ Nₓ ∧ Nₓ ⊆ U := λ x hx,
⟨U, h, hx, subset.refl U⟩

/- The backwards direction is easy once we see that we can make U 
  from the suitable union of Nₓ  -/
lemma open_of_has_smaller {U : set X} 
(h : ∀ x ∈ U, ∃ (Nₓ : set X) (h₀ : is_open Nₓ), x ∈ Nₓ ∧ Nₓ ⊆ U) :
is_open U :=
begin
  choose f hfo hf using h,
  have : is_open ⋃ (x ∈ U), f x H := is_open_Union (λ x, is_open_Union $ λ h, hfo x h), 
  convert this, ext, 
  refine ⟨λ h, mem_Union.2 ⟨x, mem_Union.2 ⟨h, (hf x h).1⟩⟩, λ h, _⟩,
    cases mem_Union.1 h with y hy, cases mem_Union.1 hy with hy₀ hy₁,
    exact (hf y hy₀).2 hy₁
end

theorem open_iff_has_smaller {U : set X} : is_open U ↔ 
∀ x ∈ U, ∃ (Nₓ : set X) (h₀ : is_open Nₓ), x ∈ Nₓ ∧ Nₓ ⊆ U :=
⟨has_smaller_of_open, open_of_has_smaller⟩