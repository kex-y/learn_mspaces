import topology.definitions

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
variables {Y : Type*} [topological_space Y] 
variables {Z : Type*} [topological_space Z]


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

namespace mapping

open function equiv

/- The composition of two continuous functions is also continuous -/
theorem comp_contin {f : X → Y} {g : Y → Z} 
(hf : is_continuous f) (hg : is_continuous g) : 
is_continuous (g ∘ f) := λ U hU, hf _ (hg _ hU)

/- A function is continuous iff. it is continuous at every point -/
lemma contin_at_all_of_contin {f : X → Y} (h : is_continuous f) : 
∀ x : X, is_continuous_at f x := λ _ U _ hU, h U hU

lemma contin_of_contin_at_all {f : X → Y} (h : ∀ x : X, is_continuous_at f x) : 
is_continuous f := λ U hU,
begin
  cases (classical.em $ f ⁻¹' U = ∅) with hempt hnempt,
    { rw hempt, exact empty_is_open },
    { cases ne_empty_iff_nonempty.1 hnempt with x hx,
      exact h _ _ (mem_preimage.1 hx) hU }
end

theorem contin_iff_contin_at_all (f : X → Y) : 
is_continuous f ↔ ∀ x : X, is_continuous_at f x :=
  ⟨contin_at_all_of_contin, contin_of_contin_at_all⟩

/- 
A bijection of sets f : X → Y gives a homeomorphism of topological 
spaces X → Y iff. it induces a bijection 𝒯(X) → 𝒯(Y) : U → f(U)
-/
lemma topo_contin_biject_of_equiv (hequiv : X ≃* Y) : 
∃ (f : X → Y) (h₀ : bijective f) (h₁ : is_continuous f), 
∀ U : set X, is_open U → is_open (f '' U) := 
begin
  refine ⟨hequiv.to_fun, _, hequiv.contin, λ U hU, _⟩,
  refine ⟨hequiv.left_inv.injective, hequiv.right_inv.surjective⟩,
  convert hequiv.inv_contin U hU, 
  ext, split; intro hx,
    { rcases (mem_image _ _ _).1 hx with ⟨y, hy₀, hy₁⟩,
      rw ←hy₁, simp [hy₀] },
    { refine ⟨(hequiv.to_equiv.symm) x, hx, _⟩, simp }
end

lemma preimage_eq_inv {f : X → Y} {U : set X} (hf : bijective f) : 
f '' U = (of_bijective hf).inv_fun ⁻¹' U :=
begin
  ext, split; intro hx,
    { rcases (mem_image _ _ _).1 hx with ⟨y, hy₀, hy₁⟩,
      rw [←hy₁, mem_preimage], 
      have : left_inverse (of_bijective hf).inv_fun f := 
        (of_bijective hf).left_inv, 
      rwa this y },
    { refine ⟨(of_bijective hf).inv_fun x, hx, _⟩,
      have : right_inverse (of_bijective hf).inv_fun f := 
        (of_bijective hf).right_inv,
      rwa this x
    }
end

noncomputable lemma equiv_of_topo_contin_biject {f : X → Y} (hf₀ : bijective f) 
(hf₁ : ∀ U : set X, is_open U → is_open (f '' U)) (hf₂ : is_continuous f) : X ≃* Y :=
{ contin := hf₂,
  inv_contin := λ U hU, by rw ←preimage_eq_inv hf₀; exact hf₁ U hU,
  .. of_bijective hf₀ }

end mapping