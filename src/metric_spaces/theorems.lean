import metric_spaces.definitions

variables {X : Type*}[metric_space X]

/- Definition of a metric space
class metric_space (α : Type u) extends has_dist α : Type u :=
(dist_self : ∀ x : α, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
[... Some stuff that doesn't matter ...]
-/

-- Some of the theorems are already in mathlib so we will work in hidden
namespace hidden
/- The metric of any two elements of a metric space is non-negative -/
theorem metric_nonneg : ∀ x y : X, 0 ≤ dist x y := λ x y,
begin
    suffices : 0 ≤ dist y x + dist x y - dist y y,
        rw [dist_self, dist_comm, sub_zero] at this,
        linarith,
    linarith [dist_triangle y x y]
end

namespace continuity

variables {Y : Type*}[metric_space Y]
variables {Z : Type*}[metric_space Z]
variables {f : X → Y} {g : Y → Z}

/- The composition of two continuous functions is continuous -/
theorem comp_continuous (h₁ : is_continuous f) (h₂ : is_continuous g) : 
is_continuous (g ∘ f) := λ a ε hε, 
    let ⟨δ₁, hg₁, hg₂⟩ := h₂ (f a) ε hε in
    let ⟨δ₂, hf₁, hf₂⟩ := h₁ a δ₁ hg₁ in
    ⟨δ₂, hf₁, λ x hx, hg₂ (f x) (hf₂ x hx)⟩

theorem func_add_continuous (f g : X → ℝ) : is_continuous (f + g) := sorry

end continuity
end hidden