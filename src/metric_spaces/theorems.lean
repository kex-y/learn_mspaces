import metric_spaces.definitions

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

noncomputable theory

namespace examples

-- Declaring X and element x with type X
inductive X : Type
|   x : X

-- A metric that maps everything to zero is a metric on X
instance metric_space_example_X : metric_space X :=
{   dist := λ _ _, 0,
    dist_self := λ _, rfl,
    eq_of_dist_eq_zero := λ a b _, by {cases a, cases b, refl},
    dist_comm := λ _ _, rfl,
    dist_triangle := λ _ _ _, show (0 : ℝ) ≤ 0 + 0, by linarith
}

-- The absolute function is a metric on ℝ
instance metric_space_example_R : metric_space ℝ :=
{   dist := λ x y, abs (x - y),
    dist_self := λ x, show abs (x - x) = 0, by simp,
    eq_of_dist_eq_zero := λ x y, show abs (x - y) = 0 → x = y,
        by {rw abs_eq_zero, intro h, linarith [h]},
    dist_comm := λ x y, show abs (x - y) = abs (y - x), from abs_sub x y,
    dist_triangle := λ x y z, show abs (x - z) ≤ abs (x - y) + abs (y - z),
        by {convert abs_add (x - y) (y - z), linarith}
}

-- The discrete metric is a metric on any set X
open tactic 
open_locale classical

definition metric_example (X : Type) (x y : X) : ℝ :=
if x = y then 0 else 1

variables {X : Type} {x y : X}

-- Useless tactic just for fun, maybe remove later
private meta def metric_example_tac : tactic unit :=
solve1 $ intros
>> `[unfold metric_example]
>> try `[simp]

instance metric_space_example_discrete : metric_space X :=
{   dist := λ x y, metric_example X x y,
    dist_self := λ x, show metric_example X x x = 0, by metric_example_tac,
    eq_of_dist_eq_zero := λ x y, show metric_example X x y = 0 → x = y,
        by {unfold metric_example, split_ifs, all_goals {finish}},
    dist_comm := λ x y, show metric_example X x y = metric_example X y x,
        by {unfold metric_example, split_ifs, all_goals {finish}},
    dist_triangle := λ x y z, show metric_example X x z ≤ metric_example X x y + metric_example X y z,
    begin
        unfold metric_example,
        split_ifs, all_goals {try {norm_num}},
        apply h, rwa [h_1, h_2]
    end
}

end examples

variables {X : Type*} [metric_space X]

/- The metric of any two elements of a metric space is non-negative -/
theorem metric_nonneg : ∀ x y : X, 0 ≤ dist x y := λ x y,
begin
    suffices : 0 ≤ dist y x + dist x y - dist y y,
        rw [dist_self, dist_comm, sub_zero] at this,
        linarith,
    linarith [dist_triangle y x y]
end

namespace continuity

variables {Y : Type*} [metric_space Y]
variables {Z : Type*} [metric_space Z]
variables {f : X → Y} {g : Y → Z}

/- The composition of two continuous functions is continuous -/
theorem comp_continuous (h₁ : is_continuous f) (h₂ : is_continuous g) : 
is_continuous (g ∘ f) := λ a ε hε, 
    let ⟨δ₁, hg₁, hg₂⟩ := h₂ (f a) ε hε in
    let ⟨δ₂, hf₁, hf₂⟩ := h₁ a δ₁ hg₁ in
    ⟨δ₂, hf₁, λ x hx, hg₂ (f x) (hf₂ x hx)⟩

/- The product of two metric spaces is also a metric space -/
@[priority 20000] instance : metric_space (X × Y) :=
{   dist := λ ⟨x₀, y₀⟩ ⟨x₁, y₁⟩, dist x₀ x₁ + dist y₀ y₁,
    dist_self := λ ⟨x, y⟩, show dist x x + dist y y = 0, by simp,
    eq_of_dist_eq_zero :=
        begin
            rintros ⟨x₀, y₀⟩ ⟨x₁, y₁⟩,
            show dist x₀ x₁ + dist y₀ y₁ = 0 → (x₀, y₀) = (x₁, y₁), intro h,
            suffices : dist x₀ x₁ = 0 ∧ dist y₀ y₁ = 0,
                rwa [eq_of_dist_eq_zero this.left, eq_of_dist_eq_zero this.right],
            split,
            all_goals {linarith [metric_nonneg x₀ x₁, metric_nonneg y₀ y₁, h]}
        end,
    dist_comm := λ ⟨x₀, y₀⟩ ⟨x₁, y₁⟩, 
        show dist x₀ x₁ + dist y₀ y₁ = dist x₁ x₀ + dist y₁ y₀, by simp [dist_comm],
    dist_triangle := λ ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩,
        show dist x₀ x₂ + dist y₀ y₂ ≤ dist x₀ x₁ + dist y₀ y₁ + (dist x₁ x₂ + dist y₁ y₂),
        by linarith [dist_triangle x₀ x₁ x₂, dist_triangle y₀ y₁ y₂]
}

theorem prod_continuous (f g : X → ℝ) (h₁ : is_continuous f) (h₂ : is_continuous g) : 
is_continuous (λ x : X, (f x, g x)) := λ x₀ ε hε,
    let ⟨δ₁, hδ₁, hf⟩ := h₁ x₀ (ε / 2) (half_pos hε) in
    let ⟨δ₂, hδ₂, hg⟩ := h₂ x₀ (ε / 2) (half_pos hε) in
    show ∃ (δ : ℝ), 0 < δ ∧ ∀ (x : X), dist x x₀ < δ → dist (f x) (f x₀) + dist (g x) (g x₀) < ε,
    from ⟨min δ₁ δ₂, by simp; from ⟨hδ₁, hδ₂⟩, λ x hx,
begin
    suffices : dist (f x) (f x₀) < ε / 2 ∧ dist (g x) (g x₀) < ε / 2,
        linarith [this.left, this.right],
    split,
        all_goals {apply hf x <|> apply hg x, apply lt_of_lt_of_le hx},
        from inf_le_left, from inf_le_right
end
⟩

/- TODO: now that we have the product of two metric spaces is also a metric space,
we can show that (+) : ℝ × ℝ → ℝ is a continuous function and this the composition of 
this and two continous functions f, g is also continuous, i.e. f + g is continuous.
-/

end continuity

end hidden