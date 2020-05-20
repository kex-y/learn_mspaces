import metric_spaces.definitions

noncomputable theory

open set

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
		by { rw abs_eq_zero, intro h, linarith [h] },
	dist_comm := λ x y, show abs (x - y) = abs (y - x), from abs_sub x y,
	dist_triangle := λ x y z, show abs (x - z) ≤ abs (x - y) + abs (y - z),
		by { convert abs_add (x - y) (y - z), linarith }
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
		by { unfold metric_example, split_ifs, all_goals {finish} },
	dist_comm := λ x y, show metric_example X x y = metric_example X y x,
		by { unfold metric_example, split_ifs, all_goals {finish} },
	dist_triangle := λ x y z, show metric_example X x z ≤ metric_example X x y + metric_example X y z,
	begin
		unfold metric_example,
		split_ifs, all_goals {try {norm_num}},
		apply h, rwa [h_1, h_2]
	end
}

end examples