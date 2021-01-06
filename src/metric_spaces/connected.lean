import metric_spaces.basic

noncomputable theory
local attribute [instance] classical.prop_decidable

open set definitions

variables {α X : Type*} [metric_space X]
variables {Y : Type*}   [metric_space Y]

namespace connected

/- We have some equivalent definitions for connected sets
- X is connected
↔ ∃ f : X → {0, 1}, f is continuous then f is a constant function
↔ the only sets that are both open and closed are X and ∅ -/

/- Since working with the set {0, 1} is a hassle, we will define the 
inductive type binary containing terms: val_a and val_b -/
inductive binary : Type* | val_a : binary | val_b : binary

lemma binary_cases (y : binary) : y = binary.val_a ∨ y = binary.val_b :=
by cases y; finish

/- We need to show that binary form a metric space so we will define 
a discrete metric on binary -/
private def binary_metric : binary → binary → ℝ :=
  λ x y, if (x = y) then 0 else 1

/- We need to prove all the metric axioms -/
private lemma binary_dist_self : ∀ x, binary_metric x x = 0 :=
λ x, by unfold binary_metric; simp

private lemma binary_eq_of_dist_eq_zero : 
  ∀ x y, binary_metric x y = 0 → x = y := λ x y h,
begin
  cases x; cases y;
  try { refl <|>
      {	exfalso, apply @zero_ne_one ℝ _, rw ←h,
        unfold binary_metric, simp } }
end

private lemma binary_dist_comm : 
  ∀ x y, binary_metric x y = binary_metric y x := λ x y,
by cases x; cases y; try { unfold binary_metric, simp }; refl

private lemma binary_dist_triangle :
  ∀ x y z, binary_metric x z ≤ binary_metric x y + binary_metric y z := λ x y z,
begin
  cases x; cases y; cases z;
  try {	unfold binary_metric, simp };
  norm_num
end

instance metric_space_of_binary : metric_space binary := 
{ dist := binary_metric, 
  dist_self := binary_dist_self,
  eq_of_dist_eq_zero := binary_eq_of_dist_eq_zero,
  dist_comm := binary_dist_comm,
  dist_triangle := binary_dist_triangle }

lemma notempty {S : set α} (h : S ≠ ∅) : ∃ s : α, s ∈ S := 
begin
  by_contra hs, push_neg at hs,
  exact (push_neg.not_eq _ _).1 h (set.eq_empty_iff_forall_not_mem.2 hs)
end

private def aux_fun (U : set X) : X → binary :=  
  λ x, if (x ∈ U) then binary.val_a else binary.val_b

private lemma aux_fun_eq_val_a {U : set X} : ∀ u ∈ U, aux_fun U u = binary.val_a :=
λ u hu, by unfold aux_fun; split_ifs; refl	

private lemma aux_fun_eq_val_b {U : set X} : ∀ u ∉ U, aux_fun U u = binary.val_b :=
λ u hu, by unfold aux_fun; split_ifs; refl	

lemma disj_if_inter_empty {U V : set X} (hdisj : U ∩ V = ∅) : 
∀ v ∈ V, v ∉ U := λ v hv hu, by rw [←(mem_empty_eq v), ←hdisj]; exact ⟨hu, hv⟩

private lemma aux_fun_is_continuous {U V : set X} 
(hU₀ : is_open' U) (hV₀ : is_open' V) (hU₁ : U ≠ ∅) (hV₁ : V ≠ ∅) 
(hdisj : U ∩ V = ∅) (hcover : U ∪ V = univ) : is_continuous (aux_fun U) := 
begin
  intros x ε hε, have := mem_univ x, 
  rw ←hcover at this, cases this,
    {	rcases hU₀ _ this with ⟨δ, hδ₀, hδ₁⟩,
      refine ⟨δ, hδ₀, λ y hy, _⟩, convert hε,
      have hyU : y ∈ U, apply hδ₁, rw dist_comm at hy, exact hy,
      rw aux_fun_eq_val_a _ this, 
      rw aux_fun_eq_val_a _ hyU,
      exact dist_self _ },
    { rcases hV₀ _ this with ⟨δ, hδ₀, hδ₁⟩,
      refine ⟨δ, hδ₀, λ y hy, _⟩, convert hε,
      have hyV : y ∈ V, apply hδ₁, rw dist_comm at hy, exact hy,
      rw aux_fun_eq_val_b x (disj_if_inter_empty hdisj _ this),
      rw aux_fun_eq_val_b y (disj_if_inter_empty hdisj _ hyV),
      exact dist_self _	}
end

lemma connected_of_const_func (h : ∀ f : X → binary, is_continuous f → 
  (f = λ _, binary.val_a) ∨ (f = λ _, binary.val_b)) : is_connected' X :=
begin
  rintro ⟨U, V, hU₀, hV₀, hU₁, hV₁, hdisj, hcover⟩,
  have := h (aux_fun U) _,
  cases notempty hU₁ with u hu,	cases notempty hV₁ with v hv,
  apply (show binary.val_a ≠ binary.val_b, by finish),
  cases this; rw function.funext_iff at this, 
    { rw ←(this v), 
      show (λ (x : X), ite (x ∈ U) binary.val_a binary.val_b) v = binary.val_b,
      simp, split_ifs with hvU, 
      exact eq_empty_iff_forall_not_mem.1 hdisj v ⟨hvU, hv⟩, refl },
    { rw ←(this u),
      show binary.val_a = (λ (x : X), ite (x ∈ U) binary.val_a binary.val_b) u,
      simp, split_ifs, refl },
  exact aux_fun_is_continuous hU₀ hV₀ hU₁ hV₁ hdisj hcover
end

private lemma binary_singleton_is_open (x : binary) : 
  is_open' ({ x } : set binary) := 
begin
  intros y hy, 
  refine ⟨1, (by norm_num), _⟩,
  rw mem_singleton_iff.1 hy, intros z hz,
  simp [dist, binary_metric] at hz,
  split_ifs at hz,
    { exact h ▸ mem_singleton _ },
    { linarith }
end

private lemma not_constant_a {f : X → binary} : 
  (¬ f = λ x, binary.val_a) → ∃ x, f x = binary.val_b := λ hf,
begin
  by_contra h, push_neg at h,
  apply hf, ext, have := h x, cases f x; finish,
end

private lemma not_constant_b {f : X → binary} : 
  (¬ f = λ x, binary.val_b) → ∃ x, f x = binary.val_a := λ hf,
begin
  by_contra h, push_neg at h,
  apply hf, ext, have := h x, cases f x; finish,
end

lemma const_func_of_connected (h : is_connected' X) : 
∀ f : X → binary, is_continuous f → 
  (f = λ _, binary.val_a) ∨ (f = λ _, binary.val_b) :=
begin
  by_contra hf, push_neg at hf,
  rcases hf with ⟨f, hf₀, hf₁, hf₂⟩, apply h, 
  refine ⟨f ⁻¹' { binary.val_a }, f ⁻¹' { binary.val_b }, _, _, _⟩;
  try { exact open_closed.contin_to_preimg_open _ 
    (binary_singleton_is_open _) hf₀ },
  cases not_constant_a hf₁ with b hb',
  cases not_constant_b hf₂ with a ha',
  refine ⟨_, _, _, _⟩,
  { intro ha, apply not_mem_empty a, rwa ←ha },
  { intro hb, apply not_mem_empty b, rwa ←hb },
  { by_contra hpre, cases notempty hpre with x hx,
    apply (show binary.val_a ≠ binary.val_b, by finish),
    rw ←(mem_singleton_iff.1 hx.1),
    exact mem_singleton_iff.1 hx.2 },
  ext, split; intro _,
    { exact mem_univ _ },
    { suffices : f x = binary.val_a ∨ f x = binary.val_b,
        cases this, left, exact this, right, exact this,
      cases f x; finish }  
end

theorem connected_iff_const_func : is_connected' X ↔ ∀ f : X → binary, 
  is_continuous f → (f = λ _, binary.val_a) ∨ (f = λ _, binary.val_b) :=
⟨λ h , const_func_of_connected h, λ h, connected_of_const_func h⟩

/- Furthermore, X is connected is equivalent to the only open sets in X are 
univ and ∅ -/
lemma compl_nempty_of_not_univ {S : set X} : ¬S = univ → Sᶜ ≠ ∅ := 
λ h hn, h $ by rw ← compl_univ at hn; exact compl_inj_iff.mp hn

lemma eq_union_sub {S T : set X} (h : S = S ∪ T) : T ⊆ S := 
by intros t ht; rw h; right; assumption

lemma sub_disj_eq_empty {S T : set X} (h : T ⊆ S) (hinter : S ∩ T = ∅) : T = ∅ :=
by rw ←hinter; ext; exact ⟨λ hx, ⟨h hx, hx⟩, λ hx, hx.2 ⟩

lemma compl_eq_disj_cover {S T : set X} 
(hinter : S ∩ T = ∅) (hcover : S ∪ T = univ) : Sᶜ = T :=
begin
  ext, split; intro hx,
    { have := mem_univ x, 
      rw ←hcover at this,
      cases this; finish },
    { intro hS,
      rw [←mem_empty_eq x, ←hinter],
      exact ⟨hS, hx⟩ }
end

lemma open_and_closed_of_connected (h : is_connected' X) 
(S : set X) (hS : is_open' S ∧ is_closed' S) : S = ∅ ∨ S = univ :=
begin
  cases hS with hS₀ hS₁,
  by_contra hp, push_neg at hp, apply h,
  cases notempty hp.1 with x hx,
  exact ⟨S, Sᶜ, hS₀, hS₁, hp.1, compl_nempty_of_not_univ hp.2, by finish⟩
end

lemma connected_of_open_and_closed 
(h : ∀ S : set X, is_open' S ∧ is_closed' S → S = ∅ ∨ S = univ) :
is_connected' X :=
begin
  rintro ⟨U, V, hU₀, hV₀, hU₁, hV₁, hinter, hcover⟩,
  cases h U ⟨hU₀, _⟩ with hempt huniv,
    { contradiction },
    { rw ←hcover at huniv,
      refine hV₁ (sub_disj_eq_empty (eq_union_sub huniv) hinter) },
  unfold is_closed',
  rwa compl_eq_disj_cover hinter hcover
end

theorem connected_iff_open_and_closed : is_connected' X ↔ 
  ∀ S : set X, is_open' S ∧ is_closed' S → S = ∅ ∨ S = univ :=
⟨λ h, open_and_closed_of_connected h, λ h, connected_of_open_and_closed h⟩

lemma image_factorization_contin {U : set X} {f : X → Y} 
  (hf : is_continuous f) : is_continuous $ image_factorization f U :=
begin
  unfold image_factorization,
  intros u ε hε,
  rcases hf u.1 ε hε with ⟨δ, hδ₀, hδ₁⟩,
  exact ⟨δ, hδ₀, λ x hx, by simp; exact hδ₁ x.1 hx⟩
end

/- The image of a connected space is connected -/
theorem image_of_connected_is_connected {U : set X} {f : X → Y}
  (hU : is_connected' U) (hf : is_continuous f) : is_connected' $ f '' U :=
begin
  rw connected_iff_const_func at *, intros g hg,
  have := hU (g ∘ image_factorization f U) (continuity.comp_continuous _ hg),
  cases this, left, swap, right,
  all_goals { try
    { ext y, rcases (mem_image f U y.1).1 y.2 with ⟨x, hx₀, hx₁⟩,
      rw (show g y = (g ∘ image_factorization f U) ⟨x, hx₀⟩, 
          by simp [function.comp, image_factorization, hx₁]),
      simp [this] } },
  exact image_factorization_contin hf
end

/- ARGGG! This is messy :( -/
theorem between_closure_is_connected_of_connected {U : set X} 
  (hU : is_connected' U) : ∀ V, U ⊆ V ∧ V ⊆ closure' U → is_connected' V :=
begin
  rintros V ⟨hV₀, hV₁⟩,
  rw connected_iff_const_func at *,
  rw open_closed.closure'.with_limit_points_is_closure U at hV₁,
  intros f hf, let g : U → binary := λ u, f ⟨u.1, hV₀ u.2⟩,
  cases hU g (open_closed.subset_contin_of_contin hV₀ f g hf rfl),
  left, swap, right,
  all_goals { ext, cases hV₁ x.2 with hinU hlp,
    { try { rw [show binary.val_a = g ⟨x.1, hinU⟩, by simp [h]] 
        <|> rw [show binary.val_b = g ⟨x.1, hinU⟩, by simp [h]] }, 
      show f x = (λ (u : U), f ⟨u.1, hV₀ u.2⟩) ⟨x.val, hinU⟩, simp },
    { choose s h₀ h₁ h₂ using λ n : ℕ, hlp (1 / (n + 1) : ℝ) nat.one_div_pos_of_nat,
      have ha : (λ n, g $ ⟨s n, h₀ n⟩) ⇒ f x := λ ε' hε', 
        by { rcases hf x ε' hε' with ⟨δ, hδ₀, hδ₁⟩,
            cases exists_nat_gt (1 / δ) with N hN,
            refine ⟨N, λ n hn, _⟩, rw dist_comm,
            refine hδ₁ ⟨s n, _⟩ (lt_trans _ ((one_div_lt _ hδ₀).2 hN)),
            rw dist_comm, refine lt_of_lt_of_le (h₂ n) _, 
            rw [one_div_le, one_div_one_div],
            norm_cast, exact le_add_right hn, 
            norm_cast, exact nat.succ_pos n, 
            
            rw one_div_pos, all_goals 
              { refine lt_trans (inv_pos.2 hδ₀) _, 
                rw inv_eq_one_div, exact hN } },
      refine convergence.limit_unique _ _ ha _,
      rw h, simp [convergence.const_converge] } }
end

/- A direct corollary is that the closure of a connected set is connected -/
theorem closure_is_connected_of_connected {U : set X} 
  (hU : is_connected' U) : is_connected' $ closure' U := 
between_closure_is_connected_of_connected hU _ 
  ⟨open_closed.closure'.subset_closure', subset.refl $ closure' U⟩

end connected