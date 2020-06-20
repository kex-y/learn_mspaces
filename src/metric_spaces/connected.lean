import metric_spaces.basic

noncomputable theory
local attribute [instance] classical.prop_decidable

open set definitions

variables {α X : Type*} [metric_space X]

namespace connected

/- We have some equivalent definitions for connected sets
- X is connected
↔ ∃ f : X → {0, 1}, f is continuous then f is a constant function
↔ the only sets that are both open and closed are X and ∅ -/

/- Since working with the set {0, 1} is a hassle, we will define the 
inductive type binary containing terms: val_a and val_b -/
inductive binary : Type* | val_a : binary | val_b : binary

/- We need to show that binary form a metric space -/
private def binary_metric : binary → binary → ℝ :=
  λ x y, if (x = y) then 0 else 1

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

instance metric_space_of_zero_one : metric_space binary := 
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
  try { exact open_closed_sets.contin_to_preimg_open _ 
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
      cases f x; finish
    }  
end

theorem connected_iff_const_func : is_connected' X ↔ ∀ f : X → binary, is_continuous f → 
  (f = λ _, binary.val_a) ∨ (f = λ _, binary.val_b) :=
⟨λ h , const_func_of_connected h, λ h, connected_of_const_func h⟩

end connected