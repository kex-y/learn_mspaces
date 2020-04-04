import metric_spaces.theorems

variables {X : Type*} [metric_space X]
variables {Y : Type*} [metric_space Y]

open definitions

/- Defining the structure of a closed set -/
structure closed_set (X : Type*) [metric_space X] :=
(carrier : set X)
(is_closed : is_closed' carrier) 

instance : has_coe (closed_set X) (set X) := ⟨closed_set.carrier⟩
instance : has_le (closed_set X) := ⟨λ α β, (α : set X) ⊆ (β : set X)⟩
instance : has_lt (closed_set X) := ⟨λ α β, (α : set X) ⊂ (β : set X)⟩

open open_closed_sets

/- The union and intersect of two closed sets are closed -/
lemma inter_two_open_is_open {U₀ U₁ : set X} 
(h₀ : is_open' U₀) (h₁ : is_open' U₁) : is_open' (U₀ ∩ U₁) := λ s ⟨hs₀, hs₁⟩,
    let ⟨ε₀, hε₀, hε₀'⟩ := h₀ s hs₀ in
    let ⟨ε₁, hε₁, hε₁'⟩ := h₁ s hs₁ in
    let ε := min ε₀ ε₁ in
    ⟨ε, by simp [hε₀, hε₁],
        begin
            rw set.subset_inter_iff, split,
                {refine set.subset.trans _ hε₀',
                simp, intros _ h _, assumption
                },
                refine set.subset.trans _ hε₁', simp
        end
    ⟩

lemma union_two_open_is_open {U₀ U₁ : set X}
(h₀ : is_open' U₀) (h₁ : is_open' U₁) : is_open' (U₀ ∪ U₁) := λ s hs,
or.elim hs
    (λ hs', let ⟨ε, hε, hε'⟩ := h₀ s hs' in
        ⟨ε, hε, set.subset.trans hε' (set.subset_union_left U₀ U₁)⟩)
    (λ hs', let ⟨ε, hε, hε'⟩ := h₁ s hs' in
        ⟨ε, hε, set.subset.trans hε' (set.subset_union_right U₀ U₁)⟩)

theorem inter_closed_is_closed {U₀ U₁ : set X}
(h₀ : is_closed' U₀) (h₁ : is_closed' U₁) : is_closed' (U₀ ∩ U₁) := 
begin
    unfold is_closed' at *, rw set.compl_inter, from union_two_open_is_open h₀ h₁
end

theorem union_closed_is_closed {U₀ U₁ : set X}
(h₀ : is_closed' U₀) (h₁ : is_closed' U₁) : is_closed' (U₀ ∪ U₁) := 
begin
    unfold is_closed' at *, rw set.compl_union, from inter_two_open_is_open h₀ h₁
end

def sup (U₀ U₁ : closed_set X) : closed_set X := 
{ carrier := (U₀ : set X) ∪ (U₁ : set X),
  is_closed := union_closed_is_closed U₀.2 U₁.2 }

def inf (U₀ U₁ : closed_set X) : closed_set X := 
{ carrier := (U₀ : set X) ∩ (U₁ : set X),
  is_closed := inter_closed_is_closed U₀.2 U₁.2 }

instance : has_sup (closed_set X) := ⟨sup⟩
instance : has_inf (closed_set X) := ⟨inf⟩

/- The closure of a set is also closed -/
lemma closure_closed (S : set X) : is_closed' $ closure' S := sorry

/- The closure of a closure is itself -/
theorem closure_closure' (S : set X) : closure' (closure' S) = closure' S := closure_self $ closure_closed S

/- The closure of a smaller set is smaller than closure -/
theorem closure_mono' {S T : set X} (h : S ⊆ T) : closure' S ⊆ closure' T := sorry

def Closure (S : closed_set X) : closed_set X := 
{ carrier := closure' S,
  is_closed := closure_closed S }

instance : lattice (closed_set X) := 
{ sup := sup,
  le := (≤),
  lt := (<),
  le_refl := by finish,
  le_trans := λ _ _ _ h₀ h₁, set.subset.trans h₀ h₁,
  lt_iff_le_not_le := sorry,
  le_antisymm := sorry,
  le_sup_left := sorry,
  le_sup_right := sorry,
  sup_le := sorry,
  inf := sorry,
  inf_le_left := sorry,
  inf_le_right := sorry,
  le_inf := sorry }