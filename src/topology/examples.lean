import topology.theorems
import data.set.finite

open definitions set

variables {X : Type*}

namespace examples

-- The cofinite topology
def example_topology : topological_space X := 
{ is_open := λ U, U ∈ {∅} ∪ {U' : set X | finite (-U')},
  is_open_univ := 
    by right; rw mem_set_of_eq; convert finite_empty; exact compl_top,
  is_open_inter := λ _ _ hS hT,
    begin
      cases hS, rw mem_singleton_iff.1 hS, simp,
      cases hT, rw mem_singleton_iff.1 hT, simp,
      right, rw mem_set_of_eq at *,
      rw compl_inter, exact finite.union hS hT,
    end,
  is_open_sUnion := λ s hs,
    begin
      cases classical.em (∀ t ∈ s, t = ∅),
        { left, rw mem_singleton_iff,
          ext, split,
            { intro ht, rw mem_sUnion at ht,
              rcases ht with ⟨t, hts, hmemt⟩,
              rw h t hts at hmemt, assumption },
            { intro hf, exfalso, exact hf }
        },
        { push_neg at h,
          rcases h with ⟨t, ht₀, ht₁⟩,
          right, rw [mem_set_of_eq, compl_sUnion],
          cases hs t ht₀, exfalso, exact ht₁ h, 
          rw mem_set_of_eq at h,
          refine finite.subset h (sInter_subset_of_mem $ _),
          rw mem_image, exact ⟨t, ht₀, rfl⟩
        }
    end }

/-
TODO: Add some examples of topological spaces
-/

variables {Y : Type*} [topological_space X] [topological_space Y]

-- The identity map is continuous
example : is_continuous (@id X) := λ _ hU, hU

-- The constant map is continuous
example (y : Y) : is_continuous (λ x : X, y) := λ U hU,
begin
  cases (classical.em $ y ∈ U) with hinU hninU,
    { convert is_open_univ, ext, simp [hinU] },
    { convert is_open_empty, ext, simp [hninU] }
end

end examples