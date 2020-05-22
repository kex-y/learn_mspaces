import topology.basic

namespace definitions

variables {X : Type*} 

/- We define the notion of order on topologies (coarser, finer).
Let 𝒯₁, 𝒯₂ be topologies on the same set X. If 𝒯₁ ⊆ 𝒯₂ then 𝒯₁ is 
said to be coarser than 𝒯₂ and 𝒯₂ is said to be finer than 𝒯₁ -/

-- Does this even make any sense?
/-
instance : has_le (topological_space X) := 
{ le := λ 𝒯₁ 𝒯₂, ∀ s : set X, 𝒯₁.is_open s → 𝒯₂.is_open s }
-/

variables {Y : Type*} [topological_space X] [topological_space Y]

def is_continuous (f : X → Y) : Prop :=
  ∀ U : set Y, is_open U → is_open (f ⁻¹' U)

def is_continuous_at (f : X → Y) (x : X) : Prop :=
  ∀ U : set Y, f x ∈ U → is_open U → is_open (f ⁻¹' U)

open function

structure topological_space_equiv 
(X Y) [topological_space X] [topological_space Y] extends X ≃ Y :=
(contin     : is_continuous to_fun)
(inv_contin : is_continuous inv_fun)
notation X ` ≃* ` Y := topological_space_equiv X Y

end definitions