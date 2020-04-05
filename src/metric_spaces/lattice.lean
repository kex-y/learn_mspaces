import metric_spaces.theorems

variables {X : Type*} [metric_space X]
variables {Y : Type*} [metric_space Y]

open definitions

namespace closed_set

/- Defining the structure of a closed set -/
structure closed_set (X : Type*) [metric_space X] :=
(carrier : set X)
(is_closed : is_closed' carrier) 

instance : has_coe (closed_set X) (set X) := ⟨closed_set.carrier⟩

open open_closed_sets

/- The closure of a set is also closed -/
lemma closure_closed (S : set X) : is_closed' $ closure' S :=
Inter_closed_is_closed $ λ T, Inter_closed_is_closed $ λ h₁,
Inter_closed_is_closed $ λ h₂, h₂

/- The closure of a closure is itself -/
theorem closure_closure' (S : set X) : closure' (closure' S) = closure' S := 
closure_self $ closure_closed S

/- The closure of a smaller set is smaller than closure -/
theorem closure_mono' {S T : set X} (h : S ⊆ T) : closure' S ⊆ closure' T :=
begin
    iterate 2 {rw with_limit_points_is_closure},
    suffices : limit_points S ⊆ limit_points T,
        rw set.union_subset_iff,
        split, refine set.subset.trans h _, simp,
            refine set.subset.trans this _, simp,
    from limit_points_le h
end

theorem monotone_closure' : monotone $ @closure' X _ := λ _ _, closure_mono'

/- A set is smaller than its closure -/
theorem subset_closure' (S : set X) : S ⊆ closure' S :=
set.subset_Inter $ λ _, set.subset_Inter $ λ h, set.subset_Inter $ λ _, h

def Closure (S : set X) : closed_set X := 
{ carrier := closure' S,
  is_closed := closure_closed S }

theorem ext' {S T : closed_set X} (h : (S : set X) = T) : S = T :=
by cases S; cases T; congr'

open set

instance : partial_order (closed_set X) :=
{.. partial_order.lift (coe : closed_set X → set X) (λ a b, ext') (by apply_instance)}

/- The closure of a closed_set is itself -/
lemma Closure_self (T : closed_set X) : T = Closure T.1 :=
ext' $ show ↑T = closure' T.carrier, by {rw closure_self, refl, from T.2}

/- Closed sets form a Galois insertion -/
def gi : @galois_insertion (set X) (closed_set X) _ _ Closure closed_set.carrier := 
{ choice := λ S h, Closure S,
  gc := λ S T, 
    ⟨λ h, set.subset.trans (subset_closure' S) h, λ h, by rw Closure_self T; from closure_mono' h⟩,
  le_l_u := λ S, subset_closure' S,
  choice_eq := λ _ _, rfl }

/- Closed sets form a complete lattice -/
instance : complete_lattice (closed_set X) := 
{ .. galois_insertion.lift_complete_lattice gi}

end closed_set