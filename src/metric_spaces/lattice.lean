import metric_spaces.theorems

/--
In this file we showed that the `closed_set` form a Galois insertion with
`Closure` being its Galois connection, and with that, we conclude `closed_set`
form a `complete_lattice`.

- `closed_set` is defined to be a closed subset of a metric space
- `Closure` is defined to be a `closed_set` with `closure' _` as its carrier
-/

variables {X : Type*} [metric_space X]
variables {Y : Type*} [metric_space Y]

open definitions set

namespace closed_set

open open_closed_sets.closure'

/- Defining the structure of a closed set -/
structure closed_set (X : Type*) [metric_space X] :=
(carrier : set X)
(is_closed : is_closed' carrier) 

instance : has_coe (closed_set X) (set X) := ⟨closed_set.carrier⟩

def Closure (S : set X) : closed_set X := 
{   carrier := closure' S,
    is_closed := closure_closed S }

theorem ext' {S T : closed_set X} (h : (S : set X) = T) : S = T :=
by cases S; cases T; congr'

/- Closed sets form a partial order -/
instance : partial_order (closed_set X) :=
{.. partial_order.lift (coe : closed_set X → set X) (λ a b, ext') (by apply_instance)}

/- The closure of a closed_set is itself -/
lemma Closure_self (T : closed_set X) : T = Closure T.1 :=
ext' $ show ↑T = closure' T.carrier, by {rw closure_self, refl, from T.2}

/- Closed sets form a Galois insertion -/
def gi : @galois_insertion (set X) (closed_set X) _ _ Closure closed_set.carrier := 
{   choice := λ S h, Closure S,
    gc := λ S T, 
        ⟨λ h, set.subset.trans subset_closure' h, λ h, by rw Closure_self T; from closure_mono' h⟩,
    le_l_u := λ S, subset_closure',
    choice_eq := λ _ _, rfl }

/- Closed sets form a complete lattice -/
instance : complete_lattice (closed_set X) := 
{ .. galois_insertion.lift_complete_lattice gi}

end closed_set