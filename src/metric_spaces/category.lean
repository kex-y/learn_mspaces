import topology.metric_space.basic
import category_theory.concrete_category

universe u

open category_theory

def Metric_space := bundled metric_space.{u}

variables {X Y Z : Metric_space.{u}}
instance has_dist_bundled : metric_space X.1 := X.2

/- Definition of continuity on metric spaces -/
def is_continuous_at (f : X.1 → Y.1) (a : X.1) := ∀ ε > 0, ∃ δ > 0, ∀ x : X.1, dist x a < δ → dist (f x) (f a) < ε
def is_continuous (f : X.1 → Y.1) := ∀ a : X.1, is_continuous_at f a

/- Defining continuous functions as morphisms of metric spaces -/
structure metric_morph (X Y : Metric_space) :=
(to_fun : X.1 → Y.1)
(is_contin : is_continuous to_fun)

/- Identity metric morphism -/
def id_metric_morph (X : Metric_space) : metric_morph X X := 
{   to_fun := λ x : X.1, x,
    is_contin := λ a ε hε, 
    ⟨ε, hε, λ x, by simp⟩
}

/- The composition of two continuous functions is continuous -/
lemma comp_continuous {f : X.1 → Y.1} {g : Y.1 → Z.1} (h₁ : is_continuous f) (h₂ : is_continuous g) : 
is_continuous (g ∘ f) := λ a ε hε, 
    let ⟨δ₁, hg₁, hg₂⟩ := h₂ (f a) ε hε in
    let ⟨δ₂, hf₁, hf₂⟩ := h₁ a δ₁ hg₁ in
    ⟨δ₂, hf₁, λ x hx, hg₂ (f x) (hf₂ x hx)⟩

/- Two metric_morph are the same if their underlying functiosn are the same -/
@[ext] lemma ext {f g : metric_morph X Y} (h : ∀ x : X.1, f.to_fun x = g.to_fun x) : f = g :=
by cases f; cases g; congr; exact funext h

lemma id_comp {f : metric_morph X Y} : f.to_fun ∘ (id_metric_morph X).to_fun = f.to_fun :=
by ext; rw [function.comp_app, show (id_metric_morph X).to_fun x = x, by refl]

lemma comp_id {f : metric_morph X Y} : (id_metric_morph Y).to_fun ∘ f.to_fun = f.to_fun :=
by ext; rw [function.comp_app, show (id_metric_morph Y).to_fun (f.to_fun x) = f.to_fun x, by refl]

/- The category of metric spaces -/
instance category_metric_space : category (Metric_space) := 
{   hom := metric_morph,
    id := id_metric_morph,
    comp := λ X Y Z f g, by {split, from comp_continuous f.is_contin g.is_contin},
    id_comp' := λ X Y f, by ext; simp [id_comp],
    comp_id' := λ X Y f, by ext; simp [comp_id],
    assoc' := λ W X Y Z f g h, by simp
}
 
/- Definition of isometry on metric spaces -/
def is_isometry (f : X.1 → Y.1) := ∀ x y : X.1, dist x y = dist (f x) (f y)

/- Defining isometries as morphisms of metric spaces -/
structure metric_morph2 (X Y : Metric_space) :=
(to_fun : X.1 → Y.1)
(is_iso : is_isometry to_fun)

/- Identity metric morphism -/
def id_metric_morph2 (X : Metric_space) : metric_morph2 X X := 
{   to_fun := λ x : X.1, x,
    is_iso := λ x y, rfl
}

/- The composition of two isometries is continuous -/
lemma comp_isometry {f : X.1 → Y.1} {g : Y.1 → Z.1} (h₁ : is_isometry f) (h₂ : is_isometry g) : 
is_isometry (g ∘ f) := λ x y, by simp [h₁ x y, h₂ (f x) (f y)]

/- Two metric_morph2 are the same if their underlying functiosn are the same -/
@[ext] lemma ext2 {f g : metric_morph2 X Y} (h : ∀ x : X.1, f.to_fun x = g.to_fun x) : f = g :=
by cases f; cases g; congr; exact funext h

lemma id_comp2 {f : metric_morph2 X Y} : f.to_fun ∘ (id_metric_morph2 X).to_fun = f.to_fun :=
by ext; rw [function.comp_app, show (id_metric_morph2 X).to_fun x = x, by refl]

lemma comp_id2 {f : metric_morph2 X Y} : (id_metric_morph2 Y).to_fun ∘ f.to_fun = f.to_fun :=
by ext; rw [function.comp_app, show (id_metric_morph2 Y).to_fun (f.to_fun x) = f.to_fun x, by refl]

/- The category of metric spaces with isometries -/
instance category_metric_space2 : category (Metric_space) := 
{   hom := metric_morph2,
    id := id_metric_morph2,
    comp := λ X Y Z f g, by {split, from comp_isometry f.is_iso g.is_iso},
    id_comp' := λ X Y f, by ext; simp [id_comp2],
    comp_id' := λ X Y f, by ext; simp [comp_id2],
    assoc' := λ W X Y Z f g h, by simp
}