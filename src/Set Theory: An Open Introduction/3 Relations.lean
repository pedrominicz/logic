import tactic

section

parameters {α : Type} {x y : α} {r : α → α → Prop}

def equivalence_class (x : α) : set α := {y | r x y}

-- Proposition 3.12. If R ⊆ A^2 is an equivalence relation, then Rxy iff
-- [x]_R = [y]_R.
lemma proposition_3_12 (hr : equivalence r) :
  r x y ↔ equivalence_class x = equivalence_class y :=
begin
  rcases hr with ⟨hr₁, hr₂, hr₃⟩,
  split,
  { intro h,
    ext z,
    split,
    { intro hz,
      change r x z at hz,
      change r y z,
      specialize hr₂ h,
      specialize hr₃ hr₂ hz,
      assumption },
    { intro hz,
      change r y z at hz,
      change r x z,
      specialize hr₂ hz,
      specialize hr₃ h hz,
      assumption } },
  { intro h,
    have : r x = r y, from h,
    rw this,
    exact hr₁ y }
end

-- Definition 3.9 (Asymmetry). A relation R ⊆ A^2 is called asymmetric if for
-- no pair x, y ∈ A we have both Rxy and Ryx.
def asymmetric (r : α → α → Prop) := ∀ ⦃x y⦄, ¬(r x y ∧ r y x)

#print irreflexive
#print transitive

-- Definition 3.21 (Strict order). A strict order is a relation which is
-- irreflexive, asymmetric, and transitive.
def strict_order (r : α → α → Prop) := irreflexive r ∧ asymmetric r ∧ transitive r

#check @relation.refl_gen

def partial_order' (r : α → α → Prop) := reflexive r ∧ transitive r ∧ anti_symmetric r

-- Proposition 3.25. If R is a strict order on A, then R^+ = R ∪ Id_A is a
-- partial order. Moreover, if R is total, then R^+ is a linear order.
lemma proposition_3_25_a (h : strict_order r) : partial_order' (relation.refl_gen r) :=
begin
  rcases h with ⟨h₁, h₂, h₃⟩,
  refine ⟨_, _, _⟩,
  { intro x, refl },
  { intros x y z,
    intros hr₁ hr₂,
    cases hr₁ with hr₁ hr₁; cases hr₂ with hr₂ hr₂,
    { refl },
    { exact relation.refl_gen.single hr₂ },
    { exact relation.refl_gen.single hr₁ },
    { have : r x z, by tidy,
      exact relation.refl_gen.single this } },
  { intros x y,
    intros hr₁ hr₂,
    by_contra,
    have hr₁ : r x y,
    { cases hr₁ with hr₁ hr₁,
      { exfalso,
        apply h,
        refl },
      { assumption } },
    have hr₂ : r y x,
    { cases hr₂ with hr₂ hr₂,
      { exfalso,
        apply h,
        refl },
      { assumption } },
    exact h₂ ⟨hr₁, hr₂⟩ }
end

-- Definition 3.7 (Connectivity). A relation R ⊆ A2 is connected if for all
-- x, y ∈ A, if x ≠ y, then either Rxy or Ryx.
def connected (r : α → α → Prop) := ∀ ⦃x y⦄, x ≠ y → r x y ∨ r y x

-- Definition 3.24 (Total order). A strict order which is also connected is
-- called a total order. This is also sometimes called a strict linear order.
def total_order (r : α → α → Prop) := strict_order r ∧ connected r

-- Definition 3.16 (Linear order). A partial order which is also connected is
-- called a total order or linear order.
def linear_order' (r : α → α → Prop) := partial_order' r ∧ connected r

-- Moreover, if R is total, then R^+ is a linear order.
lemma proposition_3_25_b (h : total_order r) : linear_order' (relation.refl_gen r) :=
begin
  split,
  { exact proposition_3_25_a h.1 },
  { intros x y,
    intro hxy,
    have : r x y ∨ r y x, from h.2 hxy,
    cases this,
    { left,
      exact relation.refl_gen.single this },
    { right,
      exact relation.refl_gen.single this } }
end

end