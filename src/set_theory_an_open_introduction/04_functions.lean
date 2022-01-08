import tactic

variables {α β γ : Type} {f : α → β} {g g₁ g₂ : β → α}

-- Problem 4.1. Show that if f : A → B has a left inverse g, then f is
-- injective.
lemma problem_4_1 (h : function.left_inverse g f) : function.injective f :=
begin
  intros x y hxy,
  have : g (f x) = g (f y), from congr_arg g hxy,
  have hx := h x,
  have hy := h y,
  rwa [hx, hy] at this
end

-- Problem 4.2. Show that if f : A → B has a right inverse h, then f is
-- surjective.
lemma problem_4_2 (h : function.right_inverse g f) : function.surjective f :=
begin
  intro y,
  use g y,
  rw h y
end

#check @classical.some
#check @classical.some_spec

-- Problem 4.3. Prove Proposition 4.18. You have to define f^−1, show that it
-- is a function, and show that it is an inverse of f, i.e., f^−1(f(x)) = x and
-- f(f^−1(y)) = y for all x ∈ A and y ∈ B.
--
-- Proposition 4.18. If f : A → B is bijective, there is a function
-- f^−1 : B → A so that for all x ∈ A, f^−1(f(x)) = x and for all y ∈ B,
-- f(f^−1(y)) = y.
lemma proposition_4_18 (h : function.bijective f) :
  ∃ g : β → α, function.left_inverse g f ∧ function.right_inverse g f :=
begin
  obtain ⟨h₁, h₂⟩ := h,
  let g : β → α := λ y, classical.some (h₂ y),
  use g,
  split,
  { intro x,
    simp only [g],
    have := classical.some_spec (h₂ (f x)),
    have := h₁ this,
    assumption },
  { intro y,
    simp only [g],
    have := classical.some_spec (h₂ y),
    assumption }
end

-- Problem 4.4. Prove Proposition 4.19.
--
-- Proposition 4.19. Show that if f : A → B has a left inverse g and a right
-- inverse h, then h = g .
lemma proposition_4_19 (hg₁ : function.left_inverse g₁ f) (hg₂ : function.right_inverse g₂ f) :
  g₁ = g₂ :=
begin
  ext y,
  have h₁ := hg₁ (g₂ y),
  have h₂ := hg₂ y,
  rwa h₂ at h₁
end

-- Problem 4.5. Show that if f : A → B and g : B → C are both injective, then
-- g ◦ f : A → C is injective.
lemma problem_4_5 {g : β → γ} (hf : function.injective f) (hg : function.injective g) :
  function.injective (g ∘ f) :=
begin
  intros x y h,
  change g (f x) = g (f y) at h,
  have := hg h,
  have := hf this,
  assumption
end

-- Problem 4.6. Show that if f : A → B and g : B → C are both surjective, then
-- g ◦ f : A → C is surjective.
lemma problem_4_6 {g : β → γ} (hf : function.surjective f) (hg : function.surjective g) :
  function.surjective (g ∘ f) :=
begin
  intro z,
  obtain ⟨y, hy⟩ := hg z,
  obtain ⟨x, hx⟩ := hf y,
  use x,
  change g (f x) = z,
  rw [hx, hy]
end

def graph (f : α → β) := λ x y, f x = y

def relative_product (r : α → β → Prop) (s : β → γ → Prop) := λ a b, ∃ c, r a c ∧ s c b

-- Problem 4.7. Suppose f : A → B and g : B → C. Show that the graph of g ◦ f
-- is R_f | R_g.
lemma problem_4_7 (f : α → β) (g : β → γ) :
  graph (g ∘ f) = relative_product (graph f) (graph g) :=
begin
  ext x z,
  split,
  { intro h,
    change g (f x) = z at h,
    rwa [relative_product, graph, exists_eq_left'] },
  { intro h,
    rwa [relative_product, graph, exists_eq_left'] at h }
end