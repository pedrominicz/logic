import set_theory.cardinal
import tactic

variables {α β : Type}

-- Definition 5.1 (Enumeration, set-theoretic). An enumeration of a set A is a
-- bijection whose range is A and whose domain is either an initial set of
-- natural numbers {0, 1, ..., n} or the entire set of natural numbers ℕ.
--
-- Definition 5.2. A set A is countable iff either A = ∅ or there is an
-- enumeration of A. We say that A is uncountable iff A is not countable.
def countable (α : Type) := ∃ f : α → ℕ, function.injective f

example : countable ℕ := ⟨id, function.injective_id⟩

def countable' (α : Type) := ∃ f : ℕ → α, function.surjective f

noncomputable example : nonempty α → α := nonempty.some

#check @function.inv_fun
#check @function.inv_fun_surjective

-- Problem 5.1. Show that a set A is countable iff either A = ∅ or there is a
-- surjection f : ℕ → A. Show that A is countable iff there is an injection
-- g : A → ℕ.
lemma problem_5_1_a [nonempty α] : countable α → countable' α :=
begin
  rintro ⟨f, hf⟩,
  change ∃ g, function.surjective g,
  let g := function.inv_fun f,
  have hg := function.inv_fun_surjective hf,
  exact ⟨g, hg⟩
end

lemma problem_5_1_b : countable' α → countable α :=
begin
  rintro ⟨f, hf⟩,
  let g := λ x, classical.some (hf x),
  use g,
  intros x y h,
  have := classical.some_spec (hf x),
  rw ←this, clear this,
  have := classical.some_spec (hf y),
  rw ←this, clear this,
  simp only [g] at h,
  rw h
end

lemma countable_iff_countable' [nonempty α] : countable α ↔ countable' α :=
⟨problem_5_1_a, problem_5_1_b⟩

-- Theorem 5.10. ℘(ℕ) is not countable.
theorem theorem_5_10 : ¬countable (set ℕ) :=
begin
  rw countable_iff_countable',
  rintro ⟨f, hf⟩,
  unfold function.surjective at hf,
  let s := {x | x ∉ f x},
  obtain ⟨x, hx⟩ := hf s,
  have : x ∈ s,
  { intro h,
    sorry },
  sorry
end

set_option pp.universes true
#check @cardinal.mk
set_option pp.universes false

prefix # := cardinal.mk

#check @function.inv_fun
#check @function.inv_fun_surjective

-- Theorem 5.16 (Cantor). A ≺ ℘(A), for any set A.
theorem theorem_5_16 : #α < #(set α) :=
begin
  change _ ∧ _,
  split,
  { let f : α → set α := λ x, {x},
    use f,
    intros x y h,
    simpa using h },
  { rintro ⟨f, hf⟩,
    let g := function.inv_fun f,
    have hg := function.inv_fun_surjective hf,
    let s := {x | x ∉ g x},
    obtain ⟨x, hx⟩ := hg s,
    have : x ∈ s ↔ x ∈ g x, by rw ←hx,
    simp only [set.mem_set_of_eq] at this,
    simpa }
end

#check @bit0
#check @bit1

variables (x : α ⊕ β) (f : α → ℕ)

#check @sum.cases_on _ _ (λ _, ℕ) x f

-- Problem 5.3. Show that if A and B are countable, so is A ∪ B.
lemma problem_5_3 (hα : countable α) (hβ : countable β) : countable (α ⊕ β) :=
begin
  obtain ⟨fα, hfα⟩ := hα,
  obtain ⟨fβ, hfβ⟩ := hβ,
  change ∃ f, _,
  let encode : α ⊕ β → ℕ :=
    λ x, @sum.cases_on _ _ (λ _, ℕ) x (bit0 ∘ fα) (bit1 ∘ fβ),
  use encode,
  intros x y h,
  cases x; cases y,
  { rw nat.bit0_eq_bit0 at h,
    rw (hfα h) },
  { simpa [encode] using h },
  { simpa [encode] using h },
  { rw nat.bit1_eq_bit1 at h,
    rw (hfβ h) }
end

-- Problem 5.16. Show that the set of all functions f : ℕ → ℕ is uncountable by
-- an explicit diagonal argument. That is, show that if f_1, f_2, ..., is a
-- list of functions and each f_i : ℕ → ℕ, then there is some g : ℕ → ℕ not on
-- this list.
lemma problem_5_16 : ¬ countable (ℕ → ℕ) :=
begin
  rw countable_iff_countable',
  rintro ⟨f, hf⟩,
  unfold function.surjective at hf,
  let g : ℕ → ℕ := λ x, f x x + 1,
  obtain ⟨x, hx⟩ := hf g,
  suffices : ∃ y, f x y ≠ g y,
  { obtain ⟨y, hy⟩ := this,
    rw hx at hy,
    apply hy,
    refl },
  use x,
  simp
end

-- Problem 5.17. Show that if there is an injective function g : B → A, and B
-- is uncountable, then so is A. Do this by showing how you can use g to turn
-- an enumeration of A into one of B.
lemma problem_5_17 {g : β → α} (hg : function.injective g) (h : ¬ countable β) :
  ¬ countable α :=
begin
  rintro ⟨f, hf⟩,
  apply h,
  clear h,
  change ∃ f, _,
  use f ∘ g,
  exact function.injective.comp hf hg
end

-- Problem 5.25. Show that there cannot be an injection g : ℘(A) → A, for any
-- set A. Hint: Suppose g : ℘(A) → A is injective. Consider
-- D = {g(B) : B ⊆ A and g(B) ∉ B}. Let x = g(D). Use the fact that g is
-- injective to derive a contradiction.
lemma problem_5_25 : ¬ ∃ f : set α → α, function.injective f :=
begin
  rintro ⟨f, hf⟩,
  let s := f <$> {x | f x ∉ x},
  let x := f s,
  change ∀ ⦃x y⦄, f x = f y → x = y at hf,
  sorry
end