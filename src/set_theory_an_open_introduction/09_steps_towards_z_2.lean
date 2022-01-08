import tactic

-- Comments follow [Set Theory: An Open Introduction][1] and, only where
-- specified, [An Introduction To Set Theory][2].
--
-- [1]: https://st.openlogicproject.org/settheory-screen.pdf
-- [2]: https://www.math.toronto.edu/weiss/set_theory.pdf

/-

An Introduction To Set Theory introduces abbreviations for working with
classes. A class is a string of symbols of the form `{x : φ}` where `x`
is a variable and `φ` is a formula. We write:

    x ∈ {y : φ} instead of φ[y / x]
    x = {y : φ} instead of ∀ z, z ∈ x ↔ φ[y / z]
    {x : φ} = y instead of ∀ z, φ[x / z] ↔ z ∈ y
    {x : φ} = {y : ψ} instead of ∀ z, φ[x / z] ↔ ψ[y / z]
    {x : φ} ∈ y instead of ∃ z, z ∈ y ∧ ∀ x, x ∈ z ↔ φ
    {x : φ} ∈ {y : ψ} instead of ∃ z, ψ[y / z] ∧ ∀ x, x ∈ z ↔ φ

where `z` is always fresh, i.e., `z` is neither `x` nor `y` and occurs in
neither `φ` or `ψ`.

Whenever we have a finite number of classes or variables `a₁`, `a₂`, ..., `aₙ`
the notation `{a₁, a₂, ..., aₙ}` is used as an abbreviation for the class:

    {x : x = a₁ ∨ x = a₂ ∨ ... ∨ x = aₙ}

We also abbreviate the following:

    a ∪ b for {x : x ∈ a ∨ x ∈ b}
    a ∩ b for {x : x ∈ a ∧ x ∈ b}
    a \ b for {x : x ∈ a ∧ x ∉ b}
    ⟨a, b⟩ for {{a}, {a, b}}
    a × b for {p : ∃ x y, x ∈ a ∧ y ∈ b ∧ p = ⟨a, b⟩}
    dom(f) for {x : ∃ y, ⟨x, y⟩ ∈ f}
    rng(f) for {y : ∃ x, ⟨x, y⟩ ∈ f}

Examples:

    ¬ ∃ z, z = {x : x ∉ x}
    ¬ ∃ z, ∀ y, y ∈ z ↔ y ∉ y
    ¬ ∃ z, ∀ x, x ∈ z ↔ x ∉ x

    ∀ a, a ∈ {a, b}
    ∀ a, a ∈ {x : x = a ∨ x = b}
    ∀ a, a = a ∨ a = b

    ∃ z, z = ∅
    ∃ z, z = {x : x ≠ x}
    ∃ z, ∀ x, x ∈ z ↔ x ≠ x
    ...
    ∃ z, ∀ x, x ∉ z

    ∀ x y, ∃ z, z = {x, y}
    ∀ x y, ∃ z, z = {w : w = x ∨ w = y}
    ∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y

-/

-- Stages-are-key. Every set is formed at some stage.
--
-- Stages-are-ordered. Stages are ordered: some come before others.
--
-- Stages-accumulate. For any stage S, and for any sets which were formed
-- before stage S: a set is formed at stage S whose members are exactly those
-- sets. Nothing else is formed at stage S.
--
-- Stages-keep-going. There is no last stage.
--
-- Stages-hit-infinity. There is an infinite stage. That is, there is a stage
-- which (a) is not the first stage, and which (b) has some stages before it,
-- but which (c) has no immediate predecessor.

noncomputable theory

axiom Set : Type
axiom mem : Set → Set → Prop
instance : has_mem Set Set := ⟨mem⟩

def subset (A B : Set) := ∀ ⦃x⦄, x ∈ A → x ∈ B
instance : has_subset Set := ⟨subset⟩

theorem russell's_paradox : ¬ ∃ z : Set, ∀ x, x ∈ z ↔ x ∉ x :=
begin
  rintros ⟨z, hz⟩,
  specialize hz z,
  simpa using hz
end

-- Axiom (Extensionality). For any sets A and B: ∀ x (x ∈ A ↔ x ∈ B) → A = B
@[ext] axiom extensionality {A B : Set} (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B

-- The axiom of equality, as presented in An Introduction To Set Theory.
example (a b : Set) (h : a = b) : ∀ x : Set, a ∈ x ↔ b ∈ x :=
by simp [h]

-- The axiom of extensionality, as presented in An Introduction To Set Theory.
lemma ext_iff {A B : Set} : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B :=
⟨λ h, by simp [h], extensionality⟩

-- Axiom (Pairs). For any sets a, b, the set {a, b} exists.
-- ∀ a ∀ b ∃ P ∀ x (x ∈ P ↔ (x = a ∨ x = b))
axiom pairing (a b : Set) : ∃ P : Set, ∀ x, x ∈ P ↔ x = a ∨ x = b

-- https://en.wikipedia.org/wiki/Extension_by_definitions
example (a b : Set) : ∃! P : Set, ∀ x, x ∈ P ↔ x = a ∨ x = b :=
begin
  obtain ⟨P, hP⟩ := pairing a b,
  refine ⟨P, hP, _⟩,
  intros P' hP',
  ext x,
  specialize hP x,
  specialize hP' x,
  rw [hP, hP']
end

-- Given the above we could add the following, making a conservative extension
-- of ZFC.
--axiom pair (a b : Set) : Set
--axiom pair_spec (a b : Set) : ∀ x, x ∈ pair a b ↔ x = a ∨ x = b

example {φ : Set → Prop} {H : ∃ z, φ z} {χ : Prop} (h : ∀ z, φ z → χ) : ∃ z, φ z ∧ χ :=
begin
  obtain ⟨z, hz⟩ := H,
  exact ⟨z, hz, h z hz⟩
end

example {φ : Set → Prop} {χ : Prop} (h : ∃ z, φ z ∧ χ) : ∀ z, φ z → χ :=
begin
  obtain ⟨z, hz, h⟩ := h,
  exact λ _ _, h
end

-- Using the abbreviations defined in An Introduction To Set Theory:
--
--      ∀ a b, ∃ P, P = {a, b}
--      ∀ a b, ∃ P, P = {x : x = a ∨ x = b}
--      ∀ a b, ∃ P, ∀ x, x ∈ P ↔ x = a ∨ x = b
--
example (a b : Set) : ∃ P : Set, ∀ x, x ∈ P ↔ x = a ∨ x = b :=
pairing a b

-- Using the abbreviations defined in An Introduction To Set Theory:
--
--      ∀ a b, ∃ P, P = ⟨a, b⟩
--      ∀ a b, ∃ P, P = {{a}, {a, b}}
--      ∀ a b, ∃ P, P = {x : x = {a} ∨ x = {a, b}}
--      ∀ a b, ∃ P, ∀ x, x ∈ P ↔ x = {a} ∨ x = {a, b}
--      ∀ a b, ∃ P, ∀ x, x ∈ P ↔ x = {y : y = a} ∨ x = {y : y = a ∨ y = b}
--      ∀ a b, ∃ P, ∀ x, x ∈ P ↔ (∀ z, z ∈ x ↔ z = a) ∨ (∀ z, z ∈ x ↔ z = a ∨ z = b)
--
lemma pair (a b : Set) :
  ∃ P : Set, ∀ x, x ∈ P ↔ (∀ z, z ∈ x ↔ z = a) ∨ (∀ z, z ∈ x ↔ z = a ∨ z = b) :=
begin
  obtain ⟨P₁, hP₁⟩ := pairing a a,
  simp only [or_self] at hP₁,
  obtain ⟨P₂, hP₂⟩ := pairing a b,
  obtain ⟨P, hP⟩ := pairing P₁ P₂,
  use P,
  intro x,
  rw hP x,
  clear hP,
  split,
  { rintro (rfl | rfl),
    { left, assumption },
    { right, assumption } },
  { rintro (h | h),
    { left, ext y, rw hP₁ y, exact h y },
    { right, ext y, rw hP₂ y, exact h y } }
end

-- Using the abbreviations defined in An Introduction To Set Theory:
--
--      ∀ a₁ a₂ b₁ b₂, ⟨a₁, b₁⟩ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ = b₂
--      ∀ a₁ a₂ b₁ b₂, {{a₁}, {a₁, b₁}} = {{a₂}, {a₂, b₂}} ↔ a₁ = a₂ ∧ b₁ = b₂
--      ∀ a₁ a₂ b₁ b₂, {x : x = {a₁} ∨ x = {a₁, b₁}} = {y : y = {a₂} ∨ y = {a₂, b₂}} ↔ a₁ = a₂ ∧ b₁ = b₂
--      ∀ a₁ a₂ b₁ b₂, (∀ z, z = {a₁} ∨ z = {a₁, b₁}} ↔ z = {a₂} ∨ z = {a₂, b₂}) ↔ a₁ = a₂ ∧ b₁ = b₂
--      ∀ a₁ a₂ b₁ b₂, (∀ z, z = {w : w = a₁} ∨ z = {w : w = a₁ ∨ w = b₁}} ↔ z = {w : w = a₂} ∨ z = {w : w = a₂ ∨ w = b₂}) ↔ a₁ = a₂ ∧ b₁ = b₂
--      ∀ a₁ a₂ b₁ b₂, (∀ z, (∀ w, w ∈ z ↔ w = a₁) ∨ (∀ w, w ∈ z ↔ w = a₁ ∨ w = b₁) ↔ (∀ w, w ∈ z ↔ w = a₂) ∨ (∀ w, w ∈ z ↔ w = a₂ ∨ w = b₂)) ↔ a₁ = a₂ ∧ b₁ = b₂
--
lemma fst_eq_fst_of_pair_eq_pair {a₁ a₂ b₁ b₂ : Set}
  (h : ∀ z : Set, (∀ w, w ∈ z ↔ w = a₁) ∨ (∀ w, w ∈ z ↔ w = a₁ ∨ w = b₁) ↔
                  (∀ w, w ∈ z ↔ w = a₂) ∨ (∀ w, w ∈ z ↔ w = a₂ ∨ w = b₂)) : a₁ = a₂ :=
begin
  obtain ⟨P₁, hP₁⟩ := pairing a₁ a₁,
  obtain ⟨P₂, hP₂⟩ := pairing a₂ a₂,
  have h₁ := h P₁,
  have h₂ := h P₂,
  finish
end

lemma snd_eq_snd_of_pair_eq_pair {a₁ a₂ b₁ b₂ : Set}
  (h : ∀ z : Set, (∀ w, w ∈ z ↔ w = a₁) ∨ (∀ w, w ∈ z ↔ w = a₁ ∨ w = b₁) ↔
                  (∀ w, w ∈ z ↔ w = a₂) ∨ (∀ w, w ∈ z ↔ w = a₂ ∨ w = b₂)) : b₁ = b₂ :=
begin
  obtain rfl := fst_eq_fst_of_pair_eq_pair h,
  rename a₁ a,
  obtain ⟨P₁, hP₁⟩ := pairing a b₁,
  obtain ⟨P₂, hP₂⟩ := pairing a b₂,
  have h₁ := h P₁, simp [hP₁] at h₁, clear hP₁ P₁,
  have h₂ := h P₂, simp [hP₂] at h₂, clear hP₂ P₂,
  clear h,
  cases h₁; cases h₂,
  { rw [h₁, h₂] },
  { tidy },
  { tidy },
  { specialize h₁ b₁, simp at h₁,
    specialize h₂ b₂, simp at h₂,
    cases h₁; cases h₂; tidy }
end

example {a₁ a₂ b₁ b₂ : Set} :
  (∀ z : Set, (∀ w, w ∈ z ↔ w = a₁) ∨ (∀ w, w ∈ z ↔ w = a₁ ∨ w = b₁) ↔
              (∀ w, w ∈ z ↔ w = a₂) ∨ (∀ w, w ∈ z ↔ w = a₂ ∨ w = b₂)) ↔ a₁ = a₂ ∧ b₁ = b₂ :=
begin
  split; intro h,
  { simp [fst_eq_fst_of_pair_eq_pair h, snd_eq_snd_of_pair_eq_pair h] },
  { simp [h] }
end