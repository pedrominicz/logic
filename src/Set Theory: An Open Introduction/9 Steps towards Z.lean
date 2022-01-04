import tactic

variable {α : Type}

-- Stages-are-key. Every set is formed at some stage.
--
-- Stages-are-ordered. Stages are ordered: some come before others.
--
-- Stages-accumulate. For any stage S, and for any sets which were formed
-- before stage S: a set is formed at stage S whose members are exactly those
-- sets. Nothing else is formed at stage S.

#print notation ⋂₀

example : ⋂₀ (∅ : set (set α)) = set.univ :=
begin
  unfold set.sInter,
  unfold Inf,
  ext,
  simp only [forall_false_left, set.mem_empty_eq, forall_const, set.set_of_true],
end

-- Stages-keep-going. There is no last stage.
--
-- Stages-hit-infinity. There is an infinite stage. That is, there is a stage
-- which (a) is not the first stage, and which (b) has some stages before it,
-- but which (c) has no immediate predecessor.

noncomputable theory

axiom Set : Type

#check @has_mem
#check @has_subset
#print notation ∈
#print notation ⊆

axiom mem : Set → Set → Prop

instance : has_mem Set Set := ⟨mem⟩

def subset (A B : Set) :=
∀ ⦃x⦄, x ∈ A → x ∈ B

instance : has_subset Set := ⟨subset⟩

-- Axiom (Extensionality). For any sets A and B: ∀ x (x ∈ A ↔ x ∈ B) → A = B
@[ext] axiom extensionality (A B : Set) (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B

-- Theorem 8.1 (Russell’s Paradox). There is no set R = {x : x ∉ x}
theorem russell's_paradox : ¬ ∃ R : Set, ∀ x, x ∈ R ↔ x ∉ x :=
begin
  rintro ⟨R, hR⟩,
  specialize hR R,
  simpa using hR
end

-- no (ZFC) axioms
#print axioms russell's_paradox

#print notation ↔
#print notation ∧

#check @classical.some
#check @classical.some_spec

-- Axiom (Scheme of Separation). For every formula φ(x) this is an axiom: for
-- any A, the set {x ∈ A : φ(x)} exists.
axiom separation (φ : Set → Prop) (A : Set) : Set
axiom separation_spec (φ : Set → Prop) (A : Set) : ∀ x, x ∈ separation φ A ↔ x ∈ A ∧ φ x

-- Theorem 9.1. There is no universal set, i.e., {x : x = x} does not exist.
theorem not_exists_universal_set : ¬ ∃ V : Set, ∀ x, x ∈ V :=
begin
  rintro ⟨V, hV⟩,
  let R := separation (λ x, x ∉ x) V,
  have hR := separation_spec (λ x, x ∉ x) V,
  change ∀ x, x ∈ R ↔ _ ∧ x ∉ x at hR,
  specialize hV R,
  specialize hR R,
  simpa [hV] using hR
end

-- separation
#print axioms not_exists_universal_set

-- Proposition 9.2. If any set exists, then ∅ exists.
lemma proposition_9_2 (A : Set) : ∃ S : Set, ∀ x, x ∉ S :=
begin
  let S := separation (λ x, false) A,
  have hS := separation_spec (λ x, false) A,
  change ∀ x, x ∈ S ↔ _ ∧ false at hS,
  use S,
  intros x hx,
  specialize hS x,
  simpa using hS
end

#check @has_sdiff.sdiff
#print notation \

-- Proposition 9.3. A \ B exists for any sets A and B
lemma proposition_9_3 (A B : Set) : ∃ S : Set, ∀ x, x ∈ S ↔ x ∈ A ∧ x ∉ B :=
⟨separation _ _, separation_spec _ _⟩

instance : has_sdiff Set :=
⟨λ A B, separation (λ x, x ∉ B) A⟩

#print notation ⋂₀

-- Proposition 9.4. If A ≠ ∅, then ⋂︁ A = {x : (∀ y ∈ A) x ∈ y} exists.
lemma proposition_9_4 (A c : Set) (hc : c ∈ A) :
  ∃ S : Set, ∀ x, x ∈ S ↔ (∀ y, y ∈ A → x ∈ y) :=
begin
  let S := separation (λ x, ∀ y, y ∈ A → x ∈ y) c,
  have hS := separation_spec (λ x, ∀ y, y ∈ A → x ∈ y) c,
  change ∀ x, x ∈ S ↔ _ ∧ ∀ y, y ∈ A → x ∈ y at hS,
  use S,
  intro x,
  specialize hS x,
  rw [hS, and_iff_right_iff_imp],
  intro h,
  specialize h c,
  specialize h hc,
  assumption
end

-- Axiom (Union). For any set A, the set ⋃︁ A = {x : (∃ b ∈ A) x ∈ b} exists.
-- ∀ A ∃ U ∀ x (x ∈ U ↔ (∃ b ∈ A) x ∈ b)
axiom union (A : Set) : Set
axiom union_spec (A : Set) : ∀ x, x ∈ union A ↔ ∃ b ∈ A, x ∈ b

#print notation ↔
#print notation ∨

-- Axiom (Pairs). For any sets a, b, the set {a, b} exists.
-- ∀ a ∀ b ∃ P ∀ x (x ∈ P ↔ (x = a ∨ x = b))
axiom pair (a b : Set) : Set
axiom pair_spec (a b : Set) : ∀ x, x ∈ pair a b ↔ x = a ∨ x = b

-- Axiom (Powersets). For any set A, the set ℘(A) = {x : x ⊆ A} exists.
-- ∀ A ∃ P ∀ x (x ∈ P ↔ (∀ z ∈ x) z ∈ A)
axiom powerset (A : Set) : Set
axiom powerset_spec (A : Set) : ∀ x, x ∈ powerset A ↔ ∀ z, z ∈ x → z ∈ A

-- Axiom (Infinity). There is a set, I, such that ∅ ∈ I and x ∪ {x} ∈ I
-- whenever x ∈ I
-- ∃ I ((∃ o ∈ I) ∀ x x ∉ o ∧
--      (∀ x ∈ I) (∃ s ∈ I) ∀ z (z ∈ s ↔ (z ∈ x ∨ z = x)))
axiom infinity : Set
axiom infinity_spec_zero : ∃ o ∈ infinity, ∀ x, x ∉ o
axiom infinity_spec_succ : ∀ x ∈ infinity, ∃ s ∈ infinity, ∀ z, z ∈ s ↔ z ∈ x ∨ z = x

#print notation ∅

instance : has_emptyc Set := ⟨separation (λ x, false) infinity⟩

lemma empty_spec : ∀ x : Set, x ∉ (∅ : Set) :=
begin
  intros x hx,
  change x ∈ separation _ _ at hx,
  have h := separation_spec (λ x, false) infinity,
  change x ∈ ∅ at hx,
  change ∀ x, x ∈ (∅ : Set) ↔ _ ∧ false at h,
  specialize h x,
  simpa [hx] using h
end

lemma empty_mem_infinity : ∅ ∈ infinity :=
begin
  obtain ⟨o, ho₁, ho₂⟩ := infinity_spec_zero,
  suffices : ∅ = o, by rwa this,
  ext x,
  have h₁ := empty_spec x,
  have h₂ := ho₂ x,
  simp [h₁, h₂]
end