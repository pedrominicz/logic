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

example : ⋂₀ (∅ : set (set α)) = λ x, true :=
begin
  unfold set.sInter,
  unfold Inf,
  ext,
  simp only [forall_false_left, set.mem_empty_eq, forall_const, iff_true],
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
axiom extensionality (A B : Set) (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B

-- Theorem 8.1 (Russell’s Paradox). There is no set R = {x : x ∉ x}
theorem russell's_paradox : ¬ ∃ R : Set, ∀ x, x ∈ R ↔ x ∉ x :=
begin
  rintro ⟨R, hR⟩,
  specialize hR R,
  simpa using hR
end

#print notation ↔
#print notation ∧

-- Axiom (Scheme of Separation). For every formula φ(x) this is an axiom: for
-- any A, the set {x ∈ A : φ(x)} exists.
axiom separation (φ : Set → Prop) (A : Set) : ∃ S : Set, ∀ x, x ∈ S ↔ x ∈ A ∧ φ x

-- Theorem 9.1. There is no universal set, i.e., {x : x = x} does not exist.
theorem not_exists_universal_set : ¬ ∃ V : Set, ∀ x, x ∈ V :=
begin
  rintro ⟨V, hV⟩,
  obtain ⟨R, hR⟩ := separation (λ x, x ∉ x) V,
  change ∀ x, _ ↔ _ ∧  x ∉ x at hR,
  specialize hV R,
  specialize hR R,
  simpa [hV] using hR
end

-- separation
#print axioms not_exists_universal_set

-- Proposition 9.2. If any set exists, then ∅ exists.
lemma proposition_9_2 (A : Set) : ∃ S : Set, ∀ x, x ∉ S :=
begin
  obtain ⟨S, hS⟩ := separation (λ x, false) A,
  use S,
  intros x hx,
  specialize hS x,
  simpa using hS
end

#check @has_sdiff.sdiff
#print notation \

-- Proposition 9.3. A \ B exists for any sets A and B
lemma proposition_9_3 (A B : Set) : ∃ S : Set, ∀ x, x ∈ S ↔ x ∈ A ∧ x ∉ B :=
separation _ _

#print notation ⋂₀

-- Proposition 9.4. If A ≠ ∅, then ⋂︁ A = {x : (∀ y ∈ A) x ∈ y} exists.
lemma proposition_9_4 (A : Set) (hA : ∃ c, c ∈ A) :
  ∃ S : Set, ∀ x, x ∈ S ↔ (∀ y, y ∈ A → x ∈ y) :=
begin
  obtain ⟨c, hc⟩ := hA,
  obtain ⟨S, hS⟩ := separation (λ x, ∀ y, y ∈ A → x ∈ y) c,
  change ∀ x, _ ↔ _ ∧ ∀ y, y ∈ A → x ∈ y at hS,
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
axiom union (A : Set) : ∃ U : Set, ∀ x, x ∈ U ↔ ∃ b ∈ A, x ∈ b

#print notation ↔
#print notation ∨

-- Axiom (Pairs). For any sets a, b, the set {a, b} exists.
-- ∀ a ∀ b ∃ P ∀ x (x ∈ P ↔ (x = a ∨ x = b))
axiom pair (a b : Set) : ∃ P : Set, ∀ x, x ∈ P ↔ x = a ∨ x = b