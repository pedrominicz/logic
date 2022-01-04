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

-- Theorem 8.1 (Russell’s Paradox). There is no set R = {x : x ∉ x}
theorem russell's_paradox : ¬ ∃ R : Set, ∀ x, x ∈ R ↔ x ∉ x :=
begin
  rintro ⟨R, hR⟩,
  specialize hR R,
  simpa using hR
end

-- no (ZFC) axioms
#print axioms russell's_paradox

-- Axiom (Extensionality). For any sets A and B: ∀ x (x ∈ A ↔ x ∈ B) → A = B
@[ext] axiom extensionality (A B : Set) (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B

#check @set.ext_iff

lemma ext_iff {A B : Set} : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B :=
begin
  have := extensionality A B,
  tidy
end

#print notation ↔
#print notation ∧

#check @classical.some
#check @classical.some_spec

-- Axiom (Scheme of Separation). For every formula φ(x) this is an axiom: for
-- any A, the set {x ∈ A : φ(x)} exists.
axiom separation (φ : Set → Prop) (A : Set) : Set
axiom separation_spec (φ : Set → Prop) (A : Set) : ∀ x, x ∈ separation φ A ↔ x ∈ A ∧ φ x

#check @has_sep

instance : has_sep Set Set := ⟨separation⟩

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
axiom union_spec (A : Set) : ∀ x, x ∈ union A ↔ ∃ b, b ∈ A ∧ x ∈ b

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

lemma empty_spec : ∀ x, x ∉ (∅ : Set) :=
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

--def closed (f : Set → Set) (X : Set) := ∀ x, x ∈ X → f x ∈ X

-- Proposition 9.5. For any sets a and b, the following sets exist:
-- 1. {a}
-- 2. a ∪ b
-- 3. ⟨a,b⟩
instance : has_singleton Set Set := ⟨λ a, pair a a⟩

lemma singleton_spec (a : Set) : ∀ x ∈ ({a} : Set), x = a :=
begin
  intros x hx,
  change x ∈ pair a a at hx,
  have h := pair_spec a a,
  change x ∈ {a} at hx,
  change ∀ x, x ∈ ({a} : Set) ↔ _ at h,
  specialize h x,
  simpa [hx] using h
end

#check @has_union
#check @has_union.union
#print notation ∪

instance : has_union Set := ⟨λ a b, union (pair a b)⟩

lemma union_spec' (a b : Set) : ∀ x, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
begin
  intro x,
  change x ∈ union (pair a b) ↔ _,
  have h := union_spec (pair a b),
  specialize h x,
  rw h,
  clear h,
  have h := pair_spec a b,
  split,
  { rintro ⟨c, hc₁, hc₂⟩,
    specialize h c,
    simp [hc₁] at h,
    cases h,
    { rw ←h,
      left,
      assumption },
    { rw ←h,
      right,
      assumption } },
  { intro hx,
    cases hx,
    { use a,
      specialize h a,
      simp at h,
      simp [h, hx] },
    { use b,
      specialize h b,
      simp at h,
      simp [h, hx] } }
end

#check @has_insert

instance : has_insert Set Set := ⟨λ a b, {a} ∪ b⟩

instance : is_lawful_singleton Set Set :=
⟨begin
  change ∀ x, {x} ∪ ∅ = {x},
  intro x,
  ext y,
  simp [union_spec', empty_spec]
end⟩

example {α : Type} (a b : α) (h : a ∈ ({b} : set α)) : a = b :=
set.mem_singleton_iff.mp h

#check @set.mem_singleton_iff

lemma mem_singleton_iff {a b : Set} : a ∈ ({b} : Set) ↔ a = b :=
begin
  change a ∈ pair b b ↔ _,
  have := pair_spec b b a,
  simp [this]
end

variables {a b c : Set}

#check ({a, b, c} : Set)

variables {a₁ a₂ b₁ b₂ : Set}

#check extensionality
#check set.ext_iff

lemma pair_spec' (a b : Set) : pair a b = {a, b} :=
begin
  ext x,
  have := pair_spec a b x,
  rw this,
  clear this,
  change _ ↔ x ∈ {a} ∪ {b},
  have := union_spec' {a} {b} x,
  rw [this, mem_singleton_iff, mem_singleton_iff]
end

lemma eq_of_eq_singleton (h : {b₁, b₂} = ({a} : Set)) : b₁ = b₂ := 
begin
  have h₁ : b₁ = a,
  { have := ext_iff.mp h b₁,
    rw [←pair_spec', mem_singleton_iff, pair_spec b₁ b₂ b₁] at this,
    simpa using this },
  have h₂ : b₂ = a,
  { have := ext_iff.mp h b₂,
    rw [←pair_spec', mem_singleton_iff, pair_spec b₁ b₂ b₂] at this,
    simpa using this },
  rw [h₁, h₂]
end

def tuple (a b : Set) : Set := pair (pair a a) (pair a b)

#check singleton_spec

example {α : Type} (a b : α) (h : ({a} : set α) = {b}) : a = b :=
by simpa only [set.singleton_eq_singleton_iff] using h

lemma singleton_eq_singleton_iff {a b : Set} : ({a} : Set) = {b} ↔ a = b :=
begin
  split,
  { intro h,
    have : a ∈ {b}, by rw [←h, mem_singleton_iff],
    rwa mem_singleton_iff at this },
  { intro h,
    rw h }
end

lemma fst_eq_fst_of_tuple_eq_tuple (h : tuple a₁ b₁ = tuple a₂ b₂) : a₁ = a₂ :=
begin
  have h' : pair a₂ a₂ ∈ tuple a₁ b₁,
  { rw h,
    have := pair_spec (pair a₂ a₂) (pair a₂ b₂) (pair a₂ a₂),
    simpa using this },
  unfold tuple at h',
  have := pair_spec (pair a₁ a₁) (pair a₁ b₁) (pair a₂ a₂),
  simp [h'] at this,
  clear h h',
  cases this,
  { change {a₂} = {a₁} at this,
    rw ←singleton_eq_singleton_iff,
    symmetry,
    assumption },
  { suffices h : a₁ = b₁,
    { subst h,
      change {a₂} = {a₁} at this,
      rw ←singleton_eq_singleton_iff,
      symmetry,
      assumption },
    change {a₂} = _ at this,
    have h := pair_spec' a₁ b₁,
    rw h at this,
    clear h,
    have := eq_of_eq_singleton (this).symm,
    assumption }
end

example {α : Type} (a b : α) : a = b ↔ b = a :=
eq_comm

lemma pair_eq_singleton (a : Set) : pair a a = {a} :=
begin
  ext,
  have := pair_spec a a x,
  simp [this, mem_singleton_iff]
end

lemma mem_pair_left (a b : Set) : a ∈ pair a b :=
begin
  have := pair_spec a b a,
  simpa using this
end

lemma mem_pair_right (a b : Set) : b ∈ pair a b :=
begin
  have := pair_spec a b b,
  simpa using this
end

lemma snd_eq_snd_of_tuple_eq_tuple (h : tuple a₁ b₁ = tuple a₂ b₂) : b₁ = b₂ :=
begin
  obtain rfl := fst_eq_fst_of_tuple_eq_tuple h,
  rename a₁ a,
  have h' : pair a b₂ ∈ tuple a b₁,
  { rw h,
    have := pair_spec (pair a a) (pair a b₂) (pair a b₂),
    simpa using this },
  unfold tuple at h',
  have := pair_spec (pair a a) (pair a b₁) (pair a b₂),
  simp [h'] at this,
  cases this,
  { have : a = b₂,
    { change _ = {a} at this,
      rw pair_spec' at this,
      simp [eq_of_eq_singleton this] },
    subst this,
    clear this,
    unfold tuple at h,
    rw [pair_eq_singleton, pair_eq_singleton, pair_spec', pair_spec'] at h,
    have h := eq_of_eq_singleton h,
    have h := eq_of_eq_singleton h.symm,
    rw h },
  { clear h h',
    have h₁ := pair_spec a b₁ b₂,
    rw ←this at h₁,
    simp [mem_pair_right] at h₁,
    have h₂ := pair_spec a b₂ b₁,
    rw this at h₂,
    simp [mem_pair_right] at h₂,
    cases h₁; cases h₂; tidy }
end

lemma tuple_spec : tuple a₁ b₁ = tuple a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
begin
  split; intro h,
  { simp [fst_eq_fst_of_tuple_eq_tuple h, snd_eq_snd_of_tuple_eq_tuple h] },
  { simp [h] }
end