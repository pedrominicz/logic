import tactic

variables {α : Type} {A B : set α}

-- Problem 2.1. Prove that there is at most one empty set, i.e., show that if A
-- and B are sets without members, then A = B.
lemma problem_2_1 (ha : ∀ x, x ∉ A) (hb : ∀ x, x ∉ B) : A = B :=
begin
  ext,
  specialize ha x,
  specialize hb x,
  split,
  { intro h,
    exfalso,
    apply ha,
    assumption },
  { intro h,
    exfalso,
    apply hb,
    assumption }
end

#check @finset.induction_on

-- Problem 2.3. Show that if A has n members, then ℘(A) has 2^n members.
lemma problem_2_3 [decidable_eq α] (A : finset α) : A.powerset.card = 2 ^ A.card :=
begin
  apply @finset.induction_on _ (λ R, R.powerset.card = 2 ^ R.card),
  { rw [finset.card_empty, finset.powerset_empty, finset.card_singleton, pow_zero] },
  { clear A,
    intro x,
    intro A,
    intro hx,
    intro ih,
    sorry
  }
end

-- Problem 2.4. Prove that if A ⊆ B, then A ∪ B = B.
lemma problem_2_4 (h : A ⊆ B) : A ∪ B = B :=
begin
  ext,
  change ∀ x, x ∈ A → x ∈ B at h,
  split,
  { intro hx,
    cases hx,
    { specialize h x,
      specialize h hx,
      assumption },
    { assumption } },
  { intro hx,
    right,
    assumption }
end

-- Problem 2.5. Prove rigorously that if A ⊆ B, then A ∩ B = A.
lemma problem_2_5 (h : A ⊆ B) : A ∩ B = A :=
begin
  ext,
  change ∀ x, x ∈ A → x ∈ B at h,
  split,
  { intro hx,
    cases hx with hxa hxb,
    assumption },
  { intro hx,
    specialize h x,
    specialize h hx,
    split; assumption }
end

-- Problem 2.6. Show that if A is a set and A ∈ B, then A ⊆ ⋃︁ B.
lemma problem_2_6 (B : set (set α)) (h : A ∈ B) : A ⊆ ⋃₀ B :=
begin
  change ∀ x, x ∈ A → x ∈ ⋃₀ B,
  intro x,
  intro hx,
  simp only [exists_prop, set.mem_set_of_eq],
  use A,
  split; assumption
end

-- Problem 2.7. Prove that if A ⊊ B, then B \ A ≠ ∅
lemma problem_2_7 (h : A ⊂ B) : B \ A ≠ ∅ :=
begin
  change A ⊆ B ∧ ¬ B ⊆ A at h,
  cases h with h₁ h₂,
  intro h,
  unfold has_sdiff.sdiff at h,
  unfold set.diff at h,
  apply h₂,
  clear h₂,
  change ∀ x, x ∈ B → x ∈ A,
  intro x,
  intro hx,
  sorry
end

-- Definition 2.23 (Ordered pair). ⟨a, b⟩ = {{a}, {a, b}}.
def pair (a b : α) : set (set α) := {{a}, {a, b}}

variables {a₁ a₂ b₁ b₂ : α}

-- Problem 2.8. Using Definition 2.23, prove that ⟨a, b⟩ = ⟨c, d⟩ iff both
-- a = c and b = d .
lemma problem_2_8 : pair a₁ b₁ = pair a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
begin
  sorry
end

-- Problem 2.10. Show, by induction on k, that for all k ≥ 1, if A has n
-- members, then Ak has n^k members.
lemma problem_2_10 : sorry := sorry