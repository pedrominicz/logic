import tactic

#check setoid
#check @quotient
#check prod

def int_relation : ℕ × ℕ → ℕ × ℕ → Prop
| (a, b) (c, d) := a + d = c + b

lemma int_relation_reflexive : reflexive int_relation :=
begin
  rintro ⟨a, b⟩,
  unfold int_relation
end

lemma int_relation_symmetric : symmetric int_relation :=
begin
  rintros ⟨a, b⟩ ⟨c, d⟩ h,
  unfold int_relation at h ⊢,
  symmetry,
  assumption
end

lemma int_relation_transitive : transitive int_relation :=
begin
  rintros ⟨a, b⟩ ⟨c, d⟩ ⟨m, n⟩ h₁ h₂,
  unfold int_relation at h₁ h₂ ⊢,
  linarith
end

lemma int_relation_equivalence : equivalence int_relation :=
begin
  refine ⟨_, _, _⟩,
  { exact int_relation_reflexive },
  { exact int_relation_symmetric },
  { exact int_relation_transitive }
end

#check int

instance int_setoid : setoid (ℕ × ℕ) := ⟨int_relation, int_relation_equivalence⟩

def int' : Type := quotient int_setoid

def int'_of_nat (n : ℕ) : int' := quotient.mk (n, 0)

#check has_add

def int_add : ℕ × ℕ → ℕ × ℕ → int'
| (a, b) (c, d) := quotient.mk (a + c, b + d)

instance : has_add int' :=
begin
  constructor,
  apply quotient.lift₂ int_add,
  rintros ⟨a₁₁, a₁₂⟩ ⟨a₂₁, a₂₂⟩ ⟨b₁₁, b₁₂⟩ ⟨b₂₁, b₂₂⟩ h₁ h₂,
  apply quotient.sound,
  change _ = _,
  change _ = _ at h₁,
  change _ = _ at h₂,
  linarith
end

def int_le : ℕ × ℕ → ℕ × ℕ → Prop
| (a, b) (c, d) := a + d ≤ b + c

instance : has_le int' :=
begin
  constructor,
  apply quotient.lift₂ int_le,
  rintros ⟨a₁₁, a₁₂⟩ ⟨a₂₁, a₂₂⟩ ⟨b₁₁, b₁₂⟩ ⟨b₂₁, b₂₂⟩ h₁ h₂,
  change _ = _ at h₁,
  change _ = _ at h₂,
  unfold int_le,
  ext,
  split; intro h; linarith
end

-- Problem 6.1. Show that (m + n)_ℤ = m_ℤ + n_ℤ and m ≤ n ↔ m_ℤ ≤ n_ℤ, for any
-- m, n ∈ ℕ.
lemma problem_6_1_a (m n : ℕ) : int'_of_nat (m + n) = int'_of_nat m + int'_of_nat n :=
begin
  unfold int'_of_nat,
  apply quotient.sound,
  refl
end

lemma problem_6_1_b (m n : ℕ) : m ≤ n ↔ int'_of_nat m ≤ int'_of_nat n :=
begin
  unfold int'_of_nat,
  change _ ↔ int_le _ _,
  unfold int_le,
  rw [add_zero, zero_add]
end

-- Problem 6.2. Show that ∽ is an equivalence relation.
--
-- Note: ∽ is the equivalence relation that is used to define ℚ, definition on
-- page 75.
example : sorry := sorry