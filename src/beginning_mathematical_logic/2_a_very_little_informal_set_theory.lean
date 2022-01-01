import tactic

variables {α : Type} {a a₁ a₂ b₁ b₂ : α}

def pair (a b : α) : set (set α) := {{a}, {a, b}}

lemma eq_of_eq_singleton (h : {b₁, b₂} = ({a} : set α)) : b₁ = b₂ := 
begin
  have h₁ := set.ext_iff.mp h b₁,
  have h₂ := set.ext_iff.mp h b₂,
  tidy
end

lemma fst_eq_fst_of_pair_eq_pair (h : pair a₁ b₁ = pair a₂ b₂) : a₁ = a₂ :=
begin
  have : {a₂} ∈ pair a₁ b₁, by simp [pair, h],
  cases this,
  { tidy },
  { suffices : a₁ = b₁, by tidy,
    simp [eq_of_eq_singleton (set.mem_singleton_iff.mp this).symm] }
end

lemma snd_eq_snd_of_pair_eq_pair (h : pair a₁ b₁ = pair a₂ b₂) : b₁ = b₂ :=
begin
  obtain rfl := fst_eq_fst_of_pair_eq_pair h,
  rename a₁ a,
  unfold pair at h,
  have : {a, b₂} ∈ pair a b₁, by simp [pair, h],
  cases this,
  { obtain rfl := eq_of_eq_singleton this,
    rw [set.pair_eq_singleton, set.pair_eq_singleton] at h,
    have h := (@eq_of_eq_singleton (set α) _ _ _ h),
    have h := eq_of_eq_singleton h.symm,
    rw h },
  { simp at this,
    change (λ x, x = a ∨ x = b₂) = (λ x, x = a ∨ x = b₁) at this,
    have h₁ := congr_fun this b₁, simp at h₁,
    have h₂ := congr_fun this b₂, simp at h₂,
    cases h₁; cases h₂; tidy }
end

example : pair a₁ b₁ = pair a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
begin
  split; intro h,
  { simp [fst_eq_fst_of_pair_eq_pair h, snd_eq_snd_of_pair_eq_pair h] },
  { simp [h] }
end