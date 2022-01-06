import tactic

namespace fol

@[reducible] def var := ℕ

structure Language :=
(functions : ℕ → Type)
(relations : ℕ → Type)

section

variable (L : Language)

def Language.constants := L.functions 0

inductive preterm : ℕ → Type
| var : var → preterm 0
| func {l : ℕ} : L.functions l → preterm l
| app {l : ℕ} : preterm (l + 1) → preterm 0 → preterm l

@[reducible] def term := preterm L 0

namespace term

def fv {L : Language} : ∀ {l : ℕ}, preterm L l → set var
| l (preterm.var x) := {x}
| l (preterm.func f) := ∅
| l (preterm.app t₁ t₂) := fv t₁ ∪ fv t₂

instance (l : ℕ) (x : var) (t : preterm L l) : decidable (x ∈ fv t) :=
begin
  induction t with y l' f l' t₁ t₂ ih₁ ih₂,
  { change decidable (x = y),
    apply_instance },
  { clear l,
    rename l' l,
    change decidable (x ∈ ∅),
    change decidable false,
    exact decidable.false },
  { clear l,
    rename l' l,
    change decidable (x ∈ fv t₁ ∪ fv t₂),
    change decidable (x ∈ fv t₁ ∨ x ∈ fv t₂),
    exact @or.decidable _ _ ih₁ ih₂ }
end

end term

inductive preformula : ℕ → Type
| eq : term L → term L → preformula 0
| rel {l : ℕ} : L.relations l → preformula l
| app {l : ℕ} : preformula (l + 1) → term L → preformula l
| not : preformula 0 → preformula 0
| or : preformula 0 → preformula 0 → preformula 0
| all : var → preformula 0 → preformula 0

@[reducible] def formula := preformula L 0

namespace formula

def fv {L : Language} : ∀ {l : ℕ}, preformula L l → set var
| l (preformula.eq t₁ t₂) := term.fv t₁ ∪ term.fv t₂
| l (preformula.rel r) := ∅
| l (preformula.app f t) := fv f ∪ term.fv t
| l (preformula.not f) := fv f
| l (preformula.or f₁ f₂) := fv f₁ ∪ fv f₂
| l (preformula.all x f) := fv f \ {x}

instance (l : ℕ) (x : var) (φ : preformula L l) : decidable (x ∈ fv φ) :=
begin
  induction φ with t₁ t₂ l' r l' φ t ih φ ih φ₁ φ₂ ih₁ ih₂ y φ ih,
  { change decidable (x ∈ term.fv t₁ ∪ term.fv t₂),
    change decidable (x ∈ term.fv t₁ ∨ x ∈ term.fv t₂),
    exact or.decidable },
  { clear l,
    rename l' l,
    change decidable (x ∈ ∅),
    change decidable false,
    exact decidable.false },
  { clear l,
    rename l' l,
    change decidable (x ∈ fv φ ∪ term.fv t),
    change decidable (x ∈ fv φ ∨ x ∈ term.fv t),
    exact @or.decidable _ _ ih _ },
  { change decidable (x ∈ fv φ),
    assumption },
  { change decidable (x ∈ fv φ₁ ∪ fv φ₂),
    change decidable (x ∈ fv φ₁ ∨ x ∈ fv φ₂),
    exact @or.decidable _ _ ih₁ ih₂ },
  { change decidable (x ∈ fv φ \ {y}),
    change decidable (x ∈ fv φ ∧ x ≠ y),
    exact @and.decidable _ _ ih (ne.decidable _ _) }
end

end formula

@[reducible] def sentence := {φ : formula L // formula.fv φ = ∅}

end

section

local notation h ` :: ` t := vector.cons h t

structure Structure (L : Language) :=
(carrier : Type)
(functions {n : ℕ} : L.functions n → vector carrier n → carrier)
(relations {n : ℕ} : L.relations n → vector carrier n → Prop)

instance (L : Language) : has_coe_to_sort (Structure L) Type :=
⟨λ A, A.carrier⟩

variables {L : Language} {A : Structure L}

def subst (s : var → A) (x : var) (a : A) : var → A :=
λ y, if x = y then a else s y

notation s `[`:95 x ` // `:95 a `]`:0 := subst s x a

def realize_preterm (s : var → A) : ∀ {l : ℕ}, vector A l → preterm L l → A
| l args (preterm.var x) := s x
| l args (preterm.func f) := A.functions f args
| l args (preterm.app t₁ t₂) := realize_preterm (realize_preterm vector.nil t₂ :: args) t₁

def realize_term (s : var → A) : term L → A :=
realize_preterm s vector.nil

-- Lemma 1.7.6. Suppose that s1 and s2 are variable assignment functions into a
-- structure A such that s1(v) = s2(v) for every variable v in the term t. Then
-- s1(t) = s2(t).
lemma realize_preterm_eq (s₁ s₂ : var → A) {l : ℕ} (args : vector A l) (t : preterm L l) :
  (∀ x ∈ term.fv t, s₁ x = s₂ x) → realize_preterm s₁ args t = realize_preterm s₂ args t :=
begin
  induction t with y l f l t₁ t₂ ih₁ ih₂ generalizing args; intro h,
  { change s₁ y = s₂ y,
    change ∀ x, x = y → s₁ x = s₂ x at h,
    rwa forall_eq at h },
  { refl },
  { unfold realize_preterm,
    rw ih₂ vector.nil (λ x hx, h x (or.inr hx)),
    exact ih₁ _ (λ x hx, h x (or.inl hx)) }
end

lemma realize_term_eq (s₁ s₂ : var → A) (t : term L) :
  (∀ x ∈ term.fv t, s₁ x = s₂ x) → realize_term s₁ t = realize_term s₂ t :=
realize_preterm_eq _ _ _ _

def realize_preformula : (var → A) → ∀ {l : ℕ}, vector A l → preformula L l → Prop
| s l args (preformula.eq t₁ t₂) := realize_term s t₁ = realize_term s t₂
| s l args (preformula.rel r) := A.relations r args
| s l args (preformula.app φ t) := realize_preformula s (realize_term s t :: args) φ
| s l args (preformula.not φ) := ¬ realize_preformula s args φ
| s l args (preformula.or φ₁ φ₂) := realize_preformula s args φ₁ ∨ realize_preformula s args φ₂
| s l args (preformula.all x φ) := ∀ a, realize_preformula (s[x // a]) args φ

def realize_formula (s : var → A) : formula L → Prop :=
realize_preformula s vector.nil

infix ` ⊨ `:51 := realize_formula

-- Proposition 1.7.7. Suppose that s₁ and s₂ are variable assignment functions
-- into a structure A such that s₁(v) = s₂(v) for every free variable v in the
-- formula φ. Then A ⊨ φ[s₁] if and only if A ⊨ φ[s₂].
lemma realize_preformula_iff (s₁ s₂ : var → A) {l : ℕ} (args : vector A l) (φ : preformula L l)
  : (∀ x ∈ formula.fv φ, s₁ x = s₂ x) →
    (realize_preformula s₁ args φ ↔ realize_preformula s₂ args φ) :=
begin
  induction φ with t₁ t₂ l r l φ t ih φ ih φ₁ φ₂ ih₁ ih₂ x φ ih generalizing s₁ s₂ args;
  intro h; unfold realize_preformula,
  { have h₁ := realize_term_eq s₁ s₂ t₁ (λ x hx, h x (or.inl hx)),
    have h₂ := realize_term_eq s₁ s₂ t₂ (λ x hx, h x (or.inr hx)),
    rw [h₁, h₂] },
  { rw realize_term_eq s₁ s₂ t (λ x hx, h x (or.inr hx)),
    exact ih _ _ _ (λ x hx, h x (or.inl hx)) },
  { rw not_iff_not,
    exact ih _ _ _ h },
  { have h₁ := ih₁ _ _ _ (λ x hx, h x (or.inl hx)),
    have h₂ := ih₂ _ _ _ (λ x hx, h x (or.inr hx)),
    exact or_congr h₁ h₂ },
  { refine forall_congr (λ a, ih _ _ _ (λ y hy, _)),
    by_cases this : x = y; unfold subst,
    { simp [this] },
    { simp [this, h _ (and.intro hy (ne.symm this))] } }
end

lemma realize_formula_iff (s₁ s₂ : var → A) (φ : formula L)
  : (∀ x ∈ formula.fv φ, s₁ x = s₂ x) → (s₁ ⊨ φ ↔ s₂ ⊨ φ) :=
realize_preformula_iff _ _ _ _

end

end fol