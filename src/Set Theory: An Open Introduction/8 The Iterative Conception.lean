import tactic

example {α : Type*} (r : α → α → Prop) : ¬ ∃ x, ∀ z, r z x ↔ ¬ r x x :=
begin
  rintros ⟨x, hx⟩,
  specialize hx x,
  simpa using hx
end