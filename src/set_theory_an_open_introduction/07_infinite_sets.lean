import tactic

-- 7.5 Appendix: Proving Schröder-Bernstein
--
-- [...] given injections f : A → B and g : B → A there is a bijection
-- h : A → B.

variables {α β : Type} {f : α → β} {g : β → α}

#print axioms is_empty_or_nonempty

example (hf : function.injective f) (hg : function.injective g) :
  ∃ i : α → β, function.bijective i :=
begin
  sorry
end