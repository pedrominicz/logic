import tactic

-- In the book, Peter Smith presents a axiomatic system for FOL with two axioms
-- schemas corresponding to the `s` and `k` combinators below.

variables {p q r : Prop} (h₁ : p → q) (h₂ : q → r)

lemma s : (p → q → r) → (p → q) → p → r :=
λ x y z, x z (y z)

lemma k : p → q → p :=
λ x y, x

-- This is a proof of `p → r` in a natural-deduction system. Lambdas and
-- function application correspond respectively to conditional proofs and modus
-- ponens.
example : p → r :=
λ x, h₂ (h₁ x)

-- One can transform a lambda term into an equivalent term in SK-combinator
-- calculus, so one should be able to transform a natural-deduction proof into
-- a axiomatic proof using the combinators above.
--
-- Roughly speaking, application is equivalent to using the S-combinator. It is
-- easy to figure out the rest.
example : p → r :=
s (k h₂) h₁