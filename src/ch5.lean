variables A B : Prop
open classical

example : ¬ A → false → A :=
sorry

example : ¬ A ∨ ¬ B → ¬ (A ∧ B) :=
assume h,
show ¬ (A ∧ B), from
    assume h1 : A ∧ B,
    show false, from
        or.elim h
        (assume na : ¬ A,
         show false, from na h1.left)
        (assume nb : ¬ B,
         show false, from nb h1.right)


-- Prove ¬ (A ∧ B) → ¬ A ∨ ¬ B by replacing the sorry's below
-- by proofs.

lemma step1 (h₁ : ¬ (A ∧ B)) (h₂ : A) : ¬ A ∨ ¬ B :=
have ¬ B, from
  assume b : B,
  show false, from h₁ (and.intro h₂ b),
show ¬ A ∨ ¬ B, from or.inr this

lemma step2 (h₁ : ¬ (A ∧ B)) (h₂ : ¬ (¬ A ∨ ¬ B)) : false :=
have ¬ A, from
  assume : A,
  have ¬ A ∨ ¬ B, from step1 h₁ ‹A›,
  show false, from h₂ this,
show false, from h₂ (or.inl this)

theorem step3 (h : ¬ (A ∧ B)) : ¬ A ∨ ¬ B :=
by_contradiction
  (assume h' : ¬ (¬ A ∨ ¬ B),
    show false, from step2 h h')

example (h : ¬ B → ¬ A) : A → B :=
assume a,
by_contradiction (assume h1 : ¬ B, show false, from h h1 a)

example (h : A → B) : ¬ A ∨ B :=
by_contradiction
  (assume h1 : ¬ (¬ A ∨ B),
  show false, from
    have a : ¬ A, from assume aa : A, show false, from h1 (or.inr (h aa)),
    h1 (or.inl a))
