variables A B C D : Prop

example : A ∧ (A → B) → B :=
assume h,
show B, from h.right h.left


example : A → ¬ (¬ A ∧ B) :=
assume h1 : A,
assume h2: ¬ A ∧ B,
show false, from h2.left h1

example : ¬ (A ∧ B) → (A → ¬ B) :=
λ h1 h2 h3, h1 (⟨ h2 , h3 ⟩)

example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
or.elim h₁
  (assume h₄ : A, show C ∨ D, from or.inl (h₂ h₄))
  (assume h₄ : B, show C ∨ D, from or.inr (h₃ h₄))

example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
assume h1 : A ∨ B,
or.elim h1
  (assume h2 : A, show false, from h.left h2)
  (assume h3 : B, show false, from h.right h3)

example : ¬ (A ↔ ¬ A) :=
assume h,
have h1 : ¬ A, from
    assume a : A,
    show false, from (h.mp a) a,
show false, from h1 (h.mpr h1)
