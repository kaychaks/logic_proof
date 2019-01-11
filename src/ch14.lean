
---

section
parameters {A : Type} {R : A → A → Prop}
parameter (irreflR : irreflexive R)
parameter (transR : transitive R)

local infix < := R

def R' (a b : A) : Prop := R a b ∨ a = b
local infix ≤ := R'

theorem reflR' (a : A) : a ≤ a := or.inr (refl a)

theorem transR' {a b c : A} (h1 : a ≤ b) (h2 : b ≤ c):
  a ≤ c :=
  or.elim h1
    (assume : a < b,
      show a ≤ c, from
        or.elim h2
          (assume : b < c, or.inl (transR ‹ a < b › ‹ b < c ›))
          (assume : b = c, or.inl (eq.subst ‹ b = c › ‹ a < b ›)))
    (assume : a = b,
      show a ≤ c, from
        or.elim h2
          (assume : b < c, or.inl (eq.symm ‹ a = b ›  ▸ ‹ b < c ›))
          (assume : b = c, or.inr (‹ b = c › ▸ ‹ a = b ›)))

theorem antisymmR' {a b : A} (h1 : a ≤ b) (h2 : b ≤ a) :
  a = b :=
    or.elim h1
      (assume : a < b,
        or.elim h2
          (assume : b < a, have false, from (irreflR a) (transR ‹ a < b › ‹ b < a ›), ‹ false ›.elim)
          (assume : b = a, eq.symm this)
      )
      (assume : a = b, eq.symm (eq.symm this))
end

---

section
parameters {A : Type} {R : A → A → Prop}
parameter (reflR : reflexive R)
parameter (transR : transitive R)

def S (a b : A) : Prop := R a b ∧ R b a

example : transitive S :=
assume a b c,
assume h1 h2,
⟨ transR h1.left h2.left , transR h2.right h1.right ⟩

end

---

section
  parameters {A : Type} {a b c : A} {R : A → A → Prop}
  parameter (Rab : R a b)
  parameter (Rbc : R b c)
  parameter (nRac : ¬ R a c)

  -- Prove one of the following two theorems:

  theorem R_is_strict_partial_order :
    irreflexive R ∧ transitive R :=
  sorry

  theorem R_is_not_strict_partial_order :
    ¬(irreflexive R ∧ transitive R) :=
  assume h : irreflexive R ∧ transitive R,
  show false, from
    nRac (h.right Rab Rbc)
end

---

open nat

example : 1 ≤ 4 :=
le_succ_of_le $ le_succ_of_le $ le_succ 1