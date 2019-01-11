section
  variable A : Type
  variable f : A → A
  variable P : A → Prop
  variable  h : ∀ x, P x → P (f x)

  -- Show the following:
  example : ∀ y, P y → P (f (f y)) :=
  assume x,
  assume h1: P x,
  have h2 : P x → P (f x), from h x,
  have h3: P (f x), from h2 h1,
  have h4 : P (f x) → P (f (f x)), from h (f x),
  show P (f (f x)), from h4 h3
end

section
  variable U : Type
  variables A B : U → Prop

  example : (∀ x, A x ∧ B x) → ∀ x, A x :=
  assume h : ∀ x, A x ∧ B x,
  assume y,
  have h1 : A y ∧ B y, from h y,
  show A y, from and.left h1
end

---

section
  variable U : Type
  variables A B C : U → Prop

  variable h1 : ∀ x, A x ∨ B x
  variable h2 : ∀ x, A x → C x
  variable h3 : ∀ x, B x → C x

  example : ∀ x, C x :=
  assume y,
  or.elim (h1 y)
    (assume ha1, show C y, from (h2 y) ha1)
    (assume ha2, show C y, from (h3 y) ha2)
end

---

open classical   -- not needed, but you can use it

-- This is an exercise from Chapter 4. Use it as an axiom here.
axiom not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P)

example (Q : Prop) : ¬ (Q ↔ ¬ Q) :=
not_iff_not_self Q

section
  variable Person : Type
  variable shaves : Person → Person → Prop
  variable barber : Person
  variable h : ∀ x, shaves barber x ↔ ¬ shaves x x

  -- Show the following:
  example : false :=
  show false, from
    (not_iff_not_self (shaves barber barber)) (h barber)
end

---

section
  variable U : Type
  variables A B : U → Prop

  example : (∃ x, A x) → ∃ x, A x ∨ B x :=
  assume h,
  exists.elim h
    (assume y (h1 : A y),
      exists.intro y (or.inl h1))
end

---

section
  variable U : Type
  variables A B : U → Prop

  variable h1 : ∀ x, A x → B x
  variable h2 : ∃ x, A x

  example : ∃ x, B x :=
  exists.elim h2
  (assume y h3,
    exists.intro y (h1 y h3))
end

---

variable  U : Type
variables A B C : U → Prop

example (h1 : ∃ x, A x ∧ B x) (h2 : ∀ x, B x → C x) :
    ∃ x, A x ∧ C x :=
exists.elim h1
(assume y h3,
    exists.intro y ⟨ and.left h3, h2 y (and.right h3) ⟩ )

---

variable  U : Type
variables A B C : U → Prop

example : (¬ ∃ x, A x) → ∀ x, ¬ A x :=
λ h1 y h3, h1 (exists.intro y h3)

example : (∀ x, ¬ A x) → ¬ ∃ x, A x :=
λ h1 h2, exists.elim h2 (λ y h3, h1 y h3)

---

variable  U : Type
variables R : U → U → Prop

example : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y :=
assume h1 y,
exists.elim h1
(assume x (h2 : ∀ x1, R x x1),
    exists.intro x (h2 y))

---

theorem foo {A : Type} {a b c : A} : a = b → c = b → a = c :=
assume h1 : a = b,
assume h2 : c = b,
show a = c, by rw [h2,h1]
-- notice that you can now use foo as a rule. The curly braces mean that
-- you do not have to give A, a, b, or c

section
  variable A : Type
  variables a b c : A

  example (h1 : a = b) (h2 : c = b) : a = c :=
  foo h1 h2
end

section
  variable {A : Type}
  variables {a b c : A}

  -- replace the sorry with a proof, using foo and rfl, without using eq.symm.
  theorem my_symm (h : b = a) : a = b :=
  have h1 : a = a, from eq.refl a,
  foo h1 h

  -- now use foo, rfl, and my_symm to prove transitivity
  theorem my_trans (h1 : a = b) (h2 : b = c) : a = c :=
  foo h1 (my_symm h2)
end

---

-- these are the axioms for a commutative ring

#check @add_assoc
#check @add_comm
#check @add_zero
#check @zero_add
#check @mul_assoc
#check @mul_comm
#check @mul_one
#check @one_mul
#check @left_distrib
#check @right_distrib
#check @add_left_neg
#check @add_right_neg
#check @sub_eq_add_neg

variables x y z : int

theorem t1 : x - x = 0 :=
calc
x - x = x + -x : by rw sub_eq_add_neg
    ... = 0      : by rw add_right_neg

theorem t2 (h : x + y = x + z) : y = z :=
calc
y     = 0 + y        : by rw zero_add
    ... = (-x + x) + y : by rw add_left_neg
    ... = -x + (x + y) : by rw add_assoc
    ... = -x + (x + z) : by rw h
    ... = (-x + x) + z : by rw add_assoc
    ... = 0 + z        : by rw add_left_neg
    ... = z            : by rw zero_add

theorem t3 (h : x + y = z + y) : x = z :=
calc
x     = x + 0        : by rw add_zero
    ... = x + (y + -y) : by rw add_right_neg
    ... = (x + y) + -y : by rw add_assoc
    ... = (z + y) + -y : by rw h
    ... = z + (y + -y) : by rw add_assoc
    ... = z + 0        : by rw add_right_neg
    ... = z            : by rw add_zero

theorem t4 (h : x + y = 0) : x = -y :=
calc
x     = x + 0        : by rw add_zero
    ... = x + (y + -y) : by rw add_right_neg
    ... = (x + y) + -y : by rw add_assoc
    ... = 0 + -y       : by rw h
    ... = -y           : by rw zero_add

theorem t5 : x * 0 = 0 :=
have h1 : x * 0 + x * 0 = x * 0 + 0, from
calc
    x * 0 + x * 0 = x * (0 + 0) : by rw left_distrib
            ... = x * 0       : by rw add_zero
            ... = x * 0 + 0   : by rw add_zero,
show x * 0 = 0, from t2 _ _ _ h1

theorem t6 : x * (-y) = -(x * y) :=
have h1 : x * (-y) + x * y = 0, from
calc
    x * (-y) + x * y = x * (-y + y) : by rw left_distrib
                ... = x * 0        : by rw add_left_neg
                ... = 0            : by rw t5 x,
show x * (-y) = -(x * y), from t4 _ _ h1

theorem t7 : x + x = 2 * x :=
calc
x + x = 1 * x + 1 * x : by rw one_mul
    ... = (1 + 1) * x   : by rw right_distrib
    ... = 2 * x         : rfl