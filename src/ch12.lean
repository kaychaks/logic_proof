section
  variable {U : Type}
  variables {A B C : set U}

  example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
  assume x : U,
  assume : x ∈ A ∩ C,
  show x ∈ A ∪ B, from or.inl (and.left this)

  example : ∀ x, x ∈ -(A ∪ B) → x ∈ -A :=
  assume x,
  assume h1 : x ∈ -(A ∪ B),
  show x ∈ -A, from
    assume : x ∈ A,
    show false, from h1 (or.inl this)
end

---

import data.set
open set

section
variable {U : Type}

example (A B C : set U) : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
assume x,
assume : x ∈ A ∩ C,
show x ∈ A ∪ B, from or.inl this.left

example (A B : set U) : ∀ x, x ∈ -(A ∪ B) → x ∈ -A :=
assume x,
assume : x ∈ -(A ∪ B),
show x ∈ -A, from
  assume : x ∈ A,
  show false, from ‹ x ∈ -(A ∪ B) › (or.inl this)

/- defining "disjoint" -/

def disj (A B : set U) : Prop := ∀ ⦃x⦄, x ∈ A → x ∈ B → false

example (A B : set U) (h : ∀ x, ¬ (x ∈ A ∧ x ∈ B)) :
  disj A B :=
assume x,
assume h1 : x ∈ A,
assume h2 : x ∈ B,
have h3 : x ∈ A ∧ x ∈ B, from and.intro h1 h2,
show false, from h x h3

-- notice that we do not have to mention x when applying
--   h : disj A B
example (A B : set U) (h1 : disj A B) (x : U)
    (h2 : x ∈ A) (h3 : x ∈ B) :
  false :=
h1 h2 h3

-- the same is true of ⊆
example (A B : set U) (x : U) (h : A ⊆ B) (h1 : x ∈ A) :
  x ∈ B :=
h h1

example (A B C D : set U) (h1 : disj A B) (h2 : C ⊆ A)
    (h3 : D ⊆ B) :
  disj C D :=
assume x,
assume : x ∈ C,
assume : x ∈ D,
show false, from h1 (h2 ‹ x ∈ C › )  (h3 ‹ x ∈ D ›)
end

---

import data.set
open set

section
variables {I U : Type}
variables {A B : I → set U}

theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i :=
by simp; assumption

@[elab_simple]
theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i :=
by simp at h; apply h

theorem Union.intro {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i :=
by {simp, existsi i, exact h}

theorem Union.elim {b : Prop} {x : U}
(h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b :=
by {simp at h₁, cases h₁ with i h, exact h₂ i h}

end

-- BEGIN
variables {I U : Type}
variables (A : I → set U) (B : I → set U) (C : set U)

example : (⋂ i, A i) ∩ (⋂ i, B i) ⊆ (⋂ i, A i ∩ B i) :=
assume x,
assume h1 : x ∈ (⋂ i, A i) ∩ (⋂ i, B i),
show x ∈ (⋂ i, A i ∩ B i), from
    have h2 : ∀ i, x ∈ A i ∩ B i, from
        assume i : I,
        have x ∈ A i, from Inter.elim (h1.left) i,
        have x ∈ B i, from Inter.elim (h1.right) i,
        ⟨ ‹ x ∈ A i › , ‹ x ∈ B i › ⟩,
    Inter.intro h2

example : C ∩ (⋃i, A i) ⊆ ⋃i, C ∩ A i :=
assume x,
assume h,
have h2 : ∀ (i : I), x ∈ A i → x ∈ ⋃i, C ∩ A i, from
    assume i : I,
    assume h1,
    have x ∈ C ∩ A i, from ⟨ h.left , h1 ⟩,
    Union.intro i ‹ x ∈ C ∩ A i › ,

Union.elim h.right h2

-- END

---

import data.set
open set

-- BEGIN
variable  {U : Type}
variables A B C : set U

-- For this exercise these two facts are useful
example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
subset.trans h1 h2

example : A ⊆ A :=
subset.refl A

example (h : A ⊆ B) : powerset A ⊆ powerset B :=
assume x,
assume : x ∈ powerset A,
have x ⊆ A, from ‹ x ∈ powerset A ›,
have x ⊆ B, from subset.trans ‹ x ⊆ A › h,
show x ∈ powerset B, from ‹ x ⊆ B ›

example (h : powerset A ⊆ powerset B) : A ⊆ B :=
assume x,
assume : x ∈ A,
h (subset.refl A) ‹ x ∈ A ›
-- END
