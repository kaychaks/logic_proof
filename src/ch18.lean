open nat

namespace hidden

theorem add_distrib (m n k: nat) : m * (n + k) = m * n + m * k :=
nat.rec_on k
  (show m * (n + 0) = m * n + m * 0, by rw [mul_zero , add_zero, add_zero])
  (assume k,
    assume ih : m * (n + k) = m * n + m * k,
    show m * (n + succ k) = m * n + m * succ k, from calc
      m * (n + succ k) = m * succ (n + k) : by rw add_succ
      ... = m * (n + k) + m : by rw mul_succ
      ... = m * n + m * k + m : by rw ih
      ... = m * n + (m * k + m) : by rw add_assoc
      ... = m * n + m * succ k : by rw mul_succ
      )

theorem zero_mul (n : nat) : 0 * n = 0 :=
nat.rec_on n
  (show 0 * 0 = 0, from rfl)
  (assume n,
    assume ih : 0 * n = 0,
    show 0 * succ n = 0, from calc
      0 * succ n = 0 * n + 0 : by rw mul_succ
      ... = 0 + 0 : by rw ih
      ... = 0 : by rw zero_add)

theorem one_mul (n : nat) : 1 * n = n :=
nat.rec_on n
  (show 1 * 0 = 0, by rw mul_zero)
  (assume n,
    assume ih: 1 * n = n,
    show 1 * succ n = succ n, from calc
      1 * succ n = 1 * n + 1 : by rw mul_succ
      ... = n + 1 : by rw ih
      ... = succ n : rfl)


theorem mul_assoc (m n k : nat) : m * (n * k) = (m * n) * k :=
nat.rec_on k
  (show m * (n * 0) = (m * n) * 0, by rw [mul_zero, mul_zero, mul_zero])
  (assume k,
    assume ih : m * (n * k) = (m * n) * k,
    show m * (n * succ k) = (m * n) * succ k, from calc
      m * (n * succ k) = m * (n * k + n) : by rw mul_succ
      ... = m * (n * k) + m * n : by rw add_distrib
      ... = (m * n) * k + m * n : by rw ih
      ... = (m * n) * succ k : by rw mul_succ)

theorem mul_comm (m n : nat) : m * n = n * m :=
nat.rec_on n
  (show m * 0 = 0 * m, by rw [zero_mul,mul_zero])
  (assume n,
    assume ih: m * n = n * m,
    show m * succ n = succ n * m, from calc
      m * succ n = m * n + m : by rw mul_succ
      ... = n * m + m : by rw ih
      ... = succ n * m : by rw succ_mul)

-- END
end hidden


open nat

namespace hidden


-- BEGIN
theorem T1 : ∀ m n : nat, m > n → (m = n + 1) ∨ (m > n + 1) :=
assume m n,
assume h,
have h1: succ n ≤ m, from succ_le_of_lt h,
have h2 : n + 1 < m ∨ n + 1 = m, from iff.elim_left le_iff_lt_or_eq h1,
or.elim h2
  (assume : n + 1 < m,
    show m = n + 1 ∨ m > n + 1, from or.inr this)
  (assume : n + 1 = m,
    have m = n + 1, from eq.symm this,
    show m = n + 1 ∨ m > n + 1, from or.inl this)


theorem T2: ∀ n : nat, n = 0 ∨ n > 0 :=
assume n,
have 0 = n ∨ 0 < n, from or.swap $ iff.elim_left le_iff_lt_or_eq $ zero_le n,
or.elim this
  (assume h1, or.inl (eq.symm h1))
  (assume h1, or.inr h1)


theorem T3 (m n : nat) : n + m = 0 → n = 0 ∧ m = 0 :=
assume h,
have h1: n ≥ 0, from zero_le n,
have h2: m ≥ 0, from zero_le m,
iff.elim_left (add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg h1 h2) h

theorem T4 (n m k : nat) : n * k < m * k → k > 0 ∧ n < m :=
assume h,
have h1 : k ≥ 0, from zero_le k,
have h2 : n < m, from lt_of_mul_lt_mul_right h h1,
have h3: k ≠ 0, from
  assume : k = 0,
  have n * 0 < m * 0, from (this ▸ h),
  lt_le_antisymm this (zero_le 0),
have h4: k > 0, from lt_of_le_of_ne h1 h3.symm,
⟨ h4 , h2 ⟩

-- END
end hidden
