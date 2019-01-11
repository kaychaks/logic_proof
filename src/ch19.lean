import data.int.basic

open int
open nat

-- quotient / remainder theorem
theorem qt : ∀ n m : ℤ, m > 0 → ∃ q r : ℤ, n = m * q + r ∧ (0 ≤ r ∧ r < m) :=
assume n m h,

exists.intro (n / m) $ exists.intro (n % m) $

  have HH:  n = m * (n / m)  + (n % m), from calc
    n = n % m + m * (n / m) : by rw [int.mod_add_div]
    ... = m * (n / m) + (n % m) : by rw add_comm,

  have HH1: 0 ≤ (n % m), from int.mod_nonneg n (ne_of_gt h),

  have HH2: (n % m) < m, from calc
    (n % m) < abs m : int.mod_lt n (ne_of_gt h)
    ... = m : abs_of_pos h,

  ⟨ HH , ⟨ HH1 , HH2 ⟩ ⟩
