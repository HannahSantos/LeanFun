import Fun.myNat.Definitions

open myNat

----------------------------------------------------------
-- Soma:
----------------------------------------------------------

theorem Add_zero_L :
  ∀ (n : myNat), O + n = n :=
by
  intro n
  induction n with
  | O => rw [add]
  | S k HI => rw [add, HI]

theorem Add_succ_L :
  ∀ (n m : myNat), (S n) + m = S (n + m) :=
by
  intro n m
  induction m with
  | O => rw [add, add]
  | S k HI => rw [add, add, HI]

theorem Add_Ass :
  ∀ (n m k : myNat), n + m + k = n + (m + k) :=
by
  intro n m k
  induction k with
  | O => rw [add, add]
  | S k HI => rw [add, add, add, HI]

theorem Add_Com :
  ∀ (n m : myNat), n + m = m + n :=
by
  intro n m
  induction m with
  | O => rw [add, Add_zero_L]
  | S k HI => rw [add, HI, Add_succ_L]

----------------------------------------------------------
-- Produto:
----------------------------------------------------------

theorem Mul_Id_R :
  ∀ (n : myNat), n * (S O) = n :=
by
  intro n
  rw [mul, mul, Add_zero_L]

theorem Mul_zero_L :
  ∀ (n : myNat), O * n = O :=
by
  intro n
  induction n with
  | O => rw [mul]
  | S k HI => rw [mul, HI, add]

theorem Mul_succ_L :
  ∀ (n m : myNat), (S n) * m = (n * m) + m :=
by
  intro n m
  induction m with
  | O => rw [mul, mul, add]
  | S k HI => rw [mul, HI, mul, add,
                  add, Add_Ass, Add_Com k n,
                  ← Add_Ass]

theorem Mul_Com :
  ∀ (n m : myNat), n * m = m * n :=
by
  intro n m
  induction m with
  | O => rw [mul, Mul_zero_L]
  | S k HI => rw [mul, HI, Mul_succ_L]

theorem Mul_Id_L :
  ∀ (n : myNat), (S O) * n = n :=
by
  intro n
  rw [Mul_Com, Mul_Id_R]

theorem Distr_L :
  ∀ (k n m : myNat), k * (n + m) = (k * n) + (k * m) :=
by
  intro k n m
  induction k with
  | O => rw [Mul_zero_L, Mul_zero_L, Mul_zero_L, add]
  | S k HI => rw [Mul_succ_L, HI, Mul_succ_L,
                  Mul_succ_L, Add_Ass (k * n) n (k * m + m),
                  Add_Com (k * m) m, ← Add_Ass n m (k * m),
                  Add_Com (n + m) (k * m), Add_Ass]
