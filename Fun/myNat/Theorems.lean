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
