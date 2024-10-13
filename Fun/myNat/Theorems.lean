import Fun.myNat.Definitions

open myNat

theorem Add_zero_L :
  ∀ (n : myNat), O + n = n :=
by
  intro n
  induction n with
  | O => rw [add]
  | S k HI => rw [add, HI]
