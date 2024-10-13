inductive myNat where
  | O : myNat
  | S : myNat → myNat
deriving Repr
