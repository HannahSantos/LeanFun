inductive myNat where
  | O : myNat
  | S : myNat → myNat
deriving Repr

def add : myNat → myNat → myNat
  | n, .O => n
  | n, (.S m) => .S (add n m)
infixl:65 " + " => add
