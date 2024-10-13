inductive myNat where
  | O : myNat
  | S : myNat → myNat
deriving Repr

def add : myNat → myNat → myNat
  | n, .O => n
  | n, (.S m) => .S (add n m)
infixl:65 " + " => add

def mul : myNat → myNat → myNat
  | _, .O => .O
  | n, .S m => (mul n m) + n
infixl:65 " * " => mul

def pow : myNat → myNat → myNat
  | _, .O => .S .O
  | n, .S m => (pow n m) * n
infixr:65 " ^ " => pow
