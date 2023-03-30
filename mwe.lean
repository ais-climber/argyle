
variable (a b : Nat) in
#synth Decidable (a ≤ b) -- Nat.decLe a b

#check Nat.decLe -- you can see how they did it in Lean