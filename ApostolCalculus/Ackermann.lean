def Ackermann (x y: Nat): Nat :=
  if x = 0 then
    y + 1
  else if y = 0 then
    Ackermann (x - 1) 1
  else
    Ackermann (x - 1) (Ackermann x (y - 1))
termination_by _ => (x, y)
