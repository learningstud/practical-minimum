import ApostolCalculus.Nat
set_option autoImplicit false

/-! # Integers -/

inductive ℤ | ofNat (n: ℕ) | negSucc (n: ℕ)

instance: Coe ℕ ℤ where coe := .ofNat

#check Int.subNatNat
protected def ℕ.sub (a b: ℕ): ℤ :=
  match b.monus a with
  | 0 => a.monus b -- b ≤ a
  | succ n => .negSucc n
instance: HSub ℕ ℕ ℤ where hSub := ℕ.sub

protected def ℕ.neg: ℕ → ℤ | 0 => .ofNat 0 | succ n => .negSucc n

namespace ℤ

#check Int.add
instance: Add ℤ where
  add
  | ofNat a, ofNat b => a + b
  | ofNat a, negSucc b => a - b.succ
  | negSucc a, ofNat b => b - a.succ
  | negSucc a, negSucc b => negSucc (a + b).succ


#check Int.neg
instance: Neg ℤ where
  neg
  | ofNat n => n.neg
  | negSucc n => n.succ

#check Int.sub
instance: Sub ℤ where
  sub a b := a + -b

#check Int.mul
instance: Mul ℤ where
  mul
  | ofNat a, ofNat b => a * b
  | ofNat a, negSucc b => (a * b.succ).neg
  | negSucc a, ofNat b => (a.succ * b).neg
  | negSucc a, negSucc b => a.succ * b.succ

  axiom coprime: ℤ → ℤ → Prop
end ℤ

/-! # Rationals -/

structure ℚ where
  /-- Numerator -/
  num: ℤ
  /-- Denominator -/
  den: ℕˣ
  /-- Numerator and denominator are coprime.
  This is required to identify structure equality with equality of rational numbers.  -/
  cop: num.coprime den

#check Setoid
#check Quotient