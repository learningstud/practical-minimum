-- import Mathlib.Init.Logic
import ApostolCalculus.Logic

set_option autoImplicit false

/-! ## Monoidal structures -/

variable {α: Type _} (op: α → α → α)

class Associative (op: α → α → α) where
  assoc (a b c): op (op a b) c = op a (op b c)

class Commutative (op: α → α → α) where
  comm (a b): op a b = op b a

class LeftCancellative (op: α → α → α) where
  cancel_l {x a b}: op x a = op x b → a = b

class RightCancellative (op: α → α → α) where
  cancel_r {x a b}: op a x = op b x → a = b

class Cancellative (op: α → α → α) extends
  LeftCancellative op, RightCancellative op

instance [C: Commutative op] [L: LeftCancellative op]: RightCancellative op where
  cancel_r {x a b} h := by apply L.cancel_l (x := x); rw [C.comm, C.comm x]; exact h

instance [C: Commutative op] [R: RightCancellative op]: LeftCancellative op where
  cancel_l {x a b} h := by apply R.cancel_r (x := x); rw [C.comm, C.comm b]; exact h

instance [Commutative op] [LeftCancellative op]: Cancellative op where
instance [Commutative op] [RightCancellative op]: Cancellative op where

class LeftUnital (op: α → α → α) where
  unit_l: ∃ u, ∀ a, op u a = a

class RightUnital (op: α → α → α) where
  unit_r: ∃ u, ∀ a, op a u = a

class Unital (op: α → α → α) where
  unit: ∃! u, ∀ a, op u a = a ∧ op a u = a

instance Unital.toLeftUnital [U: Unital op]: LeftUnital op where
  unit_l := have ⟨u, h, _⟩ := U.unit; ⟨u, fun a => (h a).left⟩
abbrev Unital.unit_l {op : α → α → α} [Unital op] := (toLeftUnital op).unit_l

instance Unital.toRightUnital [U: Unital op]: RightUnital op where
  unit_r := have ⟨u, h, _⟩ := U.unit; ⟨u, fun a => (h a).right⟩
abbrev Unital.unit_r {op : α → α → α} [Unital op] := (toRightUnital op).unit_r

instance [L: LeftUnital op] [R: RightUnital op]: Unital op where
  unit :=
    have ⟨l, hl⟩ := L.unit_l
    have ⟨r, hr⟩ := R.unit_r
    have: l = r := (hr l).symm.trans (hl r)
    ⟨l, fun a => ⟨hl a, this ▸ hr a⟩, fun u h => (hl u).symm.trans (h l).right⟩

class LeftSolvable (op: α → α → α) where
  solve_l (a b): ∃ x, op x a = b

class RightSolvable (op: α → α → α) where
  solve_r (a b): ∃ x, op a x = b

class Solvable (op: α → α → α) extends
  LeftSolvable op, RightSolvable op

-- class LeftInvertible (op: α → α → α) extends Unital op where
--   inv_l (a): ∃ x, op x a = unit

-- class RightInvertible (op: α → α → α) extends Unital op where
--   inv_r (a): ∃ x, op a x = unit

-- class Invertible (op: α → α → α) extends
--   LeftInvertible op, RightInvertible op

-- theorem Invertible.uniq_inv [I: Invertible op]: ∀ a, ∃! x,
--   op x a = I.unit ∧ op a x = I.unit
-- := sorry

-- abbrev Semigroup (op: α → α → α) := Associative op

class Monoid (op: α → α → α) extends Associative op where
  unit: α
  unit_op (a): op unit a = a
  op_unit (a): op a unit = a

instance [M: Monoid op]: LeftUnital op where
  unit_l := ⟨M.unit, M.unit_op⟩
instance [M: Monoid op]: RightUnital op where
  unit_r := ⟨M.unit, M.op_unit⟩
example [Monoid op]: Unital op := inferInstance

class CommMonoid (op: α → α → α) extends Commutative op, Monoid op where
  op_unit := fun a => comm _ _ ▸ unit_op a


/-- Cancellative commutative monoid -/
class CCMonoid (op: α → α → α) extends Cancellative op, CommMonoid op

class Group (op: α → α → α) extends Monoid op where
  inv: α → α
  inv_op (a: α): op (inv a) a = unit
  op_inv (a: α): op a (inv a) = unit
-- namespace Group
--   variable {op: α → α → α} [self: Group op]
--   theorem op_inv (a: α): op a (self.inv a) = self.unit :=
--     by rw [self.comm]
-- end Group

class AbGroup (op: α → α → α) extends Commutative op, Group op

example [AbGroup op]: CommMonoid op where

instance: CCMonoid Nat.add where
  assoc := Nat.add_assoc
  comm := Nat.add_comm
  unit := 0
  unit_op := Nat.zero_add
  op_unit := Nat.add_zero
  cancel_l := Nat.add_left_cancel
  cancel_r := Nat.add_right_cancel

instance: CommMonoid Nat.mul where
  assoc := Nat.mul_assoc
  comm := Nat.mul_comm
  unit := 1
  unit_op := Nat.one_mul
  op_unit := Nat.mul_one

abbrev Invertible (α) [Zero α] := { a: α // a ≠ 0 }
postfix:arg "ˣ" => Invertible
abbrev Pos := Natˣ

instance: One Pos where one := ⟨1, Nat.zero_ne_one.symm⟩
@[simp] theorem Pos.one_eq_Nat_one: (1:Pos).val = 1 := rfl

-- theorem Nat.add_pos (a b: Nat) (h: a + b = 0): a = 0 ∧ b = 0 :=
--   ⟨eq_zero_of_le_zero (h ▸ le_add_right a b), eq_zero_of_le_zero (h ▸ le_add_left b a)⟩

theorem Nat.integral_domain₁ (a b: Nat) (h: a * b = 0): a = 0 ∨ b = 0 :=
  a.eq_zero_or_pos.elim Or.inl fun ha => Or.inr <|
    suffices a * b = a * 0 from Nat.eq_of_mul_eq_mul_left ha this
    Nat.mul_zero a ▸ h 


theorem Nat.cancel_mul {x a b: Nat} (hnx: x ≠ 0) (h: x * a = x * b): a = b :=
  Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_ne_zero hnx) h
theorem Nat.mul_cancel {x a b: Nat}: x ≠ 0 → a * x = b * x → a = b :=
  by rw [Nat.mul_comm, Nat.mul_comm b]; exact Nat.cancel_mul

theorem Nat.integral_domain₂ {a b: Nat}: a ≠ 0 → b ≠ 0 → a * b ≠ 0
  | hna, hnb, h => (integral_domain₁ a b h).elim hna hnb
@[simp] theorem Nat.integral_domain₃ (a b: Pos): a.val * b ≠ 0 :=
  integral_domain₂ a.2 b.2

protected def Pos.mul (a b: Pos): Pos := ⟨a * b, by simp⟩
instance: Mul Pos where mul := Pos.mul
@[simp] theorem Pos.mul_eq_Nat_mul (a b: Pos): (Pos.mul a b).val = a.val * b.val := rfl
@[simp] theorem Pos.mul_iff_Nat_mul {a b: Pos}: a = b ↔ a.val = b.val :=
  ⟨fun | rfl => rfl, Subtype.eq⟩

instance: CCMonoid Pos.mul where
  assoc a b c := by simp [Nat.mul_assoc]
  comm a b := by simp [Nat.mul_comm]
  unit := 1
  unit_op a := by simp
  op_unit a := by simp
  cancel_l {x a b} := by simp; exact Nat.cancel_mul x.2
  cancel_r {x a b} := by simp; exact Nat.mul_cancel x.2

instance {α} [Add α] [Neg α]: Sub α where
  sub a b := a + -b

class Ring (α: Type _) extends Zero α, One α, Add α, Neg α, Mul α where
  zero_ne_one: (0:α) ≠ 1
  add_assoc (a b c: α): (a + b) + c = a + (b + c)
  add_comm (a b: α): a + b = b + a
  add_zero (a: α): a + 0 = a
  add_neg (a: α): a + -a = 0
  mul_assoc (a b c: α): (a * b) * c = a * (b * c)
  mul_one (a: α): a * 1 = a
  one_mul (a: α): 1 * a = a
  mul_add (x a b: α): x * (a + b) = x * a + x * b
  add_mul (x a b: α): (a + b) * x = a * x + b * x

namespace Ring
  variable [self: Ring α]
  @[simp] theorem zero_eq: self.zero = 0 := rfl
  @[simp] theorem one_eq: self.one = 1 := rfl
  @[simp] theorem add_eq (a b): self.add a b = a + b := rfl
  @[simp] theorem neg_eq (a): self.neg a = -a := rfl
  @[simp] theorem sub_eq (a b: α): a - b = a + -b := rfl
  @[simp] theorem mul_eq (a b): self.mul a b = a * b := rfl
end Ring

instance {α} [R: Ring α]: AbGroup R.add where
  comm := R.add_comm
  assoc := R.add_assoc
  unit := 0
  op_unit := R.add_zero
  unit_op a := by simp; rw [R.add_comm, R.add_zero]
  inv := R.neg
  op_inv := R.add_neg
  inv_op a := by simp; rw [R.add_comm, R.add_neg]

instance {α} [R: Ring α]: Monoid R.mul where
  assoc := R.mul_assoc
  unit := 1
  unit_op := R.one_mul
  op_unit := R.mul_one
