import ApostolCalculus.Nat
set_option autoImplicit false

/-! # Integers -/

inductive ℤ | ofNat (n: ℕ) | negSucc (n: ℕ)

instance: Coe ℕ ℤ where coe := .ofNat
instance: OfNat ℤ 0 where ofNat := .ofNat 0

#check Int.subNatNat
def ℕ.sub (a b: ℕ): ℤ := match b ∸ a with
  | 0 => a ∸ b -- b ≤ a
  | .succ n => .negSucc n
instance: HSub ℕ ℕ ℤ where hSub := ℕ.sub

namespace ℕ

@[simp] theorem sub.def (a b: ℕ): a.sub b = a - b := rfl
@[simp] theorem sub_self (a: ℕ): a - a = 0 := by rw [←sub.def]; unfold sub; simp
#check monus_eq_zero_of_le
@[simp] theorem monus_self_add (a: ℕ): (b: ℕ) → a ∸ (a + b) = 0
  | 0 => a.monus_self
  | succ b => congrArg ℕ.pred (monus_self_add a b)
@[simp] theorem monus_add_self (a b: ℕ): a ∸ (b + a) = 0 := by simp [ℕ.add_comm]
@[simp] theorem self_add_monus (a b: ℕ): a + b ∸ a = b :=
  match a with
  | 0 => b.zero_add
  | succ a =>
    calc a.succ + b ∸ a.succ
        = (a + b).succ ∸ a.succ := ℕ.succ_add a b ▸ rfl
      _ = a + b ∸ a := succ_monus_succ (a + b) a
      _ = b := self_add_monus a b
@[simp] theorem add_self_monus (a b: ℕ): b + a ∸ a = b := by simp [ℕ.add_comm]

end ℕ

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
instance: Neg ℤ where neg | ofNat n => n.neg | negSucc n => n.succ

#check Int.sub
instance: Sub ℤ where sub a b := a + -b

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

namespace ℤ
-- variable (x y z: ℤ)

@[simp] theorem add_zero: (x: ℤ) → x + 0 = x
  | ofNat a
  | negSucc a => rfl

@[simp] theorem zero_add: (x: ℤ) → 0 + x = x
  | ofNat a => congrArg ofNat (a.zero_add)
  | negSucc a => rfl

theorem add_comm: (x y: ℤ) → x + y = y + x
  | ofNat a, ofNat b => congrArg ofNat (ℕ.add_comm a b)
  | ofNat a, negSucc b
  | negSucc a, ofNat b => rfl
  | negSucc a, negSucc b => congrArg (negSucc ∘ ℕ.succ) (ℕ.add_comm a b)

@[simp] theorem neg_zero: -0 = 0 := rfl
@[simp] theorem neg_neg: (x: ℤ) → - -x = x
  | 0
  | ℕ.succ a
  | negSucc a => rfl
@[simp] theorem sub_zero: (x: ℤ) → x - 0 = x
  | ofNat a
  | negSucc a => rfl
@[simp] theorem zero_sub: (x: ℤ) → 0 - x = -x
  | 0
  | ℕ.succ a => rfl
  | negSucc a => zero_add a.succ
@[simp] theorem sub_self: (x: ℤ) → x - x = 0
  | 0 => rfl
  | ℕ.succ a
  | negSucc a => a.succ.sub_self

/-! # Equality -/

instance: (x y: ℤ) → Decidable (x = y)
  | ofNat a, ofNat b => if e: a = b then isTrue (e ▸ rfl) else isFalse (e ∘ ofNat.inj)
  | ofNat a, negSucc b | negSucc a, ofNat b => isFalse (nomatch .) -- isFalse ℤ.noConfusion
  | negSucc a, negSucc b => if e: a = b then isTrue (e ▸ rfl) else isFalse (e ∘ negSucc.inj)

/-! # Inequality -/

/-- Non-negative, i.e., postive, contrary to stricty positive. -/
inductive Pos: ℤ → Prop
  | abs (a: ℕ): Pos a

instance: (x: ℤ) → Decidable (Pos x)
  | ofNat a => isTrue ⟨a⟩
  | negSucc a => isFalse (nomatch .)

-- inductive lei: ℤ → ℤ → Prop
--   | refl x: lei x x
--   | step {x y}: lei x y → lei x y.succ

/-- `≤` according to addition. -/
def le_add (x y: ℤ): Prop := ∃ d: ℕ, x + d = y
/-- `≤` according to subtraction. -/
def le_sub (x y: ℤ): Prop := Pos (x - y)

section
  @[inherit_doc] local infix:50 " ≤+ "  => le_add
  @[inherit_doc] local infix:50 " ≤- "  => le_sub

  example (x y: ℤ): x ≤+ y → x ≤- y
    | ⟨d, hd⟩ => sorry
  example (x y: ℤ): x ≤- y → x ≤+ y := sorry
end

theorem add_sub_self: (x y: ℤ) → x + y - x = y
  | 0, y => y.zero_add.symm ▸ y.sub_zero
  | ℕ.succ a, ofNat b =>
    show a.succ + b - a.succ = b from by rw [←ℕ.sub.def]; unfold ℕ.sub; simp
  | ℕ.succ a, negSucc b =>
    show a.succ - b.succ - a.succ = negSucc b from sorry
  | negSucc a, ofNat b => sorry
  | negSucc a, negSucc b => sorry

protected theorem add_assoc_aux1 (a b c: ℕ)
  : a - b.succ + negSucc c = a - (b + c).succ.succ := sorry

theorem add_assoc: (x y z: ℤ) → x + y + z = x + (y + z)
  | ofNat a, ofNat b, ofNat c => congrArg ofNat (ℕ.add_assoc a b c)
  | ofNat a, ofNat b, negSucc c =>
    calc a + b - c.succ = ofNat a + (b - c.succ) := sorry
  | ofNat a, negSucc b, ofNat c =>
    calc a - b.succ + c = ofNat a + (c - b.succ) := sorry
  | negSucc a, ofNat b, ofNat c =>
    calc b - a.succ + ofNat c = b + c - a.succ := sorry
  | negSucc a, ofNat b, negSucc c =>
    calc b - a.succ + negSucc c = negSucc a + (b - c.succ) := sorry
  | ofNat a, negSucc b, negSucc c =>
    calc a - b.succ + negSucc c = a - (b + c).succ.succ :=
      ℤ.add_assoc_aux1 a b c
  | negSucc a, negSucc b, ofNat c =>
    calc c - (a + b).succ.succ
        = c - (b + a).succ.succ := by rw [ℕ.add_comm]
      _ = c - b.succ + negSucc a := (ℤ.add_assoc_aux1 _ _ _).symm
      _ = negSucc a + (c - b.succ) := ℤ.add_comm _ _
  | negSucc a, negSucc b, negSucc c => congrArg (negSucc ∘ ℕ.succ) <|
    calc (a + b).succ + c
        = (a + b + c).succ := ℕ.succ_add (a + b) c
      _ = (a + (b + c)).succ := congrArg ℕ.succ (ℕ.add_assoc a b c)

end ℤ

namespace ℕ



end ℕ
