import ApostolCalculus.Logic
set_option autoImplicit false

@[inherit_doc] infixl:70 "⬝" => HMul.hMul
macro_rules | `($x ⬝ $y) => `(binop% HMul.hMul $x $y)

structure Uniq {α} (P: α → Prop) (a: α): Prop where
  sat: P a
  uniq (b: α): P b → b = a
-- instance {α} {P: α → Prop} {a: α}: Coe (Uniq P a) (P a) where
--   coe u := u.sat

/-! ## I 3.2 The field axioms -/

axiom ℝ: Type
namespace ℝ
  protected axiom sum: ℝ → ℝ → ℝ
  noncomputable instance: Add ℝ where add := ℝ.sum

  protected axiom product: ℝ → ℝ → ℝ
  noncomputable instance: Mul ℝ where mul := ℝ.product

  variable (x y z: ℝ)

  /-- Axiom 1. Commutative laws. -/
  protected axiom comm: x + y = y + x ∧ x⬝y = y⬝x
  /-- Axiom 2. Associative laws. -/
  protected axiom assoc: x + (y + z) = (x + y) + z ∧ x⬝(y⬝z) = (x⬝y)⬝z
  /-- Axiom 3. Distributive law. -/
  protected axiom distrib: x⬝(y + z) = x⬝y + x⬝z
  /-- Axiom 4. Existence of identity elements. -/
  protected axiom zero: ℝ
  @[default_instance] noncomputable instance: Zero ℝ where zero := ℝ.zero
  /-- Axiom 4. Existence of identity elements. -/
  protected axiom one: ℝ
  @[default_instance] noncomputable instance: One ℝ where one := ℝ.one
  /-- Axiom 4. Existence of identity elements. -/
  protected axiom identities: 0 ≠ 1 ∧ ∀ x: ℝ, x + 0 = x ∧ 1⬝x = x
  /-- Axiom 5. Existence of negatives. -/
  protected axiom negatives (x: ℝ): ∃ y: ℝ, x + y = 0
  /-- Axiom 6. Existence of reciprocals. -/
  protected axiom reciprocals {x: ℝ}: x ≠ 0 → ∃ y: ℝ, x⬝y = 1


  variable (a b c d: ℝ)

section «colloraries of axioms»
  protected theorem add_comm: a + b = b + a := (ℝ.comm a b).left
  protected theorem mul_comm: a⬝b = b⬝a := (ℝ.comm a b).right
  protected theorem add_assoc: a + (b + c) = (a + b) + c := (ℝ.assoc a b c).left
  protected theorem mul_assoc: a⬝(b⬝c) = (a⬝b)⬝c := (ℝ.assoc a b c).right
  protected theorem mul_add: a⬝(b + c) = a⬝b + a⬝c := ℝ.distrib a b c
  protected theorem add_mul: (a + b)⬝c = a⬝c + b⬝c := by simp only [ℝ.mul_add, ℝ.mul_comm]
  @[simp] protected theorem zero_eq: ℝ.zero = 0 := rfl
  @[simp] protected theorem one_eq: ℝ.one = 1 := rfl
  protected theorem zero_ne_one: 0 ≠ 1 := ℝ.identities.left
  @[simp] protected theorem add_zero: a + 0 = a := (ℝ.identities.right a).left
  @[simp] protected theorem zero_add: 0 + a = a := by simp only [ℝ.add_zero, ℝ.add_comm]
  @[simp] protected theorem one_mul: 1⬝a = a := (ℝ.identities.right a).right
  @[simp] protected theorem mul_one: a⬝1 = a := by rw [ℝ.mul_comm, ℝ.one_mul]
end «colloraries of axioms»

  theorem neg_add_cancel {a «-a»: ℝ} (b: ℝ): a + «-a» = 0 → «-a» + (a + b) = b
    | add_neg =>
      have neg_add: «-a» + a = 0 := by rw [ℝ.add_comm, add_neg]
      by rw [ℝ.add_assoc, neg_add, ℝ.zero_add]
  /-- Theorem I.1. Cancellation law for addition. -/
  protected theorem cancel_add: a + b = a + c → b = c :=
    have ⟨«-a», add_neg⟩ := ℝ.negatives a
    have g (x: ℝ) := neg_add_cancel x add_neg
    fun h =>
      have h': «-a» + (a + b) = «-a» + (a + c) := congrArg («-a» + .) h
      by rw [g, g] at h'; exact h'

  /-- Theorem I.2. Possibility of subtraction. -/
  theorem sub_uniq_ex: ∃! x: ℝ, a + x = b :=
    have ⟨«-a», add_neg⟩ := ℝ.negatives a
    ⟨ «-a» + b
    , by simp; rw [ℝ.add_assoc, add_neg, ℝ.zero_add]
    , by intros y h; rw [←h]; exact (neg_add_cancel y add_neg).symm
    ⟩

  protected axiom subtraction: ℝ → ℝ → ℝ
  noncomputable instance: Sub ℝ where sub := ℝ.subtraction
  @[simp] protected axiom sub_def: a + (b - a) = b
  noncomputable instance: Neg ℝ where neg a := 0 - a
  @[simp] protected theorem sub_self: a + -a = 0 := ℝ.sub_def a 0
  @[simp] protected theorem self_add_inv: a + -a = 0 := ℝ.sub_self a
  @[simp] protected theorem inv_add_self: -a + a = 0 := by rw [ℝ.add_comm, ℝ.self_add_inv]
  protected theorem sub_uniq {x: ℝ} (h: a + x = b): x = b - a :=
    have ⟨y, _, uniq⟩ := sub_uniq_ex a b
    calc x = y := uniq x h
         _ = b - a := (uniq (b - a) (ℝ.sub_def a b)).symm
  protected abbrev neg_uniq {x: ℝ} := @ℝ.sub_uniq a 0 x


  /-- Theorem I.3. -/
  protected theorem add_neg: b - a = b + -a :=
    suffices a + (b + -a) = b from (ℝ.sub_uniq a b this).symm
    by rw [ℝ.add_assoc, ℝ.add_comm a, ←ℝ.add_assoc, ℝ.self_add_inv, ℝ.add_zero]
      

  /-- Theorem I.4. -/
  @[simp] protected theorem neg_neg: -(-a) = a :=
    suffices -a + a = 0 from (ℝ.neg_uniq _ this).symm
    by rw [ℝ.add_comm, ℝ.self_add_inv]

  /-! ## I 3.3 Exercises -/

  /-- Theorem I.5. -/
  protected theorem mul_sub: a⬝(b - c) = a⬝b - a⬝c :=
    suffices a⬝c + a⬝(b - c) = a⬝b from ℝ.sub_uniq _ _ this
    by rw [←ℝ.mul_add, ℝ.sub_def]

  /-- Theorem I.6. -/
  @[simp] protected theorem zero_mul: 0⬝a = 0 := by
    apply ℝ.cancel_add (0⬝a)
    rw [ℝ.add_zero, ←ℝ.add_mul, ℝ.add_zero]
  /-- Theorem I.6. -/
  @[simp] protected theorem mul_zero: a⬝0 = 0 := by rw [ℝ.mul_comm, ℝ.zero_mul]

  /-- Structurally identical to `neg_add_cancel` -/
  theorem inv_mul_cancel {a «a⁻¹»: ℝ} (b: ℝ): a⬝«a⁻¹» = 1 → «a⁻¹»⬝(a⬝b) = b
    | mul_inv =>
      have inv_mul: «a⁻¹»⬝a = 1 := by rw [ℝ.mul_comm, mul_inv]
      by rw [ℝ.mul_assoc, inv_mul, ℝ.one_mul]
  /-- Theorem I.7. Cancellation law for multiplication. -/
  protected theorem cancel_mul: a⬝b = a⬝c → a ≠ 0 → b = c
    | h, nonzero =>
      have ⟨«a⁻¹», mul_inv⟩ := ℝ.reciprocals nonzero
      have g (x: ℝ) := inv_mul_cancel x mul_inv
      suffices «a⁻¹»⬝(a⬝b) = «a⁻¹»⬝(a⬝c) from by rw [g, g] at this; exact this
      congrArg («a⁻¹»⬝ .) h
  protected theorem one_uniq {u: ℝ} (h: ∀ x, u⬝x = x): u = 1 :=
    by rw [←h 1, ℝ.mul_one]

  /-- Theorem I.8. Possibility of division. -/
  theorem div_uniq_ex (a: ℝˣ) (b: ℝ): ∃! x: ℝ, a⬝x = b :=
    have ⟨«a⁻¹», mul_inv⟩ := ℝ.reciprocals a.2
    ⟨ «a⁻¹»⬝b
    , by simp; rw [ℝ.mul_assoc, mul_inv, ℝ.one_mul]
    , by intros y h; rw [←h, inv_mul_cancel y mul_inv]
    ⟩

  protected axiom quotient: ℝ → ℝˣ → ℝ
  noncomputable instance: HDiv ℝ ℝˣ ℝ where hDiv := ℝ.quotient
  @[simp] protected axiom div_def (a: ℝˣ) (b: ℝ): a⬝(b/a) = b
  noncomputable instance: Inv ℝ where inv a := {
    val := 1/a
    property := by
      intros h; apply ℝ.zero_ne_one
      have h := congrArg (a.val ⬝ .) h; simp at h; exact h.symm
  }
  -- @[simp] protected theorem div_self (a: ℝˣ): a.val / a = 1 := ℝ.div_def a 1
  @[simp] protected theorem self_mul_inv (a: ℝˣ): a.val ⬝ a⁻¹ = 1 := ℝ.div_def a 1
  @[simp] protected theorem inv_mul_self (a: ℝˣ): a⁻¹ ⬝ a.val = 1 :=
    by rw [ℝ.mul_comm, ℝ.self_mul_inv]
  protected theorem div_uniq (a: ℝˣ) (b: ℝ) {x: ℝ} (h: a⬝x = b): x = b/a :=
    have ⟨y, _, uniq⟩ := div_uniq_ex a b
    calc x = y := uniq x h
         _ = b/a := (uniq _ (ℝ.div_def a b)).symm
  protected theorem inv_uniq (a: ℝˣ) {x: ℝ} (h: a⬝x = 1): x = a⁻¹ := ℝ.div_uniq a 1 h

  noncomputable instance: One ℝˣ where one := ⟨1, ℝ.zero_ne_one.symm⟩

  /-- Theorem I.9. -/
  protected theorem mul_inv (a: ℝˣ): b/a = b⬝a⁻¹ :=
    suffices a⬝(b⬝a⁻¹) = b from (ℝ.div_uniq _ _ this).symm
    by rw [ℝ.mul_comm b, ℝ.mul_assoc, ℝ.self_mul_inv, ℝ.one_mul]

  /-- Theorem I.10. -/
  @[simp] protected theorem inv_inv (a: ℝˣ): a⁻¹⁻¹ = a :=
    (ℝ.inv_uniq a⁻¹ (_: a⁻¹ ⬝ a = 1)).symm

  /-- Theorem I.11. -/
  protected theorem integral_domain₁ {a b: ℝ}: a⬝b = 0 → a = 0 ∨ b = 0 := sorry
  protected theorem integral_domain₂ {a b: ℝ}: a ≠ 0 → b ≠ 0 → a⬝b ≠ 0
    | ha, hb, h => (ℝ.integral_domain₁ h).elim ha hb
  protected theorem integral_domain₃ (a b: ℝˣ): a.val ⬝ b.val ≠ 0 :=
    ℝ.integral_domain₂ a.2 b.2
  noncomputable instance: Mul ℝˣ where mul a b := ⟨a⬝b, ℝ.integral_domain₃ a b⟩
  noncomputable instance: Div ℝˣ where div a b := {
    val := a.val / b
    property := by rw [ℝ.mul_inv]; exact ℝ.integral_domain₃ a b⁻¹
  }

  /-- Theorem I.12. -/
  protected theorem neg_mul: (-a)⬝b = -(a⬝b) := sorry
  /-- Theorem I.12. -/
  @[simp] protected theorem neg_mul_neg: (-a)⬝(-b) = a⬝b := sorry

  /-- Theorem I.13. -/
  protected theorem div_add_div (b d: ℝˣ): a/b + c/d = (a⬝d + b⬝c)/(b⬝d) := sorry

  /-- Theorem I.14. -/
  protected theorem div_mul_div (b d: ℝˣ): (a/b)⬝(c/d) = (a⬝c)/(b⬝d) := sorry

  /-- Theorem I.15. -/
  protected theorem div_div_div (b c d: ℝˣ): (a/b)/(c/d) = (a⬝d)/(b⬝c) := sorry

  @[simp] protected theorem neg_zero: -0 = 0 :=
    (ℝ.neg_uniq 0 (ℝ.add_zero 0)).symm
  noncomputable instance: Neg ℝˣ where neg a := {
    val := -a
    property := fun h => by have h := congrArg (- .) h; simp at h; exact a.2 h
  }
  protected theorem one_inv: 1⁻¹.val = 1 := sorry
  protected theorem zero_not_inv: 0⬝a ≠ 1 := sorry
  protected theorem neg_add: -(a + b) = -a - b := sorry
  protected theorem neg_sub: -(a - b) = -a + b := sorry
  protected theorem sub_add_sub: (a - b) + (b - c) = a - c := sorry
  protected theorem inv_mul_inv (a b: ℝˣ): (a⬝b)⁻¹ = a⁻¹⬝b⁻¹ := sorry
  protected theorem neg_div (b: ℝˣ): (-a)/b = -(a/b) := sorry
  protected theorem div_neg (b: ℝˣ): a/(-b) = -(a/b) := sorry
  protected theorem div_sub_div (b d: ℝˣ): a/b - c/d = (a⬝d - b⬝c)/(b⬝d) := sorry



  /-! ## I 3.4 The order axioms -/

  /-- Positiveness. -/
  protected axiom positive: ℝ → Prop
  /-- Axiom 7. -/
  protected axiom pos_closure: x.positive ∧ y.positive → (x + y).positive ∧ (x⬝y).positive
  /-- Axiom 8. -/
  protected axiom pos_dichotomy: x ≠ 0 → (x.positive ∨ (-x).positive) ∧ ¬(x.positive ∧ (-x).positive)
  /-- Axiom 9. -/
  protected axiom zero_not_pos: ¬ℝ.positive 0

  instance: LT ℝ where lt x y := (y - x).positive
  instance: LE ℝ where le x y := x < y ∨ x = y

  theorem pos_def: 0 < x ↔ x.positive := sorry
  
  /-- Theorem I.16. Trichotomy law. FIXME -/
  theorem trichotomy: a < b ∨ b < a ∨ a = b := sorry
  /-- Theorem I.17. Transitive law. -/
  theorem lt_trans: a < b → b < c → a < c := sorry
  /-- Theorem I.18. -/
  theorem add_lt_add: a < b → a + c < b + c := sorry
  /-- Theorem I.19. -/
  theorem mul_lt_mul: a < b → c > 0 → a⬝c < b⬝c := sorry
  
  protected noncomputable abbrev square (x: ℝ): ℝ := x⬝x
  postfix:arg "²" => ℝ.square
  /-- Theorem I.20. -/
  theorem pos_square: a ≠ 0 → a² > 0 := sorry
  /-- Theorem I.21. -/
  theorem zero_lt_one: 0 < 1 := sorry

  /-! ## I 3.5 Exercises -/

  /-- Theorem I.22. -/
  example: a < b → c < 0 → a⬝c > b⬝c := sorry
  /-- Theorem I.23. -/
  example: a < b → -a > -b := sorry
  /-- Theorem I.23. -/
  example: a < 0 → -a > 0 := sorry
  /-- Theorem I.24. -/
  example: a⬝b > 0 → (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) := sorry
  /-- Theorem I.25. -/
  example: a < c → b < d → a + b < c + d := sorry

  example: ∀ x: ℝ, x² + 1 ≠ 0 := sorry
  example: a < 0 → b < 0 → a + b < 0 := sorry
  example: (a > 0 → 1/a > 0) ∧ (a < 0 → 1/a < 0) := sorry
  example: 0 < a → a < b → 0 < b⁻¹ ∧ b⁻¹ < a⁻¹ := sorry
  theorem le_trans: a ≤ b → b ≤ c → a ≤ c := sorry
  example: a ≤ b → b ≤ c → a = c → b = c := sorry
  example: (a² + b² ≥ 0) ∧ (¬(a = 0 ∧ b = 0) → a² + b² > 0) := sorry
  example: ∀ a: ℝ, ¬∀ x: ℝ, x ≤ a := sorry
  example: (∀ h: ℝ, 0 ≤ x ∧ x < h) → x = 0 := sorry
end ℝ

/-- Positive numbers. -/
abbrev «ℝ⁺» := Subtype ℝ.positive

/-! ## 1 3.6 Integers and rational numbers -/
protected inductive ℝ.inductive: ℝ → Prop
  | one: ℝ.inductive 1
  | succ {x: ℝ}: x.inductive → (x + 1).inductive 
