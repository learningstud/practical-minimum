import ApostolCalculus.Logic
set_option autoImplicit false

/-! ## Natural Numbers -/

inductive ℕ | protected zero | succ (n: ℕ)
namespace ℕ

/-! ## Constructors -/

instance: Zero ℕ where zero := ℕ.zero

#check id.def
@[simp] protected theorem zero.def: ℕ.zero = 0 := rfl
example: ℕ.zero = 0 := by simp

theorem succ_eq_succ {a b: ℕ}: a = b ↔ a.succ = b.succ := ⟨congrArg succ, succ.inj⟩
#check Nat.succ_ne_zero
theorem succ_ne_zero (a: ℕ): a.succ ≠ 0 := ℕ.noConfusion

/-! ## Equality
Due to `decide` and `instLawfulBEqInstBEq`, we only have to establish `DecidableEq` to get `BEq` and `LawfulBEq`.
-/

#check Nat.decEq
protected instance decEq: (a b: ℕ) → Decidable (a = b)
  | 0, 0 => isTrue rfl
  | 0, succ b => isFalse b.succ_ne_zero.symm
  | succ a, 0 => isFalse a.succ_ne_zero
  | succ a, succ b => have := a.decEq b; decidable_of_decidable_of_iff succ_eq_succ
    -- match a.decEq b with
    -- | isFalse h => isFalse (h ∘ succ.inj)
    -- | isTrue h => isTrue (congrArg succ h)

example: DecidableEq ℕ := inferInstance
#check decEq
example (a b: ℕ): Decidable (a = b) := decEq a b
#check decide
#check instBEq
example: BEq ℕ := inferInstance
#check instLawfulBEqInstBEq
example: LawfulBEq ℕ := inferInstance

example (a b: ℕ): a = b ∨ a ≠ b := if h: a = b then .inl h else .inr h

/-! ## Inequalities -/

#check Nat.le
protected inductive le (a: ℕ): ℕ → Prop
  | refl: a.le a
  | step {b}: a.le b → a.le b.succ
protected instance instLe: LE ℕ where le := ℕ.le
@[simp] protected theorem le.def (a b: ℕ): a.le b = (a ≤ b) := rfl
protected instance instLt: LT ℕ where lt a b := a.succ ≤ b
@[simp] protected theorem lt.def (a b: ℕ): LT.lt a b = (a < b) := rfl

#check Nat.not_succ_le_zero
#check Nat.not_lt_zero
theorem not_lt_zero (a: ℕ): ¬a < 0 := (nomatch .)

#check Nat.zero_le
theorem zero_le: (a: ℕ) → 0 ≤ a
  | 0 => .refl
  | succ a => a.zero_le.step

#check Nat.le_of_succ_le_succ
#check Nat.succ_le_succ
theorem succ_le_succ {a b: ℕ}: a ≤ b ↔ a.succ ≤ b.succ :=
  let rec mp {a b: ℕ}: a ≤ b → a.succ ≤ b.succ
    | .refl => .refl
    | .step h => (mp h).step
  let rec mpr {a b: ℕ}: a.succ ≤ b.succ → a ≤ b
    | .refl => .refl
    | .step h => match b with | succ b => (mpr h).step
  ⟨mp, mpr⟩

#check Nat.ble
#check Nat.decLe
protected instance decLe: (a b: ℕ) → Decidable (a ≤ b)
  | 0, 0 => isTrue .refl
  | 0, succ b => isTrue b.succ.zero_le
  | succ a, 0 => isFalse a.not_lt_zero
  | succ a, succ b => have := a.decLe b; decidable_of_decidable_of_iff succ_le_succ
    -- match a.decLe b with
    -- | isFalse h => isFalse (h ∘ le_of_succ_le_succ)
    -- | isTrue h => isTrue (succ_le_succ h)

#check Nat.decLt
protected instance decLt (a b: ℕ): Decidable (a < b) := a.succ.decLe b
#check instOrdNat
instance: Ord ℕ where compare a b := compareOfLessAndEq a b

#check instMinNat
instance: Min ℕ := minOfLe
instance: Max ℕ := maxOfLe

/-! ## Reflexivity, irreflexivity, transivitity, antisymmetry -/

#check Nat.le_trans
protected theorem le_trans {a b c: ℕ} (h: a ≤ b): b ≤ c → a ≤ c
  | .refl => h
  | .step h' => (ℕ.le_trans h h').step
#check Nat.instTransNatLtInstLTNatLeInstLENat
instance: @Trans ℕ ℕ ℕ (.≤.) (.≤.) (.≤.) where trans := ℕ.le_trans
instance: @Trans ℕ ℕ ℕ (.<.) (.<.) (.<.) where trans h h' := ℕ.le_trans h.step h'
instance: @Trans ℕ ℕ ℕ (.≤.) (.<.) (.<.) where trans h h' := ℕ.le_trans (ℕ.succ_le_succ.mp h) h'
instance: @Trans ℕ ℕ ℕ (.<.) (.≤.) (.<.) where trans := ℕ.le_trans
-- instance: @Trans ℕ ℕ ℕ (.<.) (.=.) (.<.) where trans h eq := eq ▸ h

-- #check Nat.lt_trans
-- protected theorem lt_trans {a b c: ℕ} (h: a < b) (h': b < c): a < c :=
--   ℕ.le_trans h.step h'
-- instance: @Trans ℕ ℕ ℕ (.<.) (.<.) (.<.) where trans := ℕ.lt_trans

-- #check Nat.lt_of_le_of_lt
-- theorem lt_of_le_of_lt {a b c: ℕ} (h: a ≤ b) (h': b < c): a < c :=
--   ℕ.le_trans (ℕ.succ_le_succ.mp h) h'
-- instance: @Trans ℕ ℕ ℕ (.≤.) (.<.) (.<.) where trans := lt_of_le_of_lt

#check Nat.not_succ_le_self
#check Nat.lt_irrefl
protected theorem lt_irrefl: (a: ℕ) → ¬a < a
  | 0 => ℕ.not_lt_zero 0
  | succ a => a.lt_irrefl ∘ ℕ.succ_le_succ.mpr
  -- a.rec (ℕ.not_lt_zero 0) fun a ih h => ih (ℕ.succ_le_succ.mpr h)

#check Antisymm
#check Nat.le_antisymm
#check Nat.instAntisymmNatLeInstLENat
instance: @Antisymm ℕ (.≤.) where
  antisymm
  | .refl, _ => rfl
  | .step h, h' => (ℕ.lt_irrefl _ (ℕ.le_trans h' h)).elim

/-! ## Constructor inequalities -/

#check Nat.eq_zero_of_le_zero
theorem eq_zero_of_le_zero: {a: ℕ} → a ≤ 0 → a = 0
  | 0, _ => rfl
  | succ a, h => (a.not_lt_zero h).elim
example {a: ℕ} (h: a ≤ 0): a = 0 := Antisymm.antisymm h a.zero_le

#check Nat.le_of_eq
theorem le_of_eq {a b: ℕ}: a = b → a ≤ b
  | rfl => .refl

#check Nat.le_of_succ_le
#check Nat.le_of_lt
theorem le_of_lt {a b: ℕ} (h: a < b): a ≤ b := ℕ.succ_le_succ.mpr h.step

#check Nat.le_succ
theorem le_succ (a: ℕ): a ≤ a.succ := .step .refl

#check Nat.zero_lt_succ
#check Nat.succ_pos
theorem succ_pos (a: ℕ): 0 < a.succ := ℕ.succ_le_succ.mp a.zero_le

#check Nat.not_eq_zero_of_lt
theorem not_eq_zero_of_lt {a b: ℕ}: a < b → b ≠ 0
  | h, hb => a.not_lt_zero (trans h hb)

#check Nat.zero_lt_of_ne_zero
theorem zero_lt_of_ne_zero {a: ℕ}: a ≠ 0 ↔ 0 < a :=
  ⟨a.casesOn (absurd rfl) fun a _ => a.succ_pos, not_eq_zero_of_lt⟩

#check Nat.eq_zero_or_pos
theorem eq_zero_or_pos: (a: ℕ) → a = 0 ∨ a > 0
  | 0 => .inl rfl
  | succ a => .inr a.succ_pos
example (a: ℕ): a = 0 ∨ a > 0 :=
  if h: a = 0 then .inl h else .inr (zero_lt_of_ne_zero.mp h)

#check Nat.eq_or_lt_of_le
theorem eq_or_lt_of_le {a b: ℕ}: a ≤ b → a = b ∨ a < b
  | .refl => .inl rfl
  | .step h =>
    match eq_or_lt_of_le h with
    | .inl h => .inr (le_of_eq (congrArg succ h))
    | .inr h => .inr (trans h (ℕ.le_succ _))

#check Nat.lt_wfRel
/-- `<` for `ℕ` is a well-founded relation.
This instance prevents `decreasing_by` to use `sizeOf` which maps to `Nat`.
-/
instance lt_wfRel: WellFoundedRelation ℕ where
  rel := LT.lt
  wf := .intro <| ℕ.rec
    (.intro _ fun y hy => (y.not_lt_zero hy).elim)
    fun x ih => .intro _ fun y hy =>
      (ℕ.eq_or_lt_of_le (ℕ.succ_le_succ.mpr hy)).elim (. ▸ ih) ih.inv

example {a b: ℕ}: a ≤ b ↔ a = b ∨ a < b :=
  ⟨eq_or_lt_of_le, fun h => h.elim le_of_eq le_of_lt⟩

#check Nat.lt_or_ge
theorem lt_or_ge (a: ℕ): (b: ℕ) → a < b ∨ a ≥ b
  | 0 => .inr a.zero_le
  | succ b =>
    match lt_or_ge a b with
    | .inl h => .inl (trans h b.le_succ)
    | .inr h =>
      match eq_or_lt_of_le h with
      | .inl h => .inl (le_of_eq (congrArg succ h.symm))
      | .inr h => .inr h

#check Nat.le_total
theorem le_total (a b: ℕ): a ≤ b ∨ b ≤ a :=
  match lt_or_ge a b with
  | .inl h => .inl (le_of_lt h)
  | .inr h => .inr h

#check Nat.ne_of_lt
theorem ne_of_lt {a b: ℕ}: a < b → a ≠ b
  | hlt, heq => b.lt_irrefl (heq ▸ hlt)

#check Nat.gt_of_not_le
theorem gt_of_not_le {a b: ℕ} (h: ¬a ≤ b): a > b :=
  match lt_or_ge b a with
  | .inl h' => h'
  | .inr h' => (h h').elim

/-
/-! ## Finities-/

#check Fin
abbrev 𝔽 (n: ℕ) := { x: ℕ // x < n}
instance: CoeSort ℕ Type where coe := 𝔽

def ofNat: Nat → ℕ | 0 => 0 | .succ n => ofNat n
instance (n: Nat): OfNat ℕ n where ofNat := ofNat n
-- @[default_instance] instance: Coe Nat ℕ where coe := ofNat 
instance (n: Nat): OfNat Type n where
  ofNat := 𝔽 (ofNat n)

example: 1 = 𝔽 1 := rfl
example: (a b: 1) → a = b
  | ⟨a, ha⟩, ⟨b, hb⟩ => sorry
-/

/-! ## One -/

instance: One ℕ where one := ℕ.succ 0
@[simp] protected theorem one.def: ℕ.succ 0 = 1 := rfl
example: ℕ.succ 0 = 1 := by simp

theorem eq_zero_of_lt_one: {a: ℕ} → a < 1 → a = 0
  | 0, _ => rfl
  | succ a, h => (a.not_lt_zero (ℕ.succ_le_succ.mpr h)).elim

/-! ## Predecessor -/

#check Nat.pred
protected def pred: ℕ → ℕ | 0 => 0 | succ a => a

#check Nat.pred_zero
@[simp] theorem pred_zero: ℕ.pred 0 = 0 := rfl

#check Nat.pred_succ
@[simp] theorem pred_succ (a: ℕ): a.succ.pred = a := rfl

#check Nat.succ_pred
theorem succ_pred: {a: ℕ} → a ≠ 0 → a.pred.succ = a
  | 0 => absurd rfl
  | succ a => fun _ => rfl

#check Nat.pred_le
theorem pred_le: (a: ℕ) → a.pred ≤ a
  | 0 => .refl
  | succ a => a.le_succ

#check Nat.pred_le_pred
theorem pred_le_pred: {a b: ℕ} → a ≤ b → a.pred ≤ b.pred
  | _, _, .refl => .refl
  | 0, succ b, _ => b.zero_le
  | a, _, .step h => ℕ.le_trans a.pred_le h

/-! ## Addition, multiplication, exponentiation -/

#check Nat.add
protected def add (a: ℕ): ℕ → ℕ | 0 => a | succ b => (a.add b).succ
instance: Add ℕ where add := ℕ.add
@[simp] protected theorem add.def (a b: ℕ): a.add b = a + b := rfl

@[simp] protected theorem add_zero (a: ℕ): a + 0 = a := rfl
@[simp] protected theorem zero_add: (a: ℕ) → 0 + a = a
  | 0 => rfl
  | succ a => congrArg succ a.zero_add

#check Nat.succ_add
protected theorem succ_add (a: ℕ): (b: ℕ) → a.succ + b = (a + b).succ
  | 0 => rfl
  | succ b => congrArg succ (a.succ_add b)

protected theorem add_succ (a b: ℕ): a + b.succ = (a + b).succ := rfl

#check Nat.add_comm
protected theorem add_comm (a: ℕ): (b: ℕ) → a + b = b + a
  | 0 => a.zero_add.symm
  | succ b => (congrArg succ (a.add_comm b)).trans (b.succ_add a).symm

#check Nat.mul
protected def mul (a: ℕ): ℕ → ℕ | 0 => 0 | succ b => (a.mul b).add a
instance: Mul ℕ where mul := ℕ.mul
@[simp] protected theorem mul.def (a b: ℕ): a.mul b = a * b := rfl

#check Nat.pow
protected def pow (a: ℕ): ℕ → ℕ | 0 => 1 | succ b => (a.pow b).mul a
instance: Pow ℕ ℕ where pow := ℕ.pow
@[simp] protected theorem pow.def (a b: ℕ): a.pow b = a ^ b := rfl

/-! ## Truncated subtraction (monus `∸`) -/

#check Nat.sub
/-- Truncated subtraction (`∸`) -/
protected def monus (a: ℕ): ℕ → ℕ | 0 => a | succ b => (a.monus b).pred
@[inherit_doc] infixl:65 " ∸ "   => ℕ.monus

#check Nat.sub_zero
@[simp] theorem monus_zero (a: ℕ): a ∸ 0 = a := rfl

#check Nat.zero_sub
@[simp] theorem zero_monus: (a: ℕ) → 0 ∸ a = 0
  | 0 => rfl
  | succ a => congrArg ℕ.pred a.zero_monus

theorem monus_succ (a b: ℕ): a ∸ b.succ = (a ∸ b).pred := rfl

#check Nat.succ_sub_succ_eq_sub
#check Nat.succ_sub_succ
theorem succ_monus_succ (a: ℕ): (b: ℕ) → a.succ ∸ b.succ = a ∸ b
  | 0 => rfl
  | succ b => congrArg ℕ.pred (a.succ_monus_succ b)

#check Nat.sub_self
@[simp] theorem monus_self: (a: ℕ) → a ∸ a = 0
  | 0 => rfl
  | succ a => (a.succ_monus_succ a).trans a.monus_self

#check Nat.sub_eq_zero_of_le
theorem monus_eq_zero_of_le {a b: ℕ}: a ≤ b → a ∸ b = 0
  | .refl => a.monus_self
  | .step h => congrArg ℕ.pred (monus_eq_zero_of_le h)

#check Nat.sub_le
theorem monus_le (a: ℕ): (b: ℕ) → a ∸ b ≤ a
  | 0 => .refl
  | succ b => trans (a ∸ b).pred_le (a.monus_le b)

#check Nat.sub_lt
theorem monus_lt: {a b: ℕ} → 0 < a → 0 < b → a ∸ b < a
  | 0, _, ha, _ => (ℕ.not_lt_zero 0 ha).elim
  | succ _, 0, _, hb => (ℕ.not_lt_zero 0 hb).elim
  | succ a, succ b, _, _ =>
    suffices a ∸ b < a.succ from a.succ_monus_succ b ▸ this
    ℕ.succ_le_succ.mp (a.monus_le b)

#check Nat.sub_ne_zero_of_lt
theorem sub_ne_zero_of_lt {a b: ℕ}: a < b → b ∸ a ≠ 0 := sorry

#check Nat.add_sub_of_le
theorem add_monus {a b: ℕ} (h: a ≤ b): a + (b ∸ a) = b := by
  match a with
  | 0 => simp
  | succ a => rw [monus_succ, ℕ.succ_add, ←ℕ.add_succ,
      succ_pred (sub_ne_zero_of_lt h), add_monus (trans a.le_succ h)]

#check Nat.sub_add_cancel
theorem monus_add {a b: ℕ} (h: a ≤ b): (b ∸ a) + a = b :=
  by rw [ℕ.add_comm, add_monus h]

/-
theorem le_of_monus_eq_zero: {a b: ℕ} → a ∸ b = 0 → a ≤ b
  | 0, b, _ => b.zero_le
  | succ a, 0, h => ℕ.noConfusion h --a.succ.le_of_eq h
  | succ a, succ b, h => sorry
-/

#check Nat.div_rec_lemma
theorem monus_lemma {a b: ℕ}: 0 < b ∧ b ≤ a → a ∸ b < a
  | ⟨hb, hba⟩ => monus_lt (trans hb hba) hb

#check ℕ.rec
#check Nat.div.inductionOn
protected def monusRec
  {motive: ℕ → ℕ → Sort _}
  (base: (a b: ℕ) → ¬(0 < b ∧ b ≤ a) → motive a b)
  (ind: (a b: ℕ) → 0 < b ∧ b ≤ a → motive (a ∸ b) b → motive a b)
  (a b: ℕ)
: motive a b
:=
  if h: 0 < b ∧ b ≤ a
  then ind a b h (ℕ.monusRec base ind (a ∸ b) b)
  else base a b h
termination_by monusRec => a
decreasing_by exact monus_lemma h

#print ℕ.monusRec

#check ℕ.recOn
@[inline] protected def monusRecOn
  {motive: ℕ → ℕ → Sort _}
  (a b: ℕ)
  (base: (a b: ℕ) → ¬(0 < b ∧ b ≤ a) → motive a b)
  (ind: (a b: ℕ) → 0 < b ∧ b ≤ a → motive (a ∸ b) b → motive a b)
: motive a b
:= ℕ.monusRec base ind a b

#check Nat.div
/-- Truncated division -/
protected def tdiv: ℕ → ℕ → ℕ :=
  ℕ.monusRec (fun _ _ _ => 0) fun _ _ _ c => c.succ
--   if 0 < b ∧ b ≤ a then ((a ∸ b).tdiv b).succ else 0
@[inherit_doc] infixl:70 " // "   => ℕ.tdiv

#check Nat.modCore
#check Nat.mod
/-- Modulo where `0 (mod n)` is NOT judgmentally equal to `0`. -/
protected def mod: ℕ → ℕ → ℕ :=
  ℕ.monusRec (fun a _ _ => a) fun _ _ _ c => c
  -- if 0 < b ∧ b ≤ a then (a ∸ b).mod b else a

instance: Mod ℕ where mod := ℕ.mod
@[simp] protected theorem mod.def (a b: ℕ): a.mod b = a % b := rfl

#check Nat.mod_eq
theorem mod_eq (a b: ℕ): a % b = if 0 < b ∧ b ≤ a then (a ∸ b) % b else a :=
  by rw [←ℕ.mod.def, ℕ.mod]; rfl

protected theorem mod.pos {a b: ℕ} (h: 0 < b ∧ b ≤ a): a % b = (a ∸ b) % b :=
  mod_eq a b ▸ if_pos h

protected theorem mod.neg {a b: ℕ} (h: ¬(0 < b ∧ b ≤ a)): a % b = a :=
  mod_eq a b ▸ if_neg h

#check Nat.zero_mod
@[simp] theorem zero_mod (n: ℕ): 0 % n = 0 :=
  ℕ.mod.neg fun ⟨left, right⟩ => ℕ.lt_irrefl 0 (trans left right)

#check Nat.mod_zero
@[simp] theorem mod_zero (n: ℕ): n % 0 = n :=
  ℕ.mod.neg fun ⟨h, _⟩ => ℕ.lt_irrefl 0 h

#check ite_true
#check if_pos
#check eq_true
#check Nat.mod_eq_sub_mod
theorem mod_eq_sub_mod {a b: ℕ} (h: a ≥ b): a % b = (a ∸ b) % b :=
  match b.eq_zero_or_pos with
  | .inl h' => h' ▸ rfl
  | .inr h' => ℕ.mod.pos ⟨h', h⟩

#check Nat.mod_eq_of_lt
@[simp] theorem mod_eq_of_lt {a b: ℕ} (h: a < b): a % b = a :=
  mod.neg fun ⟨_, h'⟩ => b.lt_irrefl (trans h' h)

#check Nat.mod_lt
theorem mod_lt (a: ℕ) {b: ℕ}: b > 0 → a % b < b :=
  -- flip (ℕ.monusRecOn (motive := fun a b => b > 0 → a % b < b) a b)
  --   (fun a b h ih hb => trans (mod_eq_sub_mod h.2) (ih hb))
  --   fun a b h hb => suffices b > a from trans (ℕ.mod.neg h) this; gt_of_not_le (h ⟨hb, .⟩)
by
  induction a, b using ℕ.monusRec with
  | ind a b h ih => exact fun hb => trans (mod_eq_sub_mod h.2) (ih hb)
  | base a b h => exact fun hb =>
      suffices b > a from trans (ℕ.mod.neg h) this; gt_of_not_le (h ⟨hb, .⟩)

#check Nat.gcd
protected def gcd (a: ℕ): ℕ → ℕ
  | 0 => a
  | b@(succ n) => b.gcd (a % b)
termination_by gcd a b => b
decreasing_by suffices 0 < b from ‹b = n.succ› ▸ (a.mod_lt this)
              exact ‹b = n.succ› ▸ n.succ_pos

#check Nat.gcd_succ
protected def gcd_succ (a b: ℕ): a.succ.gcd b = (b.succ % a).gcd a.succ :=
  sorry

#check Nat.gcd_zero_right
@[simp] theorem gcd_zero_right (n: ℕ): n.gcd 0 = n := rfl
@[simp] theorem gcd_zero_left: (n: ℕ) → ℕ.gcd 0 n = 0
  | 0 => rfl
  | succ n => sorry

/-! ## Binary arithmetics -/

protected def double (n: ℕ): ℕ := n + n

inductive isPow2: ℕ → Prop where
  | one: isPow2 1
  | double {n: ℕ}: isPow2 n → isPow2 n.double

#check Nat.one_isPowerOfTwo
theorem one_isPow2: isPow2 1 := .one

end ℕ
