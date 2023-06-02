set_option autoImplicit false

/-! # Linear Logic
- [nLab](https://ncatlab.org/nlab/show/linear+logic)
-/

/-- A.k.a., *proposition*.
`Var` is the initial set of *propositional variables*.
-/
inductive Term (Var: Type _)
  /-
    Nullary
  -/
  /-- Propositional variables are propositions. -/
  | var (x: Var)
  /-- Additive truth (`⊤`). -/
  | top
  /-- Additive falsity (`0`). -/
  | zero
  /-- Multiplicative truth (`1`). -/
  | one
  /-- Multiplicative falsity (`⊥`). -/
  | bottom
  /-
    Unary
  -/
  /-- Negation (`Aᗮ`). -/
  | neg (A: Term Var)
  /-- Exponential conjunction (`!A`). -/
  | ofCourse (A: Term Var)
  /-- Exponential disjunction (`?A`). -/
  | whyNot (A: Term Var)
  /-
    Binary
  -/
  /-- Additive conjunction (`A & B`). -/
  | with (A B: Term Var)
  /-- Additive disjunction (`A ⊕ B`). -/
  | plus (A B: Term Var)
  /-- Multiplicative conjunction (`A ⊗ B`). -/
  | times (A B: Term Var)
  /-- Mulitplicative disjunction (`A ⅋ B`). -/
  | par (A B: Term Var)

namespace Term
  variable {Var: Type _}

  instance: Coe Var (Term Var) where coe := .var
  @[inherit_doc] notation "⊤" => Term.top
  @[default_instance] instance: OfNat (Term Var) (nat_lit 0) where ofNat := .zero
  @[default_instance] instance: OfNat (Term Var) (nat_lit 1) where ofNat := .one
  @[inherit_doc] notation "⊥" => Term.bottom

  @[inherit_doc] postfix:arg "ᗮ" => Term.neg
  @[inherit_doc] prefix:49 (priority := high) "!" => Term.ofCourse
  @[inherit_doc] prefix:arg (priority := high) "?" => Term.whyNot
  -- @[inherit_doc] notation:max (priority := high) "!" b:45 => Term.ofCourse b
  -- @[inherit_doc] notation:max "?" b:40 => Term.whyNot b

  @[inherit_doc] infix:65 " ⊕ " => Term.plus
  @[inherit_doc] infix:70 " ⊗ " => Term.times
  @[inherit_doc] infix:55 " & " => Term.with
  @[inherit_doc] infix:51 " ⅋ " => Term.par



  variable (A B: Term Var)

  @[simp] protected theorem var.def (x: Var): x = var x := rfl
  @[simp] protected theorem top.def: ⊤ = @top Var := rfl
  @[simp] protected theorem zero.def: 0 = @zero Var := rfl
  @[simp] protected theorem one.def: 1 = @one Var := rfl
  @[simp] protected theorem bottom.def: ⊥ = @bottom Var := rfl

  @[simp] protected theorem neg.def: Aᗮ = A.neg := rfl
  -- @[simp] protected theorem ofCourse.def: !A = A.ofCourse := rfl
  @[simp] protected theorem whyNot.def: ?A = A.whyNot := rfl

  @[simp] protected theorem with.def: A & B = A.with B := rfl
  @[simp] protected theorem par.def: A & B = A.with B := rfl
end Term

abbrev Context (Var: Type _) := List (Term Var)

structure Sequent (Var: Type _) where
  /-- `[tail <- head] ⊢ [head -> tail]` -/
  mk ::
  antecedents: Context Var
  conclusions: Context Var

@[inherit_doc] infix:0 " ⊢ " => Sequent.mk
#check [] ⊢ []

/-
Sometimes one does not define the operation of negation, defining only `pᗮ` for
a propositional variable `p`. It is a theorem that every proposition above is
equivalent (in the sense defined below) to a proposition in which negation is
applied only to propositional variables.
-/

#check %[5,6,7 | .nil]
#check List.append
inductive List.perm {α}: List α → List α → Prop
  | nil: [].perm []
  | cons (a: α) {as bs cs: List α}:
    as.perm (bs ++ cs) → (a::as).perm (bs ++ a::cs)

inductive Valid {Var: Type _}: Sequent Var → Prop
  /-
    Structural rules
  -/
  | exchange {Γ Γ' Δ Δ': Context Var}
    : Valid (Γ ⊢ Δ) → Γ.perm Γ' → Δ.perm Δ' → Valid (Γ' ⊢ Δ')
  | weakening {Γ Δ Θ: Context Var}
    : Valid (Δ ++ Γ ⊢ Θ) → (A: Term Var) → Valid (Δ ++ A.ofCourse :: Γ ⊢ Θ)
  | weakening' {Γ Δ Θ: Context Var}
    : Valid (Θ ⊢ Γ ++ Δ) → (A: Term Var) → Valid (Θ ⊢ Γ ++ ?A :: Δ)
  | contraction {Γ Δ Θ: Context Var} {A: Term Var}
    : Valid (Δ ++ A.ofCourse :: A.ofCourse :: Γ ⊢ Θ)
    → Valid (Δ ++ A.ofCourse :: Γ ⊢ Θ)
  | contraction' {Γ Δ Θ: Context Var} {A: Term Var}
    : Valid (Θ ⊢ Γ ++ ?A :: ?A :: Δ) → Valid (Θ ⊢ Γ ++ ?A :: Δ)
  | identity (A: Term Var): Valid ([A] ⊢ [A])
  | cut {Φ Γ Δ Ψ: Context Var} {A: Term Var}
    : Valid (Γ ⊢ A :: Φ) → Valid (A :: Ψ ⊢ Δ) → Valid (Γ ++ Ψ ⊢ Δ ++ Φ)
  /-
    Logical rules
  -/
  | neg {Γ Δ: Context Var} {A: Term Var}
    : Valid (Γ ⊢ A :: Δ) → Valid (Aᗮ :: Γ ⊢ Δ)
  | neg' {Γ Δ: Context Var} {A: Term Var}
    : Valid (A :: Γ ⊢ Δ) → Valid (Γ ⊢ Aᗮ :: Δ)
  | with {Γ Γ' Δ: Context Var} {A B: Term Var}
    : Valid (Γ ++ A :: Γ' ⊢ Δ)
    → Valid (Γ ++ B :: Γ' ⊢ Δ)
    → Valid (Γ ++ (A & B) :: Γ' ⊢ Δ)
  | with' {Γ Δ Δ': Context Var} {A B: Term Var}
    : Valid (Γ ⊢ Δ ++ A :: Δ')
    → Valid (Γ ⊢ Δ ++ B :: Δ')
    → Valid (Γ ⊢ Δ ++ (A & B) :: Δ')
  | plus' {Γ Δ Δ': Context Var} {A B: Term Var}
    : Valid (Γ ⊢ Δ ++ A :: Δ')
    → Valid (Γ ⊢ Δ ++ B :: Δ')
    → Valid (Γ ⊢ Δ ++ (A ⊕ B) :: Δ')
  | plus {Γ Γ' Δ: Context Var} {A B: Term Var}
    : Valid (Γ ++ A :: Γ' ⊢ Δ)
    → Valid (Γ ++ B :: Γ' ⊢ Δ)
    → Valid (Γ ++ (A ⊕ B) :: Γ' ⊢ Δ)
  | times {Γ Γ' Δ: Context Var} {A B: Term Var}
    : Valid (Γ ++ A :: B :: Γ' ⊢ Δ)
    → Valid (Γ ++ (A ⊗ B) :: Γ' ⊢ Δ)
  | times' {Γ Γ' Δ Δ': Context Var} {A B: Term Var}
    : Valid (Γ ⊢ Δ ++ [A])
    → Valid (Γ' ⊢ [B] ++ Δ')
    → Valid (Γ' ++ Γ ⊢ Δ ++ (A ⊗ B) :: Δ')
  | par' {Γ Δ Δ': Context Var} {A B: Term Var}
    : Valid (Γ ⊢ Δ ++ A :: B :: Δ')
    → Valid (Γ ⊢ Δ ++ (A ⅋ B) :: Δ')
  | par {Γ Γ' Δ Δ': Context Var} {A B: Term Var}
    : Valid (A :: Γ ⊢ Δ)
    → Valid (Γ' ++ [B] ⊢ Δ')
    → Valid (Γ' ++ (A ⅋ B) :: Γ ⊢ Δ ++ Δ')
  | top {Γ Δ Δ': Context Var}
    : Valid (Γ ⊢ Δ ++ ⊤ :: Δ')
  | zero {Γ Γ' Δ: Context Var}
    : Valid (Γ ++ 0 :: Γ' ⊢ Δ)
  | one {Γ Γ' Δ: Context Var}
    : Valid (Γ ++ Γ' ⊢ Δ) → Valid (Γ ++ 1 :: Γ' ⊢ Δ)
  | one'
    : Valid ([] ⊢ [1])
  | bot' {Γ Δ Δ': Context Var}
    : Valid (Γ ⊢ Δ ++ Δ') → Valid (Γ ⊢ Δ ++ ⊥ :: Δ')
  | bot
    : Valid ([⊥] ⊢ [])
  | ofCourse {Γ Γ' Δ: Context Var} {A: Term Var}
    : Valid (Γ ++ A :: Γ' ⊢ Δ) → Valid (Γ ++ A.ofCourse :: Γ' ⊢ Δ)
  | whyNot {Γ Δ Δ': Context Var} {A: Term Var}
    : Valid (Γ ⊢ Δ ++ A :: Δ') → Valid (Γ ⊢ Δ ++ ?A :: Δ')

variable {Var: Type _} (A B C: Term Var)

abbrev Term.equiv := Valid ([A] ⊢ [B]) ∧ Valid ([B] ⊢ [A])
@[inherit_doc] infix:50 "≡" => Term.equiv

example: A⊗(B ⊕ C) ≡ (A⊗B) ⊕ (A⊗C) :=
  ⟨sorry, sorry⟩