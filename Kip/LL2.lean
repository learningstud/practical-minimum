set_option autoImplicit false

/-! # Linear Logic
- [nLab](https://ncatlab.org/nlab/show/linear+logic)
- [SEP](https://plato.stanford.edu/entries/logic-linear/)
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
  @[inherit_doc] prefix:arg (priority := high) "!" => Term.ofCourse
  @[inherit_doc] prefix:arg (priority := high) "?" => Term.whyNot
  -- @[inherit_doc] notation:max (priority := high) "!" b:45 => Term.ofCourse b

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
  @[simp] protected theorem ofCourse.def: (!A) = A.ofCourse := rfl
  @[simp] protected theorem whyNot.def: ?A = A.whyNot := rfl

  @[simp] protected theorem with.def: A & B = A.with B := rfl
  @[simp] protected theorem par.def: A & B = A.with B := rfl
end Term

abbrev Context (Var: Type _) := List (Term Var)

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

/-- `[tail <- head] ⊢ [head -> tail]` -/
inductive S1 {Var: Type _}: Context Var → Context Var → Prop
  /-
    Structural rules
  -/
  | exchange {Γ Γ' Δ Δ': Context Var}
    : S1 Γ Δ → Γ.perm Γ' → Δ.perm Δ' → S1 Γ' Δ'
  | weakening {Γ Γ' Δ: Context Var}
    : S1 (Γ ++ Γ') Δ → (A: Term Var) → S1 (Γ ++ (!A) :: Γ') Δ
  | weakening' {Γ Δ Δ': Context Var}
    : S1 Γ (Δ ++ Δ') → (A: Term Var) → S1 Γ (Δ ++ ?A :: Δ')
  | contraction {Γ Γ' Δ: Context Var} {A: Term Var}
    : S1 (Γ ++ (!A) :: (!A) :: Γ') Δ → S1 (Γ ++ (!A) :: Γ) Δ
  | contraction' {Γ Δ Δ': Context Var} {A: Term Var}
    : S1 Γ (Δ ++ ?A :: ?A :: Δ') → S1 Γ (Δ ++ ?A :: Δ')
  | identity
    : (A: Term Var) → S1 [A] [A]
  | cut {Γ Γ' Δ Δ': Context Var} {A: Term Var}
    : S1 Γ (A :: Δ') → S1 (A :: Γ') Δ → S1 (Γ ++ Γ') (Δ ++ Δ')
  /-
    Logical rules
  -/
  | neg {Γ Δ: Context Var} {A: Term Var}
    : S1 Γ (A :: Δ) → S1 (Aᗮ :: Γ) Δ
  | neg' {Γ Δ: Context Var} {A: Term Var}
    : S1 (A :: Γ) Δ → S1 Γ (Aᗮ :: Δ)
  | with {Γ Γ' Δ: Context Var} {A B: Term Var}
    : S1 (Γ ++ A :: Γ') Δ → S1 (Γ ++ B :: Γ') Δ → S1 (Γ ++ (A & B) :: Γ') Δ
  | with' {Γ Δ Δ': Context Var} {A B: Term Var}
    : S1 Γ (Δ ++ A :: Δ') → S1 Γ (Δ ++ B :: Δ') → S1 Γ (Δ ++ (A & B) :: Δ')
  | plus' {Γ Δ Δ': Context Var} {A B: Term Var}
    : S1 Γ (Δ ++ A :: Δ') → S1 Γ (Δ ++ B :: Δ') → S1 Γ (Δ ++ (A ⊕ B) :: Δ')
  | plus {Γ Γ' Δ: Context Var} {A B: Term Var}
    : S1 (Γ ++ A :: Γ') Δ → S1 (Γ ++ B :: Γ') Δ → S1 (Γ ++ (A ⊕ B) :: Γ') Δ
  | times {Γ Γ' Δ: Context Var} {A B: Term Var}
    : S1 (Γ ++ A :: B :: Γ') Δ → S1 (Γ ++ (A ⊗ B) :: Γ') Δ
  | times' {Γ Γ' Δ Δ': Context Var} {A B: Term Var}
    : S1 Γ (Δ ++ [A]) → S1 Γ' (B :: Δ') → S1 (Γ' ++ Γ) (Δ ++ (A ⊗ B) :: Δ')
  | par' {Γ Δ Δ': Context Var} {A B: Term Var}
    : S1 Γ (Δ ++ A :: B :: Δ') → S1 Γ (Δ ++ (A ⅋ B) :: Δ')
  | par {Γ Γ' Δ Δ': Context Var} {A B: Term Var}
    : S1 (A :: Γ) Δ → S1 (Γ' ++ [B]) Δ' → S1 (Γ' ++ (A ⅋ B) :: Γ) (Δ ++ Δ')
  | top {Γ Δ Δ': Context Var}
    : S1 Γ (Δ ++ ⊤ :: Δ')
  | zero {Γ Γ' Δ: Context Var}
    : S1 (Γ ++ 0 :: Γ') Δ
  | one {Γ Γ' Δ: Context Var}
    : S1 (Γ ++ Γ') Δ → S1 (Γ ++ 1 :: Γ') Δ
  | one'
    : S1 [] [1]
  | bot' {Γ Δ Δ': Context Var}
    : S1 Γ (Δ ++ Δ') → S1 Γ (Δ ++ ⊥ :: Δ')
  | bot
    : S1 [⊥] []
  | ofCourse {Γ Γ' Δ: Context Var} {A: Term Var}
    : S1 (Γ ++ A :: Γ') Δ → S1 (Γ ++ A.ofCourse :: Γ') Δ
  | whyNot {Γ Δ Δ': Context Var} {A: Term Var}
    : S1 Γ (Δ ++ A :: Δ') → S1 Γ (Δ ++ ?A :: Δ')

inductive S2 {Var: Type _}: Context Var → Prop
  /-
    Structural rules
  -/
  | exchange {Γ Δ: Context Var}
    : S2 Γ → Γ.perm Δ → S2 Δ
  | weakening {Γ Δ: Context Var}
    : S2 (Γ ++ Δ) → (A: Term Var) → S2 (Γ ++ ?A :: Δ)
  | contraction {Γ Δ: Context Var} {A: Term Var}
    : S2 (Γ ++ ?A :: ?A :: Δ) → S2 (Γ ++ ?A :: Δ)
  | identity
    : (A: Term Var) → S2 [A, Aᗮ]
  | cut {Γ Δ: Context Var} {A: Term Var}
    : S2 (A :: Γ) → S2 (Aᗮ :: Δ) → S2 (Γ ++ Δ)
  /-
    Logical rules
  -/
  | with {Γ Δ: Context Var} {A B: Term Var}
    : S2 (Γ ++ A :: Δ) → S2 (Γ ++ B :: Δ) → S2 (Γ ++ (A & B) :: Δ)
  | plusl {Γ Δ: Context Var} {A B: Term Var}
    : S2 (Γ ++ A :: Δ) → S2 (Γ ++ (A ⊕ B) :: Δ)
  | plusr {Γ Δ: Context Var} {A B: Term Var}
    : S2 (Γ ++ B :: Δ) → S2 (Γ ++ (A ⊕ B) :: Δ)
  | times {Γ Δ: Context Var} {A B: Term Var}
    : S2 (Γ ++ A :: B :: Δ) → S2 (Γ ++ (A ⊗ B) :: Δ)
  | par' {Γ Δ Δ': Context Var} {A B: Term Var}
    : S2 Γ (Δ ++ A :: B :: Δ') → S2 Γ (Δ ++ (A ⅋ B) :: Δ')
  | par {Γ Γ' Δ Δ': Context Var} {A B: Term Var}
    : S2 (A :: Γ) Δ → S2 (Γ' ++ [B]) Δ' → S2 (Γ' ++ (A ⅋ B) :: Γ) (Δ ++ Δ')
  | top {Γ Δ: Context Var}
    : S2 (Γ ++ ⊤ :: Δ)
  | zero {Γ Δ: Context Var}
    : S2 (Γ ++ 0 :: Γ') Δ
  | one {Γ Γ' Δ: Context Var}
    : S2 (Γ ++ Γ') Δ → S2 (Γ ++ 1 :: Γ') Δ
  | one'
    : S2 [] [1]
  | bot' {Γ Δ Δ': Context Var}
    : S2 Γ (Δ ++ Δ') → S2 Γ (Δ ++ ⊥ :: Δ')
  | bot
    : S2 [⊥] []
  | ofCourse {Γ Γ' Δ: Context Var} {A: Term Var}
    : S2 (Γ ++ A :: Γ') Δ → S2 (Γ ++ A.ofCourse :: Γ') Δ
  | whyNot {Γ Δ Δ': Context Var} {A: Term Var}
    : S2 Γ (Δ ++ A :: Δ') → S2 Γ (Δ ++ ?A :: Δ')

/-
variable {Var: Type _} (A B C: Term Var)

abbrev Sequent (Γ Δ: Context Var) := S1 Γ Δ 
@[inherit_doc] infix:0 " ⊢ " => Sequent
abbrev Term.equiv := S1 [A] [B] ∧ S1 [B] [A]
@[inherit_doc] infix:50 "≡" => Term.equiv

example: A⊗(B ⊕ C) ≡ (A⊗B) ⊕ (A⊗C) :=
  ⟨sorry, sorry⟩
-/