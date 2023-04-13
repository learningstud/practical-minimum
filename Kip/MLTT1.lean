/-
```lean4
structure T where
  mk ::
  a: α
  [b: β]
  {c: γ}

-- is the same as:

inductive T
  | mk (a: α) [b: β] {c: γ}
def T.a (t: T): α := let { a, .. } := t ; a
def T.b (t: T): β := let { b, .. } := t ; b
def T.c (t: T): γ := let { c, .. } := t ; c
```

- Ordering of assumptions in a context
  - linearly ordered: for display
  - partially ordered (DAG): the weakest condition as commonly defined
  - arbitrarily ordered: mutually recursive
- uniqueness of assumptions in a context
  - already unique by "reference" in implementations
  - uniqueness of name is a IO/UI concern: rename on the fly or prompt users about duplicated names
-/

set_option autoImplicit false

namespace MLTT

inductive Term (Var: Type _) [BEq Var]
  | var (x: Var)
  | lam (binder: Var) (predicate: Term Var)
  | pi (binder: Var) (domain predicate: Term Var)
  | app (function argument: Term Var)
  | subst (term: Term Var) (var: Var) (replacement: Term Var)

variable (Var: Type _) [BEq Var]

instance: Coe Var (Term Var) where
  coe x := .var x

#check List.isPrefixOf
#check List.lookup
def List.beforeKey {α β} [BEq α] (xs: List (α × β)) (a: α): List (α × β) :=
  xs.takeWhile (Prod.fst . != a)

abbrev Context := List (Var × Term Var)

/-- Γ ⊢ A : 𝒰 -/
inductive JType: Context Var → Term Var → Type _
  | pi {Γ: Context Var} {x: Var} {A B: Term Var}
    : JType ((x, A) :: Γ) B → JType Γ (.pi x A B)

/-- Γ ⊢ A ≡ B : 𝒰 -/
inductive JTypeEq (Γ: Context Var) (A: Term Var): Term Var → Type _
  | refl: JType Var Γ A → JTypeEq Γ A A

/-- Γ ⊢ -/
inductive JCtx: Context Var → Type _
  | nil: JCtx .nil
  | cons {Γ: Context Var} {x: Var} {A: Term Var}
    : JType Var Γ A → (Γ.lookup x).isNone → JCtx ((x, A) :: Γ)

section
  variable {Var} [BEq Var]

  theorem JCtx.cons_type_ok {Γ: Context Var} {x: Var} {A: Term Var}
    : JCtx Var ((x, A) :: Γ) → JType Var Γ A
    | .cons j _ => j

  theorem JType.ctx_ok {Γ: Context Var} {A: Term Var}
    : JType Var Γ A → JCtx Var Γ
    | .pi j => have .cons j _ := j.ctx_ok; j.ctx_ok
    -- | j@(.pi _) => j.pi_type_ok.ctx_ok
  theorem JType.pi_type_ok {Γ: Context Var} {x: Var} {A B: Term Var}
    : JType Var Γ (.pi x A B) → JType Var Γ A
    | .pi j => j.ctx_ok.cons_type_ok -- have .cons j _ := j.ctx_ok; j

  theorem JTypeEq.ctx_ok {Γ: Context Var} {A B: Term Var}
    : JTypeEq Var Γ A B → JCtx Var Γ
    | .refl j => j.ctx_ok
  theorem JTypeEq.left_ok {Γ: Context Var} {A B: Term Var}
    : JTypeEq Var Γ A B → JType Var Γ A
    | .refl j => j
  theorem JTypeEq.right_ok {Γ: Context Var} {A B: Term Var}
    : JTypeEq Var Γ A B → JType Var Γ B
    | .refl j => j
end

mutual
/-- Γ ⊢ a : A -/
inductive JTerm: Context Var → Term Var → Term Var → Type _
  | var {Γ: Context Var} {x: Var} {A: Term Var}
    : JCtx Var Γ → (x, A) ∈ Γ → JTerm Γ x A
  | lam {Γ: Context Var} {x: Var} {b A B: Term Var}
    : JTerm ((x, A) :: Γ) b B → JTerm Γ (.lam x b) (.pi x A B)
  | app {Γ: Context Var} {x: Var} {f a A B: Term Var}
    : JTerm Γ f (.pi x A B) → JTerm Γ a A → JTerm Γ (.app f a) (.subst B x a)
  | congr {Γ: Context Var} {a b A: Term Var}
    : JTerm Γ a A → JTermEq Γ a b A → JTerm Γ b A

/-- Γ ⊢ a ≡ b : A -/
inductive JTermEq: Context Var → Term Var → Term Var → Term Var → Type _
  | refl {Γ: Context Var} {a A: Term Var}
    : JTerm Γ a A → JTermEq Γ a a A
  | symm {Γ: Context Var} {a b A: Term Var}
    : JTermEq Γ a b A → JTermEq Γ b a A
  | trans {Γ: Context Var} {a b c A: Term Var}
    : JTermEq Γ a b A → JTermEq Γ b c A → JTermEq Γ a c A
  | α {Γ: Context Var} {x: Var} {b b' A B: Term Var}
    : JTerm ((x, A) :: Γ) b B
    → JTermEq ((x, A) :: Γ) b b' B
    → JTermEq Γ (.lam x b) (.lam x b') (.pi x A B)
  | β {Γ: Context Var} {x: Var} {a b A B: Term Var}
    : JTerm ((x, A) :: Γ) b B
    → JTerm Γ a A
    → JTermEq Γ (.app (.lam x b) a) (.subst b x a) (.subst B x a)
  | η {Γ: Context Var} {x: Var} {f A B: Term Var}
    : JTerm Γ f (.pi x A B) → JTermEq Γ f (.lam x (.app f x)) (.pi x A B)
end

namespace JTerm
  variable {Var} [BEq Var]

  theorem ctx_ok {Γ: Context Var} {a A: Term Var}
    : JTerm Var Γ a A → JCtx Var Γ
    | .var j _ => j
    | .lam j => have .cons j _ := j.ctx_ok; j.ctx_ok
    | .app _ j
    | .congr j _ => j.ctx_ok
  theorem type_ok {Γ: Context Var} {a A: Term Var}
    : JTerm Var Γ a A → JType Var Γ A
    | .var j h => sorry -- weakening is admissible
    | .lam j => j.type_ok.pi
    | .app jfun jarg => sorry -- substitution is admissible
    | .congr j _ => j.type_ok
  
  -- theorem JTerm.var_type_ok {Γ: Context Var} {x: Var} {A: Term Var}
  --   : JTerm Var Γ x A → JType Var (List.beforeKey Γ x) A
  --   := sorry
end JTerm

namespace JTermEq
  variable {Var} [BEq Var]

  theorem ctx_ok {Γ: Context Var} {a b A: Term Var}
    : JTermEq Var Γ a b A → JCtx Var Γ
    | .refl j
    | .symm j
    | .trans j _
    | .β _ j
    | .η j => j.ctx_ok
    | .α j _ => have .cons j _ := j.ctx_ok; j.ctx_ok
  theorem type_ok {Γ: Context Var} {a b A: Term Var}
    : JTermEq Var Γ a b A → JType Var Γ A
    | .refl j
    | .symm j
    | .trans j _
    | .η j => j.type_ok
    | .α j _ => j.type_ok.pi
    | .β j j' => (j.lam.app j').type_ok
  theorem α_type_ok {Γ: Context Var} {x: Var} {b b' A B: Term Var}
    : JTermEq Var Γ (.lam x b) (.lam x b') (.pi x A B) → JType Var Γ A
    | j => j.type_ok.pi_type_ok
  mutual
    theorem left_ok {Γ: Context Var} {a b A: Term Var}
      : JTermEq Var Γ a b A → JTerm Var Γ a A
      | .refl j => j
      | .symm j => j.right_ok
      | .trans j _ => j.left_ok
      | .α j _ => j.lam
      | .β j j' => j.lam.app j'
      | .η j => j
    theorem right_ok {Γ: Context Var} {a b A: Term Var}
      : JTermEq Var Γ a b A → JTerm Var Γ b A
      | .refl j => j
      | .symm j => j.left_ok
      | .trans _ j => j.right_ok
      | .α _ j => j.right_ok.lam
      | je@(.β j j') => (j.lam.app j').congr je
      | je@(.η j) => j.congr je
  end
end JTermEq

variable {Var} [BEq Var] {Γ: Context Var}

namespace JCtx
  def context (_: JCtx Var Γ) := Γ
end JCtx

namespace JType
  variable {A B: Term Var}
  def context (_: JType Var Γ A) := Γ
  def type    (_: JType Var Γ A) := A

  theorem congr: JType Var Γ A → JTypeEq Var Γ A B → JType Var Γ B
    | j, .refl _ => j  
end JType

namespace JTerm
  variable {a b A B: Term Var}
  def context (_: JTerm Var Γ a A) := Γ
  def term    (_: JTerm Var Γ a A) := a
  def type    (_: JTerm Var Γ a A) := A

  -- theorem congr {Γ: Context Var} {a b A: Term Var} (j: JTerm Var Γ a A)
  --   : JTermEq Var Γ a b A → JTerm Var Γ b A
  --   | .refl .. => j
  --   | .symm j' => sorry
  --   | .trans j₁ j₂ => (j.congr j₁).congr j₂
  --   | .α _ j₂ j₃ => .lam (j₂.congr j₃)
  --   | .β j₁ j₂ => sorry -- substitution is admissible
  --   | .η j' => .lam sorry -- substitution is idempotent
  theorem congrType: JTerm Var Γ a A → JTypeEq Var Γ A B → JTerm Var Γ a B
    | j, .refl _ => j
end JTerm

namespace JTypeEq
  variable {Γ: Context Var} {A B C: Term Var}
  def context (_: JTypeEq Var Γ A B) := Γ
  def left    (_: JTypeEq Var Γ A B) := A
  def right   (_: JTypeEq Var Γ A B) := B

  theorem symm: JTypeEq Var Γ A B → JTypeEq Var Γ B A
    | j@(.refl _) => j
  theorem trans: JTypeEq Var Γ A B → JTypeEq Var Γ B C → JTypeEq Var Γ A C
    | j@(.refl _), .refl _ => j
end JTypeEq

namespace JTermEq
  variable {Γ: Context Var} {a b A B: Term Var}
  def context (_: JTermEq Var Γ a b A) := Γ
  def left    (_: JTermEq Var Γ a b A) := a
  def right   (_: JTermEq Var Γ a b A) := b
  def type    (_: JTermEq Var Γ a b A) := A

  theorem congrType: JTermEq Var Γ a b A → JTypeEq Var Γ A B → JTermEq Var Γ a b B
    | j, .refl _ => j
end JTermEq

theorem JType.wkg_cons {Γ: Context Var} {x: Var} {T A: Term Var}
    (jctx: JCtx Var ((x, T)::Γ))
  : JType Var Γ A → JType Var ((x, T)::Γ) A
  | jtype@(.pi j) => sorry

theorem JType.wkg {Γ Δ: Context Var} {A: Term Var}
    (jctx: JCtx Var (Δ ++ Γ))
  : JType Var Γ A → JType Var (Δ ++ Γ) A
  | j => by
    induction Δ with
    | nil => exact j
    | cons δ Δ ih => have .cons j _ := jctx; exact (ih j.ctx_ok).wkg_cons jctx

theorem JTypeEq.wkg {Γ Δ: Context Var} {A B: Term Var}
    (jctx: JCtx Var (Δ ++ Γ))
  : JTypeEq Var Γ A B → JTypeEq Var (Δ ++ Γ) A B
  | .refl j => .refl (j.wkg jctx)

mutual
  theorem JTerm.wkg {Γ Δ: Context Var} {a A: Term Var}
      (jctx: JCtx Var (Δ ++ Γ))
    : JTerm Var Γ a A → JTerm Var (Δ ++ Γ) a A
    | .var _ h => .var jctx (List.mem_append_of_mem_right Δ h)
    | .lam j => sorry --have := j.wkg jctx; _
    | .app j j' => .app (j.wkg jctx) (j'.wkg jctx)
    | .congr j je => .congr (j.wkg jctx) (je.wkg jctx)

  theorem JTermEq.wkg {Γ Δ: Context Var} {a b A: Term Var}
      (jctx: JCtx Var (Δ ++ Γ))
    : JTermEq Var Γ a b A → JTermEq Var (Δ ++ Γ) a b A
    | .refl j => .refl (j.wkg jctx)
    | .symm j => .symm (j.wkg jctx)
    | .trans j j' => .trans (j.wkg jctx) (j'.wkg jctx)
    | .α j j' => sorry -- substitution
    | .β j j' => sorry -- substitution
    | .η j => .η (j.wkg jctx)
end

/-
We define ∆ ⊢ σ : Γ by induction on Γ. We have ∆ ⊢ () : () (empty substitution)
and ∆ ⊢ (σ, x/u) : Γ, x : A if ∆ ⊢ σ : Γ and ∆ ⊢ u : Aσ.
-/

-- def Term.σ.aux (Δ: Context Var): (Γ: Context Var) → Type _
--   | [] => Unit
--   | (_, A)::Γ => JTerm Var Δ u (σ A)

-- def Term.σ.{u} {Var: Type (u+1)} [BEq Var] (Δ: Context Var):
--   (Γ: Context Var) → {u: Var} → Type _
--   | [] => sorry --@id (Term Var)
--   | (x, A)::Γ, u => fun (_: JTerm Var Δ u (σ Δ Γ A)) => _

/-- ∆ ⊢ σ : Γ -/
inductive Subst (Δ: Context Var): Context Var → Type _
  | nil: Subst Δ .nil
  | cons {Γ: Context Var} {x A: Term Var}
    (σ: Subst Δ Γ) (x: Var): Subst Δ ((x, A) :: Γ)

-- def Subst.apply {Δ Γ: Context Var} (σ: Subst Δ Γ)

end MLTT


/-!
namespace DeBruijn

inductive Var
  | free (i: Nat)
  | bnd (i: Nat)

inductive Term
  | var (x: Var)
  | lam (predicate: Term)
  | pi (binder: String) (domain predicate: Term)
  | app (function argument: Term)
  | subst (term: Term) (var: Var) (replacement: Term)

instance: Coe Var Term where
  coe x := .var x

abbrev Context := List (String × Term)

inductive JType: Context → Term → Type
  | pi {Γ: Context} {x: String} {A B: Term}
    : JType Γ A → JType ((x, A) :: Γ) B → JType Γ (.pi x A B)

inductive JTypeEq: Context → Term → Term → Type
  | refl {Γ: Context} {A: Term}
    : JType Γ A → JTypeEq Γ A A
  | symm {Γ: Context} {A B: Term}
    : JTypeEq Γ A B → JTypeEq Γ B A
  | trans {Γ: Context} {A B C: Term}
    : JTypeEq Γ A B → JTypeEq Γ B C → JTypeEq Γ A C

inductive JCtx: Context → Type
  | nil
    : JCtx .nil
  | cons {Γ: Context} {x: String} {A: Term}
    : JType Γ A → JCtx ((x, A) :: Γ)

#check List.instGetElemListNatLtInstLTNatLength
inductive JTerm: Context → Term → Term → Type
  | var {Γ: Context} {i: Fin Γ.length}
    : JCtx Γ → JTerm Γ (Var.free i) Γ[i].2
  | lam {Γ: Context} {x: String} {b A B: Term}
    : JTerm ((x, A) :: Γ) b B
    → JTerm Γ (.lam x b) (.pi x A B) -- Γ ⊢ λ x, b : Π (x: A), B
  | app {Γ: Context} {x: String} {f a A B: Term}
    : JTerm Γ f (.pi x A B) -- Γ ⊢ f : Π (x: A), B
    → JTerm Γ a A -- Γ ⊢ a : A
    → JTerm Γ (.app f a) (.subst B x a) -- Γ ⊢ f a : B (x := a)
  | congr {Γ: Context} {a A B: Term}
    : JTerm Γ a A -- Γ ⊢ a : A
    → JTypeEq Γ A B -- Γ ⊢ A ≡ B : 𝒰
    → JTerm Γ a B -- Γ ⊢ a : B

end DeBruijn
-/

theorem List.Mem.append_or {α} {a: α}
  : {xs ys: List α} → (xs ++ ys).Mem a → a ∈ xs ∨ a ∈ ys
  | [], _, h => .inr h
  | _::_, _, .head _ => .inl (.head _)
  | _::_, _, .tail x h => h.append_or.elim (.inl ∘ .tail x) .inr

namespace MLTT2

inductive Term (Var: Type _) [BEq Var] [LawfulBEq Var]
  | var (x: Var)
  | lam (binder: Var) (predicate: Term Var)
  | pi (binder: Var) (domain predicate: Term Var)
  | app (function argument: Term Var)

variable (Var: Type _) [DecidableEq Var]

instance: Coe Var (Term Var) where coe := .var

/-- Context of unique free variables. -/
abbrev Ctx := List (Var × Term Var)

/-- Judgment (`⊢ 𝒥`). -/
inductive Jud
  /-- Well-formed context (`ctx`).  -/
  | ctx
  /-- Well-formed type (`A type`). -/
  | typ (A: Term Var)
  /-- Well-typed value (`a : A`). -/
  | val (a A: Term Var)
  /-- Type equality (`A ≡ B type`). -/
  | teq (A B: Term Var)
  /-- Value equality (`a ≡ b : A`). -/
  | eq (a b A: Term Var)

-- instance: Coe (Term Var) (Jud Var) where coe := .typ

variable {Var: Type _} [DecidableEq Var]

/-- `A[t / x]`, i.e., `A[x := t]` -/
def Term.subst (A t: Term Var) (x: Var): Term Var :=
  match A with
  | term@(var y) => if x = y then t else term
  | term@(lam binder predicate) =>
    if x = binder then term else lam binder (predicate.subst t x)
  | (pi binder domain predicate) =>
    if x = binder
    then pi binder (domain.subst t x) predicate
    else pi binder (domain.subst t x) (predicate.subst t x)
  | app function argument => app (function.subst t x) (argument.subst t x)

/-- Sequent (`Γ ⊢ 𝒥`). -/
inductive Seq: Ctx Var → Jud Var → Type _
  | ctx.emp
    : Seq [] .ctx
  | ctx.ext {Γ: Ctx Var} {x: Var} {A: Term Var}
    : Seq Γ (.typ A) → (Γ.lookup x).isNone → Seq ((x, A)::Γ) .ctx
  | typ.pi {Γ: Ctx Var} {x: Var} {A B: Term Var}
    : Seq ((x, A)::Γ) (.typ B) → Seq Γ (.typ (.pi x A B))
  | val.var {Γ: Ctx Var} {x: Var} {A: Term Var}
    : Seq Γ .ctx → (x, A) ∈ Γ → Seq Γ (.val x A)
  | val.lam {Γ: Ctx Var} {x: Var} {b A B: Term Var}
    : Seq ((x, A)::Γ) (.val b B) → Seq Γ (.val (.lam x b) (.pi x A B))
  | val.app {Γ: Ctx Var} {x: Var} {f a A B: Term Var}
    : Seq Γ (.val f (.pi x A B))
    → Seq Γ (.val a A)
    → Seq Γ (.val (.app f a) (B.subst a x))
  | val.congr {Γ: Ctx Var} {a b A: Term Var}
    : Seq Γ (.val a A) → Seq Γ (.eq a b A) → Seq Γ (.val b A)
  | teq.refl {Γ: Ctx Var} {A: Term Var}
    : Seq Γ (.typ A) → Seq Γ (.teq A A)
  | eq.refl {Γ: Ctx Var} {a A: Term Var}
    : Seq Γ (.val a A) → Seq Γ (.eq a a A)
  | eq.symm {Γ: Ctx Var} {a b A: Term Var}
    : Seq Γ (.eq a b A) → Seq Γ (.eq b a A)
  | eq.trans {Γ: Ctx Var} {a b c A: Term Var}
    : Seq Γ (.eq a b A) → Seq Γ (.eq b c A) → Seq Γ (.eq a c A)
  | eq.lam_uniq {Γ: Ctx Var} {x: Var} {b b' A B: Term Var}
    : Seq ((x, A)::Γ) (.val b B)
    → Seq ((x, A)::Γ) (.eq b b' B)
    → Seq Γ (.eq (.lam x b) (.lam x b') (.pi x A B))
  | eq.β {Γ: Ctx Var} {x: Var} {a b A B: Term Var}
    : Seq ((x, A)::Γ) (.val b B)
    → Seq Γ (.val a A)
    → Seq Γ (.eq (.app (.lam x b) a) (.subst b a x) (.subst B a x))
  | eq.η {Γ: Ctx Var} {x: Var} {f A B: Term Var}
    : Seq Γ (.val f (.pi x A B)) → Seq Γ (.eq f (.lam x (.app f x)) (.pi x A B))

namespace Seq

mutual
  protected def typ.ctx_ok {Γ: Ctx Var} {A: Term Var}
    : Seq Γ (.typ A) → Seq Γ .ctx
    | typ.pi j => have := Seq.typ.ctx_ok j; Seq.ctx.ext.ctx_ok this
  protected def ctx.ext.ctx_ok {Γ: Ctx Var} {x: Var} {A: Term Var}
    : Seq ((x, A)::Γ) .ctx → Seq Γ .ctx
    | ctx.ext j _ => Seq.typ.ctx_ok j
end

def ctx_ok {Γ: Ctx Var} {j: Jud Var}
  : Seq Γ j → Seq Γ .ctx
  | j@ctx.emp
  | j@(ctx.ext ..)
  | val.var j _ => j
  | val.app _ j
  | val.congr j _
  | teq.refl j
  | eq.refl j
  | eq.symm j
  | eq.trans j _
  | eq.β _ j
  | eq.η j => j.ctx_ok
  | typ.pi j
  | val.lam j
  | eq.lam_uniq j _ => ctx.ext.ctx_ok j.ctx_ok

namespace teq
  -- @[match_pattern] abbrev rfl {Γ : Ctx Var} {A : Term Var} {j: Seq Γ (Jud.typ A)}
  --   := teq.refl j
  def left_ok {Γ: Ctx Var} {A B: Term Var}
    : Seq Γ (.teq A B) → Seq Γ (.typ A)
    | refl j => j
  def right_ok {Γ: Ctx Var} {A B: Term Var}
    : Seq Γ (.teq A B) → Seq Γ (.typ B)
    | refl j => j
  def symm {Γ: Ctx Var} {A B: Term Var}
    : Seq Γ (.teq A B) → Seq Γ (.teq B A)
    | j@(refl _) => j
  def trans {Γ: Ctx Var} {A B C: Term Var}
    : Seq Γ (.teq A B) → Seq Γ (.teq B C) → Seq Γ (.teq A C)
    | j, refl _ => j
  def congr {Γ: Ctx Var} {A B: Term Var}
    : Seq Γ (.typ A) → Seq Γ (.teq A B) → Seq Γ (.typ B)
    | j, refl _ => j
end teq

namespace eq
  mutual
    theorem left_ok {Γ: Ctx Var} {a b A: Term Var}
      : Seq Γ (.eq a b A) → Seq Γ (.val a A)
      | refl j => j
      | symm j => right_ok j
      | trans j _ => left_ok j
      | lam_uniq j _ => val.lam j
      | β j j' => val.app (val.lam j) j'
      | η j => j
    theorem right_ok {Γ: Ctx Var} {a b A: Term Var}
      : Seq Γ (.eq a b A) → Seq Γ (.val b A)
      | refl j => j
      | symm j => left_ok j
      | trans _ j => right_ok j
      | lam_uniq _ j => val.lam (right_ok j)
      | je@(β j j') => val.congr (val.app (val.lam j) j') je
      | je@(η j) => val.congr j je
  end
  def congr_typ {Γ: Ctx Var} {a b A B: Term Var}
    : Seq Γ (.eq a b A) → Seq Γ (.teq A B) → Seq Γ (.eq a b B)
    | j, teq.refl _ => j
end eq

section
  def ctx.ext.typ_ok {Γ: Ctx Var} {x: Var} {A: Term Var}
    : Seq ((x, A) :: Γ) .ctx → Seq Γ (.typ A)
    | ctx.ext j _ => j
  def typ.pi.typ_ok {Γ: Ctx Var} {x: Var} {A B: Term Var}
    : Seq Γ (.typ (.pi x A B)) → Seq Γ (.typ A)
    | typ.pi j => ctx.ext.typ_ok j.ctx_ok
  def val.congr_typ {Γ: Ctx Var} {a A B: Term Var}
    : Seq Γ (.val a A) → Seq Γ (.teq A B) → Seq Γ (.val a B)
    | j, teq.refl _ => j
end

theorem ctx.uniq_vars {Γ Δ: Ctx Var} {x: Var} {A: Term Var}
  : Seq (Γ ++ (x, A) :: Δ) .ctx → (Γ.lookup x).isNone ∧ (Δ.lookup x).isNone
:= sorry

theorem ctx.uniq_vars' {Γ Δ Θ: Ctx Var} {x y: Var} {A B: Term Var}
  : Seq (Γ ++ (x, A) :: Δ ++ (y, B) :: Θ) .ctx → x ≠ y
:= sorry

#check List.nil_append

/-- `(Γ, x: A ⊢ P type) → (Γ ⊢ a : A) → (Γ ⊢ P[a / x] type)` -/
theorem subst {Γ: Ctx Var} {x: Var} {a A P: Term Var}
  : Seq ((x, A)::Γ) (.typ P) → Seq Γ (.val a A) → Seq Γ (.typ (P.subst a x))
  | @typ.pi _ _ _ y B C j, j' => by
    have: y ≠ x := ctx.uniq_vars' (Γ := []) (Δ := []) j.ctx_ok
    -- have := beq_false_of_ne this
    unfold Term.subst
    simp [this.symm]
    apply typ.pi
    sorry
    
    -- induction Γ generalizing x y A B with
    -- | nil => 
    -- | cons δ Δ ih => sorry
    
    -- exact @subst ((y, Term.subst B a x)::Γ) x a A C sorry _
    -- exact subst (A := A) _ sorry

end Seq

namespace Term
  def isFreeVar (x: Var): Term Var → Prop
    | var y => x = y
    | app f a => isFreeVar x f ∨ isFreeVar x a
    | lam y a => x ≠ y ∧ isFreeVar x a
    | pi y A B => isFreeVar x A ∨ (x ≠ y ∧ isFreeVar x B)
  instance: Membership Var (Term Var) where
    mem := Term.isFreeVar

  def freeVars: Term Var → List Var :=
    aux []
  where aux (binders: List Var): Term Var → List Var
    | var y => if y ∈ binders then [] else [y]
    | app f a => aux binders f ++ aux binders a
    | lam y a => aux (y::binders) a
    | pi y A B => aux binders A ++ aux (y::binders) B

  -- theorem freeVars.aux_cons' {x: Var} (y: Var) {ys: List Var} {term: Term Var}
  --     (h: x ∈ aux (y::ys) term)
  --   : x ∈ aux ys term
  -- :=
  --   match term with
  --   | var z => by
  --     unfold aux; split;
  --     . case inl h' => 
  --   | app f a => _
  --   | lam y a => _
  --   | pi y A B => _
  theorem freeVars.aux_cons {x: Var} (y: Var) {ys: List Var} {term: Term Var}
      (h: x ∉ aux ys term)
    : x ∉ aux (y::ys) term
  := sorry
    -- match term with
    -- | var y => _
    -- | app f a => _
    -- | lam y a => _
    -- | pi y A B => _
  theorem freeVars.aux_head {x: Var} {binders: List Var}
      (term: Term Var) (h: x ∈ binders)
    : x ∉ aux binders term
  :=
    match term with
    | var y =>
      if h': x = y then by
        rw [h'.symm]; unfold aux; simp [h]; intros k; exact nomatch k
      else by
        unfold aux; split;
        . case inl h => simp [h]; exact fun g => nomatch g
        . case inr h => simp [h]; intros g; apply h'; match g with | .head _ => rfl
    | app f a => fun h' => h'.append_or.elim (aux_head f h) (aux_head a h)
    | lam y a => aux_cons y (aux_head a h)
    | pi y A B => fun h' =>
      h'.append_or.elim (aux_head A h) (aux_cons y (aux_head B h))
  theorem freeVars.aux_tail {x: Var} {binders: List Var}
      (term: Term Var) (h: x ∉ binders)
    : x ∈ freeVars.aux binders term ↔ x ∈ freeVars term
    := sorry

  #check decide
  #check List.Mem
  -- instance (x: Var) (term: Term Var): Decidable (x ∈ term) where

  theorem mem_freeVars_of_isFreeVar {x: Var}
    : {term: Term Var} → isFreeVar x term → x ∈ term.freeVars
    | var y, h => h ▸ List.Mem.head []
    | app f a, .inl h
    | pi y A B, .inl h => List.mem_append_of_mem_left _ (mem_freeVars_of_isFreeVar h)
    | app f a, .inr h => List.mem_append_of_mem_right _ (mem_freeVars_of_isFreeVar h)
    | lam y a, ⟨hne, h⟩ =>
      have: x ∉ [y] | .head [] => hne rfl
      (freeVars.aux_tail a this).mpr (mem_freeVars_of_isFreeVar h)
    | pi y A B, .inr ⟨hne, h⟩ =>
      suffices x ∈ freeVars.aux [y] B from List.mem_append_of_mem_right _ this
      have: x ∉ [y] | .head [] => hne rfl
      (freeVars.aux_tail B this).mpr (mem_freeVars_of_isFreeVar h)

  theorem isFreeVar_of_mem_freeVars {x: Var}
    : {term: Term Var} → x ∈ term.freeVars → isFreeVar x term
    | var _, .head _ => rfl
    | app f a, h => h.append_or.elim
      (.inl ∘ isFreeVar_of_mem_freeVars)
      (.inr ∘ isFreeVar_of_mem_freeVars)
    | lam y a, h => 
      if h': x = y then
        absurd (h' ▸ h) (freeVars.aux_head a (.head (a := x) []))
      else
        suffices x ∈ freeVars a from ⟨h', isFreeVar_of_mem_freeVars this⟩
        have: x ∉ [y] | .head [] => h' rfl; (freeVars.aux_tail a this).mp h
    | pi y A B, h => h.append_or.elim
      (.inl ∘ isFreeVar_of_mem_freeVars) (fun h => .inr <|
      if h': x = y then
        absurd (h' ▸ h) (freeVars.aux_head B (.head (a := x) []))
      else
        suffices x ∈ freeVars B from ⟨h', isFreeVar_of_mem_freeVars this⟩
        have: x ∉ [y] | .head [] => h' rfl; (freeVars.aux_tail B this).mp h
    )
  
  /-!
  -- mutual recursion doesn't support structural recursion
  theorem isFreeVar_of_mem_freeVars {x: Var}
    : {term: Term Var} → x ∈ term.freeVars → isFreeVar x term
    | var _, .head _ => rfl
    | app f a, h => h.append_or.elim
      (.inl ∘ isFreeVar_of_mem_freeVars)
      (.inr ∘ isFreeVar_of_mem_freeVars)
    | lam y a, h => aux h
    | pi y A B, h => h.append_or.elim
      (.inl ∘ isFreeVar_of_mem_freeVars) (.inr ∘ aux)
  where aux {x y: Var} {a: Term Var} (h: x ∈ freeVars.aux [y] a)
    : x ≠ y ∧ isFreeVar x a :=
    if h': x = y then
      absurd (h' ▸ h) (freeVars.aux.head a (.head (a := x) []))
    else
      suffices x ∈ freeVars a from ⟨h', isFreeVar_of_mem_freeVars this⟩
      suffices x ∉ [y] from (freeVars.aux.tail a this).mp h
      fun | .head [] => h' rfl
  -/

  instance isFreeVarDec (x: Var) (term: Term Var): Decidable (x ∈ term) :=
    decidable_of_decidable_of_iff ⟨isFreeVar_of_mem_freeVars, mem_freeVars_of_isFreeVar⟩

end Term

/-- Universe. -/
axiom Term.U: Term Var
-- inductive Uni
-- def Uni.toTerm: Uni → Term Var := sorry

def Seq.uni.intro {Γ: Ctx Var}
  : Seq Γ .ctx → Seq Γ (.typ Term.U)
  := sorry

def Seq.uni.type {Γ: Ctx Var} {A: Term Var}
  : Seq Γ (.typ A) → Seq Γ (.val A Term.U)
  := sorry

example {Γ: Ctx Var}
  : Seq Γ .ctx → Seq Γ (.val Term.U Term.U)
  | j => Seq.uni.type (Seq.uni.intro j)


end MLTT2

example (p q: Prop) (h: p → q): ¬q → ¬p
  | hnq, hp => hnq (h hp)

theorem List.not_mem_nil {α} (a: α) (h: List.Mem a []): False := nomatch h
  -- | .tail _ _ => nomatch
  -- | .head _ => nomatch