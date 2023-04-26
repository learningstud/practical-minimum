/-
- [λ](https://en.wikipedia.org/wiki/Lambda_calculus_definition)
- [η](https://math.stackexchange.com/a/836124)
- [substitution vs application](https://cs.stackexchange.com/questions/69790/difference-between-beta-reduction-and-substitution)
- https://math.stackexchange.com/questions/1832272/categorical-semantics-explained-what-is-an-interpretation
- [capture-avoiding substitution](https://en.wikipedia.org/wiki/Lambda_calculus#Capture-avoiding_substitutions)

All equivalences (α,β,η) are guided by extensionality. 
-/
import Kip.Prelude

set_option autoImplicit false
-- set_option linter.unusedVariables false

namespace Untyped

-- inductive 

/-- Underspecification; only to be constrained by judgments. -/
inductive Term.{u} (Var: Type u) where
  | var (x: Var)
  | lam (binder: Var) (predicate: Term Var)
  | app (function argument: Term Var)
  -- deriving DecidableEq

namespace Term
  universe u
  variable {Var: Type u}

  instance: Coe Var (Term Var) where coe := .var
  infixr:25 " ↦ " => Term.lam
  instance: CoeFun (Term Var) (fun _ => Term Var → Term Var) where
    coe f := f.app

  inductive free (x: Var): Term Var → Prop
    | var: free x x
    | lam {y: Var} {t: Term Var}: x ≠ y → free x t → free x (y ↦ t)
    | appFun {f a: Term Var}: free x f → free x (f a)
    | appArg {f a: Term Var}: free x a → free x (f a)
  instance: Membership Var (Term Var) where mem := free

  variable [DecidableEq Var]

  instance freeDec (x: Var): (t: Term Var) → Decidable (x ∈ t)
    | var y =>
      if h: x = y then isTrue (h ▸ .var) else isFalse fun | .var => h rfl
    | lam y t =>
      if h: x = y then isFalse fun | .lam hn _ => hn h else
      match freeDec x t with
      | isTrue h' => isTrue (.lam h h')
      | isFalse h' => isFalse fun | .lam _ h => h' h
    | app f a => 
      match freeDec x f, freeDec x a with
      | isTrue hf, _ => isTrue (.appFun hf)
      | _, isTrue ha => isTrue (.appArg ha)
      | isFalse hnf, isFalse hna => isFalse fun
        | .appFun hf => hnf hf
        | .appArg ha => hna ha

  /-- `A[t / x]`, i.e., `A[x := t]` -/
  def subst (A t: Term Var) (x: Var): Term Var :=
    match A with
    | var y => if x = y then t else A
    | y ↦ s => if x = y then A else y ↦ (s.subst t x)
    | app f a => (f.subst t x) (a.subst t x)
  
  @[inherit_doc subst] macro:max A:term noWs "[" x:ident  "←" t:term "]" : term
    => `(subst $A $t $x)
  example (A t: Term Var) (x: Var): A[x←t] = A.subst t x := rfl

  theorem subst_self (A: Term Var) (x: Var): A[x←x] = A :=
    match A with
    | var y => if h: x = y then trans (if_pos h) (congrArg var h) else if_neg h
    | y ↦ s => if h: x = y then if_pos h else
      trans (if_neg h) (congrArg (y ↦ .) (s.subst_self x))
    | app f a => congr (congrArg app (f.subst_self x)) (a.subst_self x)

  theorem subst_nonfree {A: Term Var} {x: Var} (nonfree: x ∉ A) (t: Term Var)
    : A[x←t] = A :=
    match A with
    | var y => if_neg fun | rfl => nonfree .var
    | y ↦ s => if g: x = y then if_pos g else
      have hs := subst_nonfree (nonfree ∘ .lam g) t
      trans (if_neg g) (congrArg (y ↦ .) hs)
    | app f a =>
      have hf := subst_nonfree (nonfree ∘ .appFun) t
      have ha := subst_nonfree (nonfree ∘ .appArg) t
      congr (congrArg app hf) ha

  protected abbrev closed (A: Term Var): Prop := ∀ x: Var, x ∉ A

  theorem subst_closed {A: Term Var} (closed: A.closed) (x: Var) (t: Term Var)
    : A[x←t] = A := subst_nonfree (closed x) t

  -- def αconv (A: Term Var) (x x': Var): Term Var :=
  --   match A with
  --   | var y => if x = y then t else A
  --   | y ↦ s => if x = y then A else lam y (s.αconv x x')
  --   | app f a => app (f.αconv x x') (a.αconv x x')
  def αconvible1 (A: Term Var) (x x': Var): Bool :=
    aux A x x' true
  where aux (A: Term Var) (x x': Var) (yes: Bool): Bool :=
    match A with
    | var y => x ≠ y || yes
    | y ↦ s => x = y || aux s x x' (yes && x' ≠ y)
    | app f a => aux f x x' yes && aux a x x' yes
  
  inductive αconvible (x x': Var): (A: Term Var) → Prop
    | varNe {y: Var}: x ≠ y → αconvible x x' y
    | lamBound (s: Term Var): αconvible x x' (x ↦ s)
    | app {f a: Term Var}
      : αconvible x x' f → αconvible x x' a → αconvible x x' (f a)

  /-- Everything is guided by extensionality. -/
  inductive Equiv: Term Var → Term Var → Prop
    | refl (A: Term Var): Equiv A A
    -- | α (x y: Var) (A: Term Var): Equiv (x ↦ A) (y ↦ A[x←y])
    -- | β (x: Var) (A B: Term Var): Equiv ((x ↦ A) B) (A[x←B])
    -- | η (x: Var) (A: Term Var): Equiv (x ↦ A x) A
  
  inductive substitutable (t: Term Var) (x: Var): Term Var → Prop where
    | var (y: Var): substitutable t x y
    | lamBound (A: Term Var): substitutable t x (x ↦ A)
    | lamFree {y: Var} {A: Term Var} -- `x ≠ y` is unnecessary
      : y ∉ t → substitutable t x A → substitutable t x (y ↦ A)
    | app {f a: Term Var}
      : substitutable t x f → substitutable t x a → substitutable t x (f a)
end Term

/-
Two caveats of α-conversion.
- `λx.λx.x` could be α-converted into `λy.λx.x` but not `λy.λx.y`.
- `x with y` in `λx.λy.x`, we get `λy.λy.y`, which is not at all the same
-/

end Untyped

#check {x: Nat // x < 3 }
example (l: List Nat): l[0]'sorry = 0 := sorry