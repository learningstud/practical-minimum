/-
- [λ](https://en.wikipedia.org/wiki/Lambda_calculus_definition)
- [η](https://math.stackexchange.com/a/836124)
- [substitution vs application](https://cs.stackexchange.com/questions/69790/difference-between-beta-reduction-and-substitution)
- https://math.stackexchange.com/questions/1832272/categorical-semantics-explained-what-is-an-interpretation
- [capture-avoiding substitution](https://en.wikipedia.org/wiki/Lambda_calculus#Capture-avoiding_substitutions)
- [efficient term rewrite](https://math.stackexchange.com/a/4090017)

All equivalences (α,β,η) are guided by extensionality.
-/
import Kip.Prelude
set_option autoImplicit false
-- set_option linter.unusedVariables false

inductive Term.{u} (Var: Type u) where
  | var (x: Var)
  | lam (binder: Var) (predicate: Term Var)
  | app (function argument: Term Var)
namespace Term

universe u
variable {Var: Type u}

instance: Coe Var (Term Var) where coe := var
infixr:25 " ↦ " => lam
instance: CoeFun (Term Var) (fun _ => Term Var → Term Var) where coe := app

inductive free (x: Var): Term Var → Prop
  | var: free x x
  | lam {y: Var} {t: Term Var}: x ≠ y → free x t → free x (y ↦ t)
  | appFun {f a: Term Var}: free x f → free x (f a)
  | appArg {f a: Term Var}: free x a → free x (f a)
instance: Membership Var (Term Var) where mem := free

-- theorem free_var_iff_eq {x y: Var}: x ∈ var y ↔ x = y :=
--   ⟨fun | .var => rfl, fun | rfl => .var⟩

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

/-- Should be a `Prop`, but Lean4 has its limits. -/
class inductive substitutable (x: Var) (t: Term Var): Term Var → Prop
  | var (y: Var): substitutable x t y
  | lamBound (A: Term Var): substitutable x t (x ↦ A)
  | lamFree {y: Var} {A: Term Var} -- `x ≠ y` is unnecessary
    : y ∉ t → substitutable x t A → substitutable x t (y ↦ A)
  | app {f a: Term Var}
    : substitutable x t f → substitutable x t a → substitutable x t (f a)

/-- Capture-avoiding substitution: `A[x←t]`. -/
def subst (x: Var) (t: Term Var)
  : (A: Term Var) → [precond: substitutable x t A] → Term Var
  | A@(var y), _ => if x = y then t else A
  | A@(y ↦ B), h => if e: x = y then A else
    have: substitutable x t B := match h, e with | .lamFree _ h, _ => h
    y ↦ subst x t B
  | app f a, h =>
    have: substitutable x t f := have .app hf _ := h; hf
    have: substitutable x t a := have .app _ ha := h; ha
    (subst x t f) (subst x t a)

-- @[inherit_doc subst]
-- macro A:term noWs "[" x:ident "←" t:term "]'" h:term:max : term =>
--   `(subst $x $t $A (precond := $h))
@[inherit_doc subst]
macro:max A:term noWs "[" x:ident "←" t:term "]" : term => `(subst $x $t $A)
example {x: Var} {t A: Term Var} [substitutable x t A]: A[x←t] = subst x t A := rfl

-- @[inherit_doc subst]
-- macro:max A:term noWs "[" x:ident "←" t:term "]" : term => `(subst <| by first
--   | exact subst_self.precond $x $A
--   | fail "Failed to prove that the substitution avoids capture. Try:
-- - `have`-expressions to prove that the substitution avoids capture, or
-- - the `A[x←t]'h` notation, where `h` is a proof that the substitution avoids capture."
-- )

-- @[inherit_doc subst]
-- syntax:max term noWs "[" withoutPosition(term "←" term) "]" : term
-- macro_rules | `($A[$x←$x]) => `(subst (subst_self.precond $x $A))

section variable (A: Term Var) (x: Var)
local instance: substitutable x (var x) A := sorry
theorem subst_self: (A: Term Var) → A[x←x] = A
  | var y => if e: x = y then trans (if_pos e) (congrArg var e) else if_neg e
  | y ↦ B => if e: x = y then dif_pos e else
    have hB := subst_self B
    trans (if_neg e) (congrArg (y ↦ .) hB)
  | app f a =>
    have hf := subst_self f
    have ha := subst_self a
    congr (congrArg app hf) ha
end

section variable {x: Var} {A: Term Var} (t: Term Var) (nonfree: x ∉ A)
local instance: substitutable x t A := sorry
theorem subst_nonfree {x: Var} {A: Term Var} (nonfree: x ∉ A): A[x←t] = A :=
  match A with
  | var y => if_neg fun | rfl => nonfree .var
  | y ↦ B => if e: x = y then dif_pos e else
    have hB := subst_nonfree (nonfree ∘ .lam e)
    trans (if_neg e) (congrArg (y ↦ .) hB)
  | app f a =>
    have hf := subst_nonfree (nonfree ∘ .appFun)
    have ha := subst_nonfree (nonfree ∘ .appArg)
    congr (congrArg app hf) ha
end

protected abbrev closed (A: Term Var): Prop := ∀ x: Var, x ∉ A

section variable {A: Term Var} (closed: A.closed) (x: Var) (t: Term Var)
local instance: substitutable x t A := sorry
theorem subst_closed: A[x←t] = A := subst_nonfree t (closed x)
end

end Term

/-
Two caveats of α-conversion.
- `λx.λx.x` could be α-converted into `λy.λx.x` but not `λy.λx.y`.
- `x with y` in `λx.λy.x`, we get `λy.λy.y`, which is not at all the same
-/

#check {x: Nat // x < 3 }
example (l: List Nat): l[0]'sorry = 0 := sorry
#check And