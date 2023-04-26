set_option autoImplicit false
-- set_option linter.unusedVariables false

-- class inductive Ext.{u} {T: Type u} (eval: T → T → T): T → T → Prop
--   | ext {f g: T} (extEq: ∀x, Ext eval (eval f x) (eval g x)): Ext eval f g
inductive Ext.{u} {T: Type u} (eval: T → T → T): T → T → Prop
  | ext {f g: T} (extEq: ∀x, eval f x = eval g x): Ext eval f g
namespace Ext
  universe u
  variable {T: Type u} (eval: T → T → T) (f g h: T)

  theorem refl: Ext eval f f := ext fun _ => rfl
  theorem symm: Ext eval f g → Ext eval g f
    | ext e => ext fun x =>
      match f, g, e x with
      | _, _, rfl => rfl
end Ext

/-
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



end Term
-/

-- abbrev ExtConst (t: Term) := Ext (fun _ _ => t)
-- theorem refl (t: Term): ExtConst t t t := ext fun _ => refl t

-- theorem reflUniq {eval eval': Term → Term → Term}
--   : (∀x, Ext eval x x) → (∀x, Ext eval' x x) → ∀ f x, eval f x = eval' f x
--   | h, h', f, x =>
--     match h f, h' f with
--     | ext k, ext k' => _
