/-
https://github.com/leanprover/lean/blob/72a965986fa5aeae54062e98efb3140b2c4e79fd/library/init/logic.lean#L539-L544
https://github.com/leanprover-community/mathlib4/blob/5230db6df2ef97710db9e1c217513ec17566814c/Mathlib/Init/Logic.lean#L212-L217
-/
def ExistsUnique (p: α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean TSyntax.Compat in
macro "∃! " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

@[app_unexpander ExistsUnique] def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)               => `(∃! ($x:ident : $t), $b)
  | _                                               => throw ()


def AtMostOne (p: α → Prop) := ¬∃ x y: α, x ≠ y ∧ p x ∧ p y

open Lean TSyntax.Compat in
macro "∃? " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``AtMostOne xs b

@[app_unexpander AtMostOne] def unexpandAtMostOne : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃? $xs:binderIdent*, $b) => `(∃? $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                      => `(∃? $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)               => `(∃? ($x:ident : $t), $b)
  | _                                               => throw ()

theorem all_then_not_exists_not {p: α → Prop} (h: ∀ x, p x): ¬∃ x, ¬p x
  | ⟨x, hnp⟩ => hnp (h x)
example {p: α → Prop} (h: ¬∀ x, p x) : ∃ x : α, ¬p x := sorry
theorem not_exists_not {p: α → β → Prop}: (∀ a b, p a b) → ¬∃ a, ∃ b, ¬p a b
  | h, ⟨a, b, hnp⟩ => hnp (h a b)

#check funext
#check Classical.axiomOfChoice
#check Classical.choice
#check Quot
#check Quotient


-- import Mathlib.Init.ZeroOne
/-! ## Classes for `Zero` and `One` -/

class Zero (α: Type _) where
  zero: α
instance {α} [self: Zero α]: OfNat α (nat_lit 0) where
  ofNat := self.zero
instance {α} [OfNat α (nat_lit 0)]: Zero α where
  zero := 0
-- @[simp] protected theorem Zero.zero_eq {α} [self: Zero α]: self.zero = 0 := rfl

class One (α: Type _) where
  one: α
instance {α} [self: One α] : OfNat α (nat_lit 1) where
  ofNat := self.one
instance {α} [OfNat α (nat_lit 1)]: One α where
  one := 1
-- @[simp] protected theorem One.one_eq {α} [self: One α]: self.one = 1 := rfl

abbrev Invertible (α) [Zero α] := { a: α // a ≠ 0 }
postfix:arg "ˣ" => Invertible
-- instance {α} [Zero α] {a: α} {nonzero: a ≠ 0}: CoeDep α a αˣ where
--   coe := ⟨a, nonzero⟩

class Inv (α) extends Zero α where
  inv (a: αˣ): αˣ
postfix:arg "⁻¹" => Inv.inv
