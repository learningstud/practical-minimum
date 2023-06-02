set_option autoImplicit false

#check Antisymm

abbrev Rel.{u} (α: Sort u) := α → α → Prop
namespace Rel
universe u
variable {α: Sort u}

/-- Subrelation (`⊆`). -/
class Sub (r s: Rel α): Prop where
  sub {x y}: r x y → s x y
@[inherit_doc] infix:50 " ⊆ " => Sub
-- /-- `a ∉ b` is negated elementhood. It is notation for `¬ (a ∈ b)`. -/
-- notation:50 a:50 " ⊆ " b:50 => ¬ (a ⊆ b)

class Refl (r: Rel α): Prop where
  refl x: r x x
class Symm (r: Rel α): Prop where
  symm {x y}: r x y → r y x
class Antisymm (r: Rel α): Prop where
  antisymm {x y}: r x y → r y x → x = y
class Trans (r: Rel α): Prop where
  trans {x y z}: r x y → r y z → r x z

-- inductive Closure (r: Rel α) (p: Rel α → Prop): α → α → Prop
--   | embed {x y}: r x y → Closure r p x y
--   | close {x y}: p (Closure r p) → Closure r p x y

inductive ReflClosure (r: Rel α): Rel α
  | embed {x y}: r x y → ReflClosure r x y
  | refl x: ReflClosure r x x
instance (r: Rel α): r ⊆ (ReflClosure r) where sub := .embed
instance (r: Rel α): Refl (ReflClosure r) where refl := .refl

inductive TransClosure (r: Rel α): Rel α
  | embed {x y}: r x y → TransClosure r x y
  | trans {x y z}: TransClosure r x y → TransClosure r y z → TransClosure r x z
instance (r: Rel α): r ⊆ (TransClosure r) where sub := .embed
instance (r: Rel α): Trans (TransClosure r) where trans := .trans

end Rel

class inductive WF.Acc {α} (r: α → α → Prop): α → Prop
  | intro {x} (h: ∀ {y}, r y x → Acc r y): Acc r x
abbrev WF {α} (r: α → α → Prop) := ∀ a, WF.Acc r a
namespace WF

namespace experimental1
  variable {α} (r: α → α → Prop)
  inductive WF: Prop | intro (h: ∀ a, Acc r a)
  example: WF r ↔ (∀ a, Acc r a) := ⟨fun | .intro h => h, .intro⟩
end experimental1

universe u
variable {α: Sort u} {r s: α → α → Prop} [hwf: WF r]

theorem recursion.{v} {motive: α → Sort v}
  (a: α) (F: ∀ x, (∀ y, r y x → motive y) → motive x): motive a
:= (hwf a).rec fun _ ih => F _ fun _ => ih

abbrev induction {motive: α → Prop}
: (a: α) → (∀ x, (∀ y, r y x → motive y) → motive x) → motive a
:= recursion

theorem fixF.{v} {motive: α → Sort v}
  (F: ∀ x, (∀ y, r y x → motive y) → motive x) (a: α) (h: Acc r a)
: motive a
:= recursion a F

-- def fixFEq (a: α) (acx : Acc r x) : fixF F x acx = F x (fun (y : α) (p : r y x) => fixF F y (Acc.inv acx p)) := by
--   induction acx with
--   | intro x r _ => exact rfl

instance wf [sub: r ⊆ s] (h: WF s): WF r :=
  fun _ => .intro fun {x} _ => aux (h x)
where aux {a: α} (h: Acc s a): Acc r a :=
  h.rec fun _ ih => .intro (ih ∘ sub.sub)

-- def accessible {z : α} (ac : Acc r z) : Acc (TC r) z := by
--   induction ac with
--   | intro x acx ih =>
--     apply Acc.intro x
--     intro y rel
--     induction rel with
--     | base a b rab => exact ih a rab
--     | trans a b c rab _ _ ih₂ => apply Acc.inv (ih₂ acx ih) rab

def wftc (h: WF r): WF (Rel.TransClosure r) :=
  fun _ => .intro fun {y} _ => aux (h y)
where aux {a: α} (h: Acc r a): Acc (Rel.TransClosure r) a :=
  h.rec fun {x} h ih => .intro fun rel =>
    rel.rec (fun k => ih k) fun k _ ih' _ => ih'


-- class WellFoundedRelation (α : Sort u) where
--   rel : α → α → Prop
--   wf  : WellFounded rel

end WF
