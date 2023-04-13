set_option autoImplicit false
set_option linter.unusedVariables false

/-
class MLTT.{u} (Var: Type u) [decEq: DecidableEq Var] where
  Term: Type u
  var (x: Var): Term
  lam (binder: Var) (predicate: Term): Term
  pi (binder: Var) (domain predicate: Term): Term
  app (function argument: Term): Term

  Jud: Type u
  jctx: Jud
  jtyp (A: Term): Jud
  jval (a A: Term): Jud
  jteq (A B: Term): Jud
  jeq (a b A: Term): Jud

  Seq: List (Var × Term) → Jud → Type u
  ctx_ok {Γ: List (Var × Term)} {j: Jud}: Seq Γ j → Seq Γ jctx
-/

theorem isSome_ne_isNone {α}: {opt: Option α} → opt.isSome ≠ opt.isNone
  | some _, h => nomatch h
  | none, h => nomatch h

namespace List
  universe u v
  variable {α: Type u}

  #check List.mem_append_of_mem_left
  #check List.mem_append_of_mem_right

  example {xs: List α}: [] ++ xs = xs := rfl
  example {a: α} {xs ys: List α}: (a::xs) ++ ys = a::(xs ++ ys) := rfl

  theorem List.mem_or_of_mem_append {a: α}
    : {xs ys: List α} → a ∈ xs ++ ys → a ∈ xs ∨ a ∈ ys
    | [], ys, h => .inr h
    | _::xs, ys, .head _ => .inl (.head xs)
    | x::xs, ys, .tail _ h => (mem_or_of_mem_append h).elim (.inl ∘ .tail x) .inr
  
  variable [DecidableEq α] {β: Type v}
  
  theorem cons_lookup_some_eq_head (a: α) (b: β) (l: List (α × β))
    : ((a, b)::l).lookup a = some b :=
    by unfold List.lookup; simp

  -- theorem ne_head_of_cons_lookup_none {x a: α} {b: β} {l: List (α × β)}
  --   : ((a, b)::l).lookup x = none → a ≠ x
  --   | h, rfl => by unfold List.lookup at h; simp at h
  
  -- theorem lookup_none_of_cons_lookup_none {x a: α} {b: β} {l: List (α × β)}
  --   : ((a, b)::l).lookup x = none → l.lookup x = none
  --   | h => by unfold List.lookup at h; split at h; exact nomatch h; exact h
  
  theorem lookup_none {x a: α} {b: β} {l: List (α × β)}
    : (((a, b)::l).lookup x).isNone → a ≠ x ∧ (l.lookup x).isNone
    | h => by
      unfold List.lookup at h; apply And.intro
      . intro h'; match h' with | rfl => simp at h; exact nomatch h
      . split at h; exact nomatch h; exact h

  theorem lookup_some {x a: α} {b: β} {l: List (α × β)}
    : (((a, b)::l).lookup x).isSome → a = x ∨ (l.lookup x).isSome
    | h => by
      unfold List.lookup at h; split at h
      . apply Or.inl; apply Eq.symm; apply of_decide_eq_true; assumption
      . exact Or.inr h

end List

namespace MLTT3

/-- Underspecification; only to be constrained by judgments. -/
inductive Term.{u} (Var: Type u) where
  | var (x: Var)
  | lam (binder: Var) (predicate: Term Var)
  | pi (binder: Var) (domain predicate: Term Var)
  | app (function argument: Term Var)

namespace Term
  universe u
  variable {Var: Type u}

  instance: Coe Var (Term Var) where coe := .var

  inductive free (x: Var): Term Var → Prop
    | var: free x (var x)
    | lam {binder: Var} {predicate: Term Var}
      : x ≠ binder → free x predicate → free x (lam binder predicate)
    | pid {domain: Term Var} (binder: Var) (predicate: Term Var)
      : free x domain → free x (pi binder domain predicate)
    | pip {binder: Var} {predicate: Term Var} (domain: Term Var)
      : x ≠ binder → free x predicate → free x (pi binder domain predicate)
    | appf {f: Term Var} (a: Term Var)
      : free x f → free x (app f a)
    | appa {a: Term Var} (f: Term Var)
      : free x a → free x (app f a)
  instance: Membership Var (Term Var) where mem := free

  variable [DecidableEq Var]

  instance freeDec (x: Var): (t: Term Var) → Decidable (x ∈ t)
    | var y =>
      if h: x = y then isTrue (h ▸ .var) else isFalse fun | .var => h rfl
    | app f a =>
      match freeDec x f, freeDec x a with
      | isTrue hf, _ => isTrue (.appf a hf)
      | _, isTrue ha => isTrue (.appa f ha)
      | isFalse hnf, isFalse hna => isFalse fun
        | .appf _ hf => hnf hf
        | .appa _ ha => hna ha
    | lam y t =>
      if h: x = y then isFalse fun | .lam hn _ => hn h else
      match freeDec x t with
      | isTrue h' => isTrue (.lam h h')
      | isFalse h' => isFalse fun | .lam _ h => h' h
    | pi y s t =>
      match freeDec x s with
      | isTrue h => isTrue (.pid y t h)
      | isFalse hn => -- this arm is the same as the `lam` arm
        if h: x = y then isFalse fun | .pid _ _ h | .pip _ hn _ => hn h else
        match freeDec x t with
        | isTrue h' => isTrue (.pip s h h')
        | isFalse h' => isFalse fun | .pid _ _ h => hn h | .pip _ _ h => h' h

  -- theorem free_var_iff_eq {x y: Var}: x ∈ var y ↔ x = y :=
  --   ⟨fun | .var => rfl, fun | rfl => .var⟩

  /-- `A[t / x]`, i.e., `A[x := t]`

  The sensible requirement that "`t` must be free in `A` if `t` is a variable"
    is only enforced by judgments. Directly calling `subst` on terms out of
    context can cause accidental captures of free variables if `t` is a variable
    bounded in `A`. All "operations on terms" (i.e., judgments) only make sense
    in the correct context.
  -/
  def subst (A t: Term Var) (x: Var): Term Var :=
    match A with
    | var y => if x = y then t else A
    | lam y s => if x = y then A else lam y (s.subst t x)
    | pi y d s => pi y (d.subst t x) (if x = y then s else s.subst t x)
    | app f a => app (f.subst t x) (a.subst t x)

  theorem subst_self (A: Term Var) (x: Var): A.subst (var x) x = A :=
    match A with
    | var y => if h: x = y then trans (if_pos h) (congrArg var h) else if_neg h
    | app f a => congr (congrArg app (f.subst_self x)) (a.subst_self x)
    | lam y s => if h: x = y then if_pos h else
      trans (if_neg h) (congrArg (lam y) (s.subst_self x))
    | pi y d s =>
      have hd := subst_self d x
      congr (congrArg (pi y) hd) <| if h: x = y then if_pos h else
        trans (if_neg h) (subst_self s x)

  theorem subst_bounded {A: Term Var} {x: Var} (h: x ∉ A) (t: Term Var)
    : A.subst t x = A :=
    match A with
    | var y => if_neg fun | rfl => h .var -- if_neg (h ∘ free_var_iff_eq.mpr)
    | app f a =>
      have hf := subst_bounded (h ∘ .appf a) t
      have ha := subst_bounded (h ∘ .appa f) t
      congr (congrArg app hf) ha
    | lam y s => if g: x = y then if_pos g else
      have hs := subst_bounded (h ∘ .lam g) t
      trans (if_neg g) (congrArg (lam y) hs)
    | pi y d s =>
      have hd := subst_bounded (h ∘ .pid y s) t
      congr (congrArg (pi y) hd) <| if g: x = y then if_pos g else
        trans (if_neg g) (subst_bounded (h ∘ .pip d g) t)

end Term


abbrev Ctx.{u} (Var: Type u) := List (Var × Term Var)

inductive Jud.{u} (Var: Type u)
  | ctx
  | typ (A: Term Var)
  | var (a A: Term Var)

universe u
variable {Var: Type u} [DecidableEq Var]

namespace Jud
  inductive free (x: Var): Jud Var → Prop
    | typ {A: Term Var}: x ∈ A → free x (.typ A)
    | var {a: Term Var} (A: Term Var): x ∈ a → free x (.var a A)
    | var_typ (a: Term Var) {A: Term Var}: x ∈ A → free x (.var a A)
  instance: Membership Var (Jud Var) where mem := free

  instance freeDec (x: Var): (j: Jud Var) → Decidable (x ∈ j)
    | ctx => isFalse fun h => nomatch h
    | typ A => if h: x ∈ A then isTrue (.typ h) else isFalse fun | .typ h' => h h'
    | var a A =>
      if h₁: x ∈ a then isTrue (.var A h₁)
      else if h₂: x ∈ A then isTrue (.var_typ a h₂)
      else isFalse fun | .var _ h => h₁ h | .var_typ _ h => h₂ h
end Jud

inductive Seq: Ctx Var → Jud Var → Type _
  | emp
    : Seq [] .ctx
  | ext {Γ: Ctx Var} {x: Var} {A: Term Var}
    : Seq Γ (.typ A) → (Γ.lookup x).isNone → Seq ((x, A)::Γ) .ctx
  | pi {Γ: Ctx Var} {x: Var} {A B: Term Var}
    : Seq ((x, A)::Γ) (.typ B) → Seq Γ (.typ (.pi x A B))
  | var {Γ: Ctx Var} {x: Var} {A: Term Var}
    : Seq Γ .ctx → (x, A) ∈ Γ → Seq Γ (.var x A)

def Seq.ctx_ok {Γ: Ctx Var} {j: Jud Var}
  : Seq Γ j → Seq Γ .ctx
  | σ@emp
  | σ@(ext _ _) => σ
  | pi σ => have .ext σ _ := σ.ctx_ok; σ.ctx_ok
  | var σ _ => σ

def Seq.ext_typ_ok {Γ: Ctx Var} {x: Var} {A: Term Var}
  : Seq ((x, A)::Γ) .ctx → Seq Γ (.typ A)
  | ext σ _ => σ

-- def Seq.ext_ctx_ok {Γ: Ctx Var} {x: Var} {A: Term Var}
--   : Seq ((x, A)::Γ) .ctx → Seq Γ .ctx
--   | j => j.ext_typ_ok.ctx_ok

def Seq.pi_typ_ok {Γ: Ctx Var} {x: Var} {A B: Term Var}
  : Seq Γ (.typ (.pi x A B)) → Seq Γ (.typ A)
  | pi σ => have .ext σ _ := σ.ctx_ok; σ

theorem free_in_jud_of_free_in_ctx {Γ: Ctx Var} {j: Jud Var} {x: Var}
  : Seq Γ j → x ∈ j → (List.lookup x Γ).isSome
  | .pi σ, .typ h =>
    match h with
    | .pid (domain := B) y A h' =>
      have .ext σ _ := σ.ctx_ok; free_in_jud_of_free_in_ctx σ (.typ h')
    | .pip (binder := y) (predicate := A) B hn h' =>
      have := free_in_jud_of_free_in_ctx σ (.typ h')
      (List.lookup_some this).elim (absurd . hn.symm) id
  | .var σ h, .var _ .var => sorry
  | .var σ h, .var_typ _ h' => sorry

theorem var_ne_of_ext {Γ: Ctx Var} {x y: Var} {A B: Term Var}
  : Seq ((x, A)::Γ) .ctx → (y, B) ∈ Γ → x ≠ y
  | .ext _ h, h', rfl => sorry

theorem free_in_typ_of_ext {x y: Var} {A B: Term Var}
  : {Γ: Ctx Var} → Seq ((x, A)::Γ) .ctx → (y, B) ∈ Γ → x ∉ B
  | [], _, h, _ => nomatch h
  | _::Γ, .ext σ h, .head _, h' => by
    unfold List.lookup at h; split at h
    . exact nomatch h
    . have .ext σ _ := σ.ctx_ok
      have := free_in_jud_of_free_in_ctx σ (.typ h')
      exact isSome_ne_isNone (this.trans h.symm)
  | γ::Γ, .ext σ h, .tail _ h', h'' =>
    have := Seq.var σ.ctx_ok (.tail _ h')
    have := free_in_jud_of_free_in_ctx this (.var_typ _ h'')
    isSome_ne_isNone (this.trans h.symm)

example {Γ: Ctx Var} {x y: Var} {A B: Term Var}
  : Seq ((x, A)::(y, B)::Γ) .ctx → y ∉ A → Seq ((y, B)::(x, A)::Γ) .ctx
  | .ext σ h, h' => .ext (
    sorry
  ) (
    have .ext _ g := σ.ctx_ok;
    have: (y == x) = false := decide_eq_false (List.lookup_none h).left
    by unfold List.lookup; simp [this, g]
  )

example {Γ: Ctx Var} {x: Var} {A: Term Var} {j: Jud Var}
  : Seq ((x, A)::Γ) j → x ∉ j → Seq Γ j
  := sorry

example {Γ: Ctx Var} {x: Var} {A: Term Var} {j: Jud Var}
  : Seq Γ j → Seq ((x, A)::Γ) .ctx → Seq ((x, A)::Γ) j
  := sorry

end MLTT3

namespace List
  universe u v
  variable {α: Type u} [DecidableEq α] {β: Type v}

end List

#check Option.isSome
#check some
