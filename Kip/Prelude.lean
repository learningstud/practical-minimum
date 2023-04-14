set_option autoImplicit false

universe u v
variable {α: Type u} {β: Type v}

theorem some_ne_none {α}: {opt: Option α} → opt.isSome ≠ opt.isNone
  | some _, h => nomatch h
  | none, h => nomatch h

theorem not_some_none {α} {opt: Option α}: opt.isSome → opt.isNone → False
  | h, hn => some_ne_none (h.trans hn.symm)

namespace List

  #check List.mem_append_of_mem_left
  #check List.mem_append_of_mem_right

  example {xs: List α}: [] ++ xs = xs := rfl
  example {a: α} {xs ys: List α}: (a::xs) ++ ys = a::(xs ++ ys) := rfl

  theorem mem_or_of_mem_append {a: α}
    : {xs ys: List α} → a ∈ xs ++ ys → a ∈ xs ∨ a ∈ ys
    | [], ys, h => .inr h
    | _::xs, ys, .head _ => .inl (.head xs)
    | x::xs, ys, .tail _ h => (mem_or_of_mem_append h).elim (.inl ∘ .tail x) .inr
  
  variable [DecidableEq α]

  example (a x: α) (b: β) (l: List (α × β))
    : ((a, b)::l).lookup x = cond (x == a) (some b) (l.lookup x)
    := rfl
  
  example (a: α) (b: β) (l: List (α × β))
    : cond (a == a) (some b) (l.lookup a) = some b
    := beq_self_eq_true a ▸ rfl

  theorem cons_lookup_some {a: α} (x: α × β) {l: List (α × β)}
    : (l.lookup a).isSome → ((x::l).lookup a).isSome
    | h => by unfold lookup; split; rfl; exact h
  
  theorem cons_lookup_some_eq_head (a: α) (b: β) (l: List (α × β))
    : ((a, b)::l).lookup a = some b
    := by unfold lookup; simp
    -- := show cond (a == a) _ _ = _ from beq_self_eq_true a ▸ rfl
  
  theorem lookup_of_mem {a: α} {b: β} {l: List (α × β)}
    : (a, b) ∈ l → (l.lookup a).isSome
    | .head l => congrArg Option.isSome (cons_lookup_some_eq_head a b l)
    | .tail (as := l) x h => cons_lookup_some x (lookup_of_mem h)
  
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

#check cond_true