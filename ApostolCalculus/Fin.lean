instance: CoeSort Nat Type where
  coe := Fin
instance: OfNat Type n where
  ofNat := Fin n

#check proofIrrel

theorem eq_0_of_lt_1: {n: Nat} → n < 1 → n = 0
  | 0, _ => rfl
  | .succ n, h => (n.not_lt_zero (Nat.le_of_succ_le_succ h)).elim

example: (a b: 1) → a = b
  | ⟨a, ha⟩, ⟨b, hb⟩ =>
    match a, b, (eq_0_of_lt_1 ha).trans (eq_0_of_lt_1 hb).symm with
    | _, _, rfl => by rw [proofIrrel ha hb]

theorem Fin_0_rec (motive: 0 → Sort u) (t: 0): motive t :=
  (t.val.not_lt_zero t.isLt).elim
example: 0 = Empty := sorry