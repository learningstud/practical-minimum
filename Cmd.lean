
def ofefes: Array String := #[
  "zero", "un", "deux", "trois", "quatre",
  "cinq", "six", "sept", "huit", "neuf",
  "dix", "onze"
]

def le15: Fin 15 → String
  | 0 => "zéro"
  | 1 => "un"
  | 2 => "deux"
  | 3 => "trois"
  | 4 => "quatre"
  | 5 => "cinq"
  | 6 => "six"
  | 7 => "sept"
  | 8 => "huit"
  | 9 => "neuf"
  | 10 => "dix"
  | 11 => "onze"
  | 12 => "douze"
  | 13 => "treize"
  | 14 => "quatorze"
  -- | 15 => "quinze"
  -- | 16 => "seize"

def ones: Fin 11 → String
  | 0 => "zéro"
  | 1 => "un"
  | 2 => "deux"
  | 3 => "trois"
  | 4 => "quatre"
  | 5 => "cinq"
  | 6 => "six"
  | 7 => "sept"
  | 8 => "huit"
  | 9 => "neuf"
  | 10 => "dix"
  -- | 11 => "onze"
  -- | 12 => "douze"
  -- | 13 => "treize"
  -- | 14 => "quatorze"
  -- | 15 => "quinze"
  -- | 16 => "seize"
  -- | 17 => "dix-sept"
  -- | 18 => "dix-huit"
  -- | 19 => "dix-neuf"

def tens: Fin 10 → String
  | 0 => ones 0
  | 1 => ones 10
  | 2 => "vingt"
  | 3 => "trente"
  | 4 => "quarante"
  | 5 => "cinquante"
  | 6 => "soixant"
  | 7 => "soixant-dix"
  | 8 => "quatre-vingts"
  | 9 => "quatre-vingts-dix"

#check Fin.val_lt_of_le
#check Fin.coeToNat

instance (n: Nat): Coe (Fin n) (Fin n.succ) where
  coe x := ⟨x.val, .step x.isLt⟩

def tens_ones_simp (ten: Fin 10): Fin 10 → String
  | 0 => tens ten
  | 1 => tens ten ++ " et " ++ ones 1
  | one => tens ten ++ "-" ++ ones one

#check Nat.lt_sub_of_add_lt
#check Nat.sub_add_cancel
def le20 (n: Fin 20): String :=
  let one: Fin 10 := ⟨n.val - 10, _⟩
  match one with
  | 0 => ones one
  | 1 => "onze"
  | 2 => "douze"
  | 3 => "treize"
  | 4 => "quatorze"
  | 5 => "quinze"
  | 6 => "seize"
  | one => tens 1 ++ "-" ++ ones one
  -- if n > 10 then
  --   if n < 17 then
  --     match n with
  --     | 11 => "onze"
  --     | 12 => "douze"
  --     | 13 => "treize"
  --     | 14 => "quatorze"
  --     | 15 => "quinze"
  --     | 16 => "seize"
  --   else

#check Nat.add_sub_cancel
example (n: Fin 20): n.val - 10 < 10 :=
  have: 10 ≤ 20 := by decide
  have := Nat.sub_add_cancel this
  _