-- import Cpp.lex.ucs
set_option autoImplicit false

/-! 
# [lex.charset](https://timsong-cpp.github.io/cppwp/n4868/lex#charset)
-/

inductive digit: Char → Type
  | «0»: digit '0'
  | «1»: digit '1'
  | «2»: digit '2'
  | «3»: digit '3'
  | «4»: digit '4'
  | «5»: digit '5'
  | «6»: digit '6'
  | «7»: digit '7'
  | «8»: digit '8'
  | «9»: digit '9'

def digit.toNat {ch: Char}: digit ch → Nat
  | «0» => 0
  | «1» => 1
  | «2» => 2
  | «3» => 3
  | «4» => 4
  | «5» => 5
  | «6» => 6
  | «7» => 7
  | «8» => 8
  | «9» => 9

inductive nondigit: Char → Prop
  | _: nondigit '_'
  /- Lowercase. -/
  | a: nondigit 'a'
  | b: nondigit 'b'
  | c: nondigit 'c'
  | d: nondigit 'd'
  | e: nondigit 'e'
  | f: nondigit 'f'
  | g: nondigit 'g'
  | h: nondigit 'h'
  | i: nondigit 'i'
  | j: nondigit 'j'
  | k: nondigit 'k'
  | l: nondigit 'l'
  | m: nondigit 'm'
  | n: nondigit 'n'
  | o: nondigit 'o'
  | p: nondigit 'p'
  | q: nondigit 'q'
  | r: nondigit 'r'
  | s: nondigit 's'
  | t: nondigit 't'
  | u: nondigit 'u'
  | v: nondigit 'v'
  | w: nondigit 'w'
  | x: nondigit 'x'
  | y: nondigit 'y'
  | z: nondigit 'z'
  /- Uppercase. -/
  | A: nondigit 'A'
  | B: nondigit 'B'
  | C: nondigit 'C'
  | D: nondigit 'D'
  | E: nondigit 'E'
  | F: nondigit 'F'
  | G: nondigit 'G'
  | H: nondigit 'H'
  | I: nondigit 'I'
  | J: nondigit 'J'
  | K: nondigit 'K'
  | L: nondigit 'L'
  | M: nondigit 'M'
  | N: nondigit 'N'
  | O: nondigit 'O'
  | P: nondigit 'P'
  | Q: nondigit 'Q'
  | R: nondigit 'R'
  | S: nondigit 'S'
  | T: nondigit 'T'
  | U: nondigit 'U'
  | V: nondigit 'V'
  | W: nondigit 'W'
  | X: nondigit 'X'
  | Y: nondigit 'Y'
  | Z: nondigit 'Z'

inductive basic_source_character_set: Char → Prop
  | space: basic_source_character_set ' '
  | htab: basic_source_character_set '\t'
  | vtab: basic_source_character_set '\x0B'
  | form_feed: basic_source_character_set '\x0C'
  | new_line: basic_source_character_set '\n'

  | digit {ch: Char}: digit ch → basic_source_character_set ch
  | nondigit {ch: Char}: nondigit ch → basic_source_character_set ch

instance {ch: Char}: Coe (digit ch) (basic_source_character_set ch) where
  coe h := .digit h
instance {ch: Char}: Coe (nondigit ch) (basic_source_character_set ch) where
  coe h := .nondigit h

def basic_source_character_set.toChar {ch: Char}
  : basic_source_character_set ch → Char
  | _ => ch
instance {ch: Char}: Coe (basic_source_character_set ch) Char where
  coe := basic_source_character_set.toChar

#eval basic_source_character_set.form_feed.toChar.toNat == 12

inductive hexadecimal_digit: Char → Type
  | digit {ch: Char}: digit ch → hexadecimal_digit ch
  | a: hexadecimal_digit 'a'
  | b: hexadecimal_digit 'b'
  | c: hexadecimal_digit 'c'
  | d: hexadecimal_digit 'd'
  | e: hexadecimal_digit 'e'
  | f: hexadecimal_digit 'f'
  | A: hexadecimal_digit 'A'
  | B: hexadecimal_digit 'B'
  | C: hexadecimal_digit 'C'
  | D: hexadecimal_digit 'D'
  | E: hexadecimal_digit 'E'
  | F: hexadecimal_digit 'F'

-- instance {ch: Char}: Coe (hexadecimal_digit ch) Char where
--   coe _ := ch

-- @[match_pattern]
instance {ch: Char}: Coe (digit ch) (hexadecimal_digit ch) where
  coe h := .digit h
instance {ch: Char}: Coe (hexadecimal_digit ch) (basic_source_character_set ch) where
  coe
  | .digit h => h
  | .a => nondigit.a
  | .b => nondigit.b
  | .c => nondigit.c
  | .d => nondigit.d
  | .e => nondigit.e
  | .f => nondigit.f
  | .A => nondigit.A
  | .B => nondigit.B
  | .C => nondigit.C
  | .D => nondigit.D
  | .E => nondigit.E
  | .F => nondigit.F

def hexadecimal_digit.toNat {ch: Char}: hexadecimal_digit ch → Nat
  | digit h => h.toNat
  | a | A => 0xA
  | b | B => 0xB
  | c | C => 0xC
  | d | D => 0xD
  | e | E => 0xE
  | f | F => 0xF

structure hex_quad (ch3 ch2 ch1 ch0: Char) where
  mk ::
  hex3: hexadecimal_digit ch3
  hex2: hexadecimal_digit ch2
  hex1: hexadecimal_digit ch1
  hex0: hexadecimal_digit ch0

def hex_quad.toNat {ch3 ch2 ch1 ch0: Char}
  : hex_quad ch3 ch2 ch1 ch0 → Nat
  | {hex3, hex2, hex1, hex0} =>
    (hex3.toNat <<< 12) ^ (hex2.toNat <<< 8) ^ (hex1.toNat <<< 4) ^ hex0.toNat

/-- https://timsong-cpp.github.io/cppwp/n4868/lex.charset#nt:universal-character-name -/
inductive universal_character_name
  | u {lo3 lo2 lo1 lo0: Char} (low: hex_quad lo3 lo2 lo1 lo0)
  | U {hi3 hi2 hi1 hi0: Char} (high: hex_quad hi3 hi2 hi1 hi0)
      {lo3 lo2 lo1 lo0: Char} (low: hex_quad lo3 lo2 lo1 lo0)

inductive identifier_nondigit
  | nd {ch: Char} (nd: nondigit ch)
  | ucn (ucn: universal_character_name)

/-- [lex.name](https://timsong-cpp.github.io/cppwp/n4868/lex.name#nt:identifier) -/
inductive identifier
  | idnd (idnd: identifier_nondigit)
  | id_idnd (id: identifier) (idnd: identifier_nondigit)
  | id_d (id: identifier) {ch: Char} (d: digit ch)


/-
inductive basic_source_character_set
  | space | htab | vtab | form_feed | new_line

  | a | b | c | d | e | f | g | h | i | j | k | l | m
  | n | o | p | q | r | s | t | u | v | w | x | y | z

  | A | B | C | D | E | F | G | H | I | J | K | L | M
  | N | O | P | Q | R | S | T | U | V | W | X | Y | Z

  | «0» | «1» | «2» | «3» | «4» | «5» | «6» | «7» | «8» | «9»

  | _ | «{» | «}» | «[» | «]» | «#» | «(» | «)» | «<» | «>»
  | «%» | «:» | «;» | «.» | «?» | «*» | «+» | «-» | «/» | «^» | «&» | «|»
  | «~» | «!» | «=» | «,» | «\» | «"» | «'»

abbrev hexadecimal_digit := Fin 16

abbrev hex_quad :=
  hexadecimal_digit × hexadecimal_digit × hexadecimal_digit × hexadecimal_digit

inductive universal_character_name
  | u (low: hex_quad)
  | U (high low: hex_quad)

abbrev universal_character_name.allowed :=
  { ch: UCS // ∃ r: UCS.Range, lex.name.allowed r → ch ∈ r }

abbrev universal_character_name.allowed_initial :=
  { ch: universal_character_name.allowed // ∀ r: UCS.Range, lex.name.disallowed r → ch.val ∉ r }
-/
