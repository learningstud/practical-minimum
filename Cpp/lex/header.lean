/- [lex.header](https://timsong-cpp.github.io/cppwp/n4868/lex#header) -/
import Cpp.lex.charset
set_option autoImplicit false

open basic_source_character_set in
abbrev h_char := { ch: basic_source_character_set // ch ≠ new_line ∧ ch ≠ «>» }

open basic_source_character_set in
abbrev q_char := { ch: basic_source_character_set // ch ≠ new_line ∧ ch ≠ «"» }

inductive header_name
  | h (q_char_sequence: List h_char)
  | q (h_char_sequence: List q_char)
