/-!
# ISO/IEC 10646: Universal Coded Character Set (UCS)

See also [*Unicode and ISO 10646*](http://unicode.org/faq/unicode_iso.html).
-/

abbrev UCS := Nat

instance: Coe Char UCS where
  coe := Char.toNat

/-- Inclusive range of UCS. -/
structure UCS.Range where
  /-- Inclusive. -/
  first: UCS
  /-- Inclusive. -/
  last: UCS
  protected le: first ≤ last := by decide

instance: Membership UCS UCS.Range where
  mem ch r := r.first ≤ ch ∧ ch ≤ r.last

def UCS.Singleton (ch: UCS): Range where
  first := ch
  last := ch
  le := .refl

/-- https://timsong-cpp.github.io/cppwp/n4868/lex#tab:lex.name.allowed -/
inductive lex.name.allowed: UCS.Range → Type
  |  «00A8»      : allowed (UCS.Singleton 0x00A8)
  |  «00AA»      : allowed (UCS.Singleton 0x00AA)
  |  «00AD»      : allowed (UCS.Singleton 0x00AD)
  |  «00AF»      : allowed (UCS.Singleton 0x00AF)
  |  «00B2-00B5» : allowed {first := 0x00B2, last := 0x00B5}
  |  «00B7-00BA» : allowed {first := 0x00B7, last := 0x00BA}
  |  «00BC-00BE» : allowed {first := 0x00BC, last := 0x00BE}
  |  «00C0-00D6» : allowed {first := 0x00C0, last := 0x00D6}
  |  «00D8-00F6» : allowed {first := 0x00D8, last := 0x00F6}
  |  «00F8-00FF» : allowed {first := 0x00F8, last := 0x00FF}
  |  «0100-167F» : allowed {first := 0x0100, last := 0x167F}
  |  «1681-180D» : allowed {first := 0x1681, last := 0x180D}
  |  «180F-1FFF» : allowed {first := 0x180F, last := 0x1FFF}
  |  «200B-200D» : allowed {first := 0x200B, last := 0x200D}
  |  «202A-202E» : allowed {first := 0x202A, last := 0x202E}
  |  «203F-2040» : allowed {first := 0x203F, last := 0x2040}
  |  «2054»      : allowed (UCS.Singleton 0x2054)
  |  «2060-206F» : allowed {first := 0x2060, last := 0x206F}
  |  «2070-218F» : allowed {first := 0x2070, last := 0x218F}
  |  «2460-24FF» : allowed {first := 0x2460, last := 0x24FF}
  |  «2776-2793» : allowed {first := 0x2776, last := 0x2793}
  |  «2C00-2DFF» : allowed {first := 0x2C00, last := 0x2DFF}
  |  «2E80-2FFF» : allowed {first := 0x2E80, last := 0x2FFF}
  |  «3004-3007» : allowed {first := 0x3004, last := 0x3007}
  |  «3021-302F» : allowed {first := 0x3021, last := 0x302F}
  |  «3031-D7FF» : allowed {first := 0x3031, last := 0xD7FF}
  |  «F900-FD3D» : allowed {first := 0xF900, last := 0xFD3D}
  |  «FD40-FDCF» : allowed {first := 0xFD40, last := 0xFDCF}
  |  «FDF0-FE44» : allowed {first := 0xFDF0, last := 0xFE44}
  |  «FE47-FFFD» : allowed {first := 0xFE47, last := 0xFFFD}
  | «10000-1FFFD»: allowed {first := 0x10000, last := 0x1FFFD}
  | «20000-2FFFD»: allowed {first := 0x20000, last := 0x2FFFD}
  | «30000-3FFFD»: allowed {first := 0x30000, last := 0x3FFFD}
  | «40000-4FFFD»: allowed {first := 0x40000, last := 0x4FFFD}
  | «50000-5FFFD»: allowed {first := 0x50000, last := 0x5FFFD}
  | «60000-6FFFD»: allowed {first := 0x60000, last := 0x6FFFD}
  | «70000-7FFFD»: allowed {first := 0x70000, last := 0x7FFFD}
  | «80000-8FFFD»: allowed {first := 0x80000, last := 0x8FFFD}
  | «90000-9FFFD»: allowed {first := 0x90000, last := 0x9FFFD}
  | «A0000-AFFFD»: allowed {first := 0xA0000, last := 0xAFFFD}
  | «B0000-BFFFD»: allowed {first := 0xB0000, last := 0xBFFFD}
  | «C0000-CFFFD»: allowed {first := 0xC0000, last := 0xCFFFD}
  | «D0000-DFFFD»: allowed {first := 0xD0000, last := 0xDFFFD}
  | «E0000-EFFFD»: allowed {first := 0xE0000, last := 0xEFFFD}

/-- https://timsong-cpp.github.io/cppwp/n4868/lex#tab:lex.name.disallowed -/
inductive lex.name.disallowed: UCS.Range → Prop
  | «0300-036F»: disallowed {first := 0x0300, last := 0x036F}
  | «1DC0-1DFF»: disallowed {first := 0x1DC0, last := 0x1DFF}
  | «20D0-20FF»: disallowed {first := 0x20D0, last := 0x20FF}
  | «FE20-FE2F»: disallowed {first := 0xFE20, last := 0xFE2F}
