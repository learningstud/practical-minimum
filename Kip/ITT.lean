/-!
```
structure T where
  mk ::
  a: α
  [b: β]
  {c: γ}

-- is the same as:

inductive T
  | mk (a: α) [b: β] {c: γ}
def T.a (t: T): α := let { a, .. } := t ; a
def T.b (t: T): β := let { b, .. } := t ; b
def T.c (t: T): γ := let { c, .. } := t ; c
```
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

class Variable (Var: Type)
class Universe (𝒰: Type) where
  enlarge: 𝒰 → 𝒰
  join: 𝒰 → 𝒰 → 𝒰

class ITT (Var 𝒰: Type) [Variable Var] [Universe 𝒰]
namespace ITT

variable {Var 𝒰: Type} [Variable Var] [Universe 𝒰]
inductive Term [ITT Var 𝒰]
  | variable (x: Var)
  | universe (u: 𝒰)
  | arrow (binder: Var) (domain predicate: Term)
  | application (function argument: Term)
  | substitution (term: Term) (var: Var) (replacement: Term)

variable [tt: ITT Var 𝒰]
abbrev Context := List (Var × tt.Term)

mutual
  /-- Γ ⊢ -/
  inductive JCtx: tt.Context → Type
    | empty
      : JCtx .nil -- ⊢
    | extension {Γ: Context} {A: Term}
      : JTerm Γ A (.universe _) -- Γ ⊢ A : 𝒰
      → (x: Var) -- x
      → (∀ t: Term, (x, t) ∉ Γ) -- x ∉ Γ
      → JCtx ((x, A) :: Γ) -- Γ, x: A ⊢

  /-- Γ ⊢ a : A -/
  inductive JTerm: tt.Context → tt.Term → tt.Term → Type
    | variable {Γ: Context} {A: Term}
      : JCtx Γ -- Γ ⊢
      → (x: Var) -- x
      → (x, A) ∈ Γ -- (x: A) ∈ Γ
      → JTerm Γ (.variable x) A -- Γ ⊢ x : A
    | universe {Γ: Context}
      : JCtx Γ -- Γ ⊢
      → (U: 𝒰) -- 𝒰
      → JTerm Γ (.universe U) (.universe (Universe.enlarge U)) -- Γ ⊢ 𝒰 : 𝒰₊
    | abstraction {Γ: Context} {x: Var} {b A B: Term}
      : JTerm ((x, A) :: Γ) b B -- Γ, x: A ⊢ b : B
      → JTerm Γ (.arrow x A b) (.arrow x A B) -- Γ ⊢ λ x, b : Π (x: A), B
    | product {Γ: Context} {x: Var} {A B: Term} {U V: 𝒰}
      : JTerm Γ A (.universe U) -- Γ ⊢ A : 𝒰
      → JTerm ((x, A) :: Γ) B (.universe V) -- Γ, x: A ⊢ B : 𝒱
      → JTerm Γ (.arrow x A B) (.universe (Universe.join U V)) -- Γ ⊢ Π (x: A), B : 𝒰 ⊔ 𝒱
    | application {Γ: Context} {x: Var} {f a A B: Term}
      : JTerm Γ f (.arrow x A B) -- Γ ⊢ f : Π (x: A), B
      → JTerm Γ a A -- Γ ⊢ a : A
      → JTerm Γ (.application f a) (.substitution B x a) -- Γ ⊢ f a : B (x := a)
    -- | congruence {Γ: Context} {a A B: Term}
      -- : JTerm Γ a A -- Γ ⊢ a : A
      -- → JEq Γ A B (.universe _) -- Γ ⊢ A ≡ B : 𝒰
      -- → JTerm Γ a B -- Γ ⊢ a : B

    /-- Γ ⊢ a ≡ b : A -/
    inductive JEq: tt.Context → tt.Term → tt.Term → tt.Term → Type
      | refl {Γ: Context} {a A: Term}
        : JTerm Γ a A -- Γ ⊢ a : A
        → JEq Γ a a A -- Γ ⊢ a ≡ a : A
      -- | symm {Γ: Context} {a b A: Term}
      --   : JEq Γ a b A -- Γ ⊢ a ≡ b : A
      --   → JEq Γ b a A -- Γ ⊢ b ≡ a : A
      -- | trans {Γ: Context} {a b c A: Term}
      --   : JEq Γ a b A -- Γ ⊢ a ≡ b : A
      --   → JEq Γ b c A -- Γ ⊢ b ≡ c : A
      --   → JEq Γ a c A -- Γ ⊢ a ≡ c : A
      -- | congr {Γ: Context} {a b A B: Term}
      --   : JEq Γ a b A -- Γ ⊢ a ≡ b : A
      --   → JEq Γ A B (.universe _) -- Γ ⊢ A ≡ B : 𝒰
      --   → JEq Γ a b B -- Γ ⊢ a ≡ b : B
      | alpha {Γ: Context} {x: Var} {b b' A B: Term}
        : JTerm Γ A (.universe _) -- Γ ⊢ A : 𝒰
        → JTerm ((x, A) :: Γ) b B -- Γ, x: A ⊢ b : B
        → JEq ((x, A) :: Γ) b b' B -- Γ, x: A ⊢ b ≡ b' : B
        → JEq Γ (.arrow x A b) (.arrow x A b') (.arrow x A B) -- Γ ⊢ λ x, b ≡ λ x, b' : Π (x: A), B
      | beta {Γ: Context} {x: Var} {a b A B: Term}
        : JTerm ((x, A) :: Γ) b B -- Γ, x: A ⊢ b, B
        → JTerm Γ a A -- Γ ⊢ a : A
        → JEq Γ (.application (.arrow x A b) a) (.substitution b x a) (.substitution B x a) -- Γ ⊢ (λ x, b) a ≡ b (x := a) : B (x := a)
      | eta {Γ: Context} {x: Var} {f A B: Term}
        : JTerm Γ f (.arrow x A B) -- Γ ⊢ f : Π (x: A), B
        → JEq Γ f (.arrow x A (.application f (.variable x))) (.arrow x A B) -- Γ ⊢ f ≡ λ x, f x : Π (x: A), B
end

namespace JCtx

  section
    variable {Γ: tt.Context}
    def context (_: JCtx Γ) := Γ
  end

  theorem ctx_ok {Γ: tt.Context}: JCtx Γ → JCtx Γ :=
    id

end JCtx

namespace JTerm

  section
    variable {Γ: tt.Context} {a A: tt.Term}
    def context (_: JTerm Γ a A) := Γ
    def term    (_: JTerm Γ a A) := a
    def type    (_: JTerm Γ a A) := A
  end

  theorem ctx_ok {Γ: tt.Context} {a A: Term}: JTerm Γ a A → JCtx Γ
    | .variable jctx _ _
    | .universe jctx _ => jctx
    | .abstraction jterm => let .extension j _ _ := ctx_ok jterm ; ctx_ok j
    | .product jterm _
    | .application _ jterm => ctx_ok jterm

end JTerm

namespace JEq

  section
    variable {Γ: tt.Context} {a b A: tt.Term}
    def context (_: JEq Γ a b A) := Γ
    def left    (_: JEq Γ a b A) := a
    def right   (_: JEq Γ a b A) := b
    def type    (_: JEq Γ a b A) := A
  end

  theorem ctx_ok {Γ: tt.Context} {a b A: Term}: JEq Γ a b A → JCtx Γ
    | .refl jterm
    | .alpha jterm _ _
    | .beta _ jterm
    | .eta jterm => JTerm.ctx_ok jterm

end JEq

end ITT
