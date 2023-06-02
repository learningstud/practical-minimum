set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Untyped
  abbrev Variable: Type := String
  inductive Term
    | variable (x: Variable)
    | abstraction (binder: Variable) (predicate: Term)
    | application (function argument: Term)
    -- | substitution (binder: Variable) (predicate replacement: Term) --(reduct: Thunk Term)
  abbrev Context := List Variable
  inductive JCtx: Context → Type
    | empty
      : JCtx .nil
    | extend {Γ: Context}
      : JCtx Γ → (x: Variable) → x ∉ Γ → JCtx (x :: Γ)
  inductive JTerm: Context → Term → Type
    | variable {Γ: Context}
      : JCtx Γ → (x: Variable) → x ∈ Γ → JTerm Γ (.variable x)
    | abstraction {Γ: Context} {x: Variable} {a: Term}
      : JTerm (x :: Γ) a → JTerm Γ (.abstraction x a)
    | application {Γ: Context} {f a: Term}
      : JTerm Γ f → JTerm Γ a → JTerm Γ (.application f a)
  inductive JEq: Context → Term → Term → Type
    | refl {Γ: Context} {a: Term}
      : JTerm Γ a → JEq Γ a a
    | alpha {Γ: Context} {x: Variable} {a b: Term}
      : JTerm (x :: Γ) a → JEq Γ a b → JEq Γ (.abstraction x a) (.abstraction x b)
    -- | beta {Γ: Context} {x: Variable} {a b: Term}
    --   : JTerm (x :: Γ) a → JEq Γ (.application (.abstraction x a) b) (.substitution x a b)
    | eta {Γ: Context} {x: Variable} {f: Term}
      : JTerm Γ f → JEq Γ f (.abstraction x (.application f (.variable x)))
end Untyped

namespace Typed
  abbrev Variable := String
  inductive Term
    | variable (x: Variable)
    | abstraction (binder: Variable) (predicate: Term)
    | application (function argument: Term)
    | product (binder: Variable) (domain predicate: Term)
    -- | substitution (binder: Variable) (predicate replacement: Term) --(reduct: Thunk Term)
  abbrev Context := List (Variable × Term)
  inductive JType: Context → Term → Type
    | product {Γ: Context} {x: Variable} {A B: Term}
      : JType Γ A → JType ((x, A) :: Γ) B → JType Γ (.product x A B)
end Typed

namespace Typed2
  abbrev Variable := String
  inductive Term
    | variable (x: Variable)
    | abstraction (binder: Variable) (predicate: Term)
    | application (function argument: Term)
    | product (binder: Variable) (domain predicate: Term)
    -- | substitution (binder: Variable) (predicate replacement: Term) --(reduct: Thunk Term)
  abbrev Context := List (Variable × Term)
  inductive JType: Context → Term → Type
    | product {Γ: Context} {x: Variable} {A B: Term}
      : JType Γ A → JType ((x, A) :: Γ) B → JType Γ (.product x A B)
end Typed2

namespace CTT
  abbrev Variable := String

  inductive IntervalTerm
    | zero -- bottom
    | one -- top
    | involution (i: IntervalTerm)
    | join (i j: IntervalTerm) -- sup
    | meet (i j: IntervalTerm) -- inf
    | variable (i: Variable)

  inductive FaceTerm
    | constraint (i: Variable) (name: IntervalTerm)
    | disjunction (φ ψ: FaceTerm)
    | conjunction (φ ψ: FaceTerm)
  
  inductive GlueTerm
    | Glue
    | glue
    | unglue
  
  mutual
    inductive Term
      | product (t: ProductTerm)
      | path (t: PathTerm)
    inductive ProductTerm
      | variable (x: Variable)
      | abstraction (binder: Variable) (predicate: Term)
      | application (function argument: Term)
      | product (binder: Variable) (domain predicate: Term)
    inductive PathTerm
      | abstraction (binder: Variable) (predicate: Term)
      | application (function: Term) (argument: IntervalTerm)
      | path (space startPoint endPoint: Term)
    inductive CompositionTerm
      | composition (i: Variable)
  end

  abbrev SystemTerm := List (FaceTerm × Term)

  inductive Assumption
    | term (x: Variable) (type: Term)
    | interval (i: IntervalTerm)
    | face (φ: FaceTerm)
    | system (b: SystemTerm)
  
  abbrev Context := List Assumption
end CTT
