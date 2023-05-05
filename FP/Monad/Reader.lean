set_option autoImplicit false

#check ReaderT
#check ReaderM

universe u v w
variable (ρ: Type u) (α: Type v) (β: Type w)
/-- `ρ` is conventionally used to denote the type of an environment. -/
def Reader := ρ → α
namespace Reader
  def read: Reader ρ ρ
    | env => env
  def pure (x: α): Reader ρ α
    | _ => x
  def bind (result: Reader ρ α) (next: α → Reader ρ β): Reader ρ β
    | env => next (result env) env
end Reader
instance: Monad (Reader ρ) where
  pure x _ := x
  bind result next env := next (result env) env