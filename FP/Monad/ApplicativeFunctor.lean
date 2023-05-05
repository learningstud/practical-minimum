set_option autoImplicit false

#check Alternative
#check Applicative
#check LawfulApplicative
#check Functor
#check LawfulFunctor
#check Monad
/-
@[inherit_doc HOrElse.hOrElse] syntax:20 term:21 " <|> " term:20 : term
@[inherit_doc HAndThen.hAndThen] syntax:60 term:61 " >> " term:60 : term
@[inherit_doc] infixl:55  " >>= " => Bind.bind
@[inherit_doc] notation:60 a:60 " <*> " b:61 => Seq.seq a fun _ : Unit => b
@[inherit_doc] notation:60 a:60 " <* " b:61 => SeqLeft.seqLeft a fun _ : Unit => b
@[inherit_doc] notation:60 a:60 " *> " b:61 => SeqRight.seqRight a fun _ : Unit => b
@[inherit_doc] infixr:100 " <$> " => Functor.map

macro_rules | `($x <|> $y) => `(binop_lazy% HOrElse.hOrElse $x $y)
macro_rules | `($x >> $y)  => `(binop_lazy% HAndThen.hAndThen $x $y)
-/
namespace Category
universe u v

/-- For `f: α → β`, `map f: F α → F β`, and `f <$> x ≡ map f x : F β` -/
class Functor (F: Type u → Type v) where
  /-- If `f: α → β` and `x: F α` then `f <$> x: F β`. -/
  map {α β}: (α → β) → F α → F β
  id_map {α} (x: F α): map id x = x
  comp_map {α β γ} (f: α → β) (g: β → γ) (x: F α): map (g ∘ f) x = map g (map f x)

namespace Functor
  @[inherit_doc] infixr:100 " <$> " => map
  variable {F: Type u → Type v} [self: Functor F] {α β: Type u}

  /-- The special case `(fun _ => b) <$> x`. -/
  def mapConst (b: β): F α → F β := map fun _ => b
  theorem map_const: (mapConst: β → F α → F β) = map ∘ (fun b _ => b) := rfl
end Functor

/--
An [applicative functor](https://en.wikipedia.org/wiki/Applicative_functor) is
an intermediate structure between `Functor` and `Monad`. It mainly consists of
two operations:

* `pure: α → F α`
* `seq: F (α → β) → F α → F β` (written as `<*>`)

The `seq` operator gives a notion of evaluation order to the effects, where
the first argument is executed before the second, but unlike a monad the results
of earlier computations cannot be used to define later actions.
-/
class Applicative (F: Type u → Type v) where
  pure {α}: α → F α
  /-- If `mf: F (α → β)` and `mx: F α`, then `mf <*> mx : F β`.
  In a monad this is the same as `do let f ← mf; x ← mx; pure (f x)`:
  it evaluates first the function, then the argument, and applies one to the other.

  To avoid surprising evaluation semantics, `mx` is taken "lazily", using a
  `Unit → f α` function. -/
  seq {α β}: F (α → β) → (Unit → F α) → F β

  id_map {α} (x : F α): (seq (pure id) fun _ => x) = x
  comp_map {α β γ} (f: α → β) (g: β → γ) (x: F α):
    (seq (pure (g ∘ f)) fun _ => x) = seq (pure g) fun _ => (seq (pure f) fun _ => x)
  -- comp_map g h x := (by
  --   repeat rw [← pure_seq]
  --   simp [seq_assoc, map_pure, seq_pure])

namespace Applicative
  @[inherit_doc] notation:60 a:60 " <*> " b:61 => seq a fun (_: Unit) => b
  variable {F: Type u → Type v} [self: Applicative F] {α β γ: Type u}

  instance toFunctor: Functor F where
    map x y := pure x <*> y
    id_map := id_map
    comp_map := comp_map
  
  theorem pure_seq (f: α → β) (x: F α): pure f <*> x = f <$> x := rfl
  theorem map_pure (f: α → β) (x: α): f <$> (pure x : F α) = pure (f x) := rfl
  theorem seq_pure (f: F (α → β)) (x: α): f <*> pure x = (. x) <$> f := rfl
  theorem seq_assoc (x: F α) (f: F (α → β)) (g: F (β → γ))
    : g <*> (f <*> x) = ((. ∘ .) <$> g) <*> f <*> x := rfl

  /-- If `x: F α` and `y: F β`, then `x <* y` evaluates `x`, then `y`,
  and returns the result of `x`. -/
  def seqLeft (x: F α): (Unit → F β) → F α := seq ((fun a _ => a) <$> x)
  @[inherit_doc] notation:60 a:60 " <* " b:61 => seqLeft a fun (_: Unit) => b
  -- seqLeft_eq {α β} (x: F α) (y: F β): x <* y = const β <$> x <*> y

  /-- If `x: F α` and `y: F β`, then `x *> y` evaluates `x`, then `y`,
  and returns the result of `y`. -/
  def seqRight (x: F α): (Unit → F β) → F β := seq ((fun _ b => b) <$> x)
  @[inherit_doc] notation:60 a:60 " *> " b:61 => seqRight a fun (_: Unit) => b
  -- seqRight_eq (x : f α) (y : f β)     : x *> y = const α id <$> x <*> y
  
end Applicative

end Category