set_option autoImplicit false

inductive Expr.{u} (Op: Type u)
  | const (value: Int)
  | binop (op: Op) (left right: Expr Op)

inductive Binop.{u} (FallibleOp: Type u)
  | add | sub | mul
  | fallible (op: FallibleOp)

inductive FallibleOp
  | div

def applyFallibleOption (x y: Int): FallibleOp → Option Int
  | .div => if y = 0 then none else x / y

def applyFallibleExcept (x y: Int): FallibleOp → Except String Int
  | .div => if y = 0 then .error s!"Divide {x} by zero" else .ok (x / y)

def applyOp {m} [Monad m] (applyFallible: Int → Int → FallibleOp → m Int) (x y: Int)
  : Binop FallibleOp → m Int
  | .add => pure (x + y)
  | .sub => pure (x - y)
  | .mul => pure (x * y)
  | .fallible op => applyFallible x y op

def evaluateM {m} [Monad m] (applyFallible: Int → Int → FallibleOp → m Int)
  : Expr (Binop FallibleOp) → m Int
  | .const value => pure value
  | .binop op left right =>
    evaluateM applyFallible left >>= fun x =>
    evaluateM applyFallible right >>= fun y =>
    applyOp applyFallible x y op

def evaluateOption: Expr (Binop FallibleOp) → Option Int :=
  evaluateM applyFallibleOption
def evaluateExcept: Expr (Binop FallibleOp) → Except String Int :=
  evaluateM applyFallibleExcept
