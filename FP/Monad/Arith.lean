set_option autoImplicit false

inductive Expr.{u} (Op: Type u)
  | const (value: Int)
  | binop (op: Op) (left right: Expr Op)

inductive Binop | add | sub | mul | div

def applyDivOption (x y: Int): Option Int :=
  if y = 0 then none else x / y

def applyDivExcept (x y: Int): Except String Int :=
  if y = 0 then .error s!"Divide {x} by zero" else .ok (x / y)

def applyOp {m} [Monad m] (applyDiv: Int → Int → m Int) (x y: Int): Binop → m Int
  | .add => pure (x + y)
  | .sub => pure (x - y)
  | .mul => pure (x * y)
  | .div => applyDiv x y

def evaluateM {m} [Monad m] (applyDiv: Int → Int → m Int): Expr Binop → m Int
  | .const value => pure value
  | .binop op left right =>
    evaluateM applyDiv left >>= fun x =>
    evaluateM applyDiv right >>= fun y =>
    applyOp applyDiv x y op

def evaluateOption: Expr Binop → Option Int := evaluateM applyDivOption
def evaluateExcept: Expr Binop → Except String Int := evaluateM applyDivExcept
