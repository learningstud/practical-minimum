set_option autoImplicit false

inductive Expr.{u} (Op: Type u)
  | const (value: Int)
  | binop (op: Op) (left right: Expr Op)

inductive Binop | add | sub | mul | div

def applyOpOption (x y: Int): Binop → Option Int
  | .add => x + y
  | .sub => x - y
  | .mul => x * y
  | .div => if y = 0 then none else x / y

def applyOpExcept (x y: Int): Binop → Except String Int
  | .add => .ok (x + y)
  | .sub => .ok (x - y)
  | .mul => .ok (x * y)
  | .div => if y = 0 then .error s!"Divide {x} by zero" else .ok (x / y)

def evaluateM {m} [Monad m] (applyOp: Int → Int → Binop → m Int): Expr Binop → m Int
  | .const value => pure value
  | .binop op left right =>
    evaluateM applyOp left >>= fun x =>
    evaluateM applyOp right >>= fun y =>
    applyOp x y op

def evaluateOption: Expr Binop → Option Int := evaluateM applyOpOption
def evaluateExcept: Expr Binop → Except String Int := evaluateM applyOpExcept
