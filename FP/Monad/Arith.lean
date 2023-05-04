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

def evaluateOption: Expr Binop → Option Int
  | .const value => value
  | .binop op left right =>
    evaluateOption left >>= fun x =>
    evaluateOption right >>= fun y =>
    applyOpOption x y op

def applyOpExcept (x y: Int): Binop → Except String Int
  | .add => .ok (x + y)
  | .sub => .ok (x - y)
  | .mul => .ok (x * y)
  | .div => if y = 0 then .error s!"Divide {x} by zero" else .ok (x / y)

def evaluateExcept: Expr Binop → Except String Int
  | .const value => .ok value
  | .binop op left right =>
    evaluateExcept left >>= fun x =>
    evaluateExcept right >>= fun y =>
    applyOpExcept x y op