set_option autoImplicit false

inductive Expr.{u} (Op: Type u)
  | const (value: Int)
  | binop (op: Op) (left right: Expr Op)

inductive Binop | add | sub | mul | div

def evaluateOption: Expr Binop → Option Int
  | .const value => value
  | .binop op left right =>
    evaluateOption left >>= fun x =>
    evaluateOption right >>= fun y =>
    match op with
    | .add => x + y
    | .sub => x - y
    | .mul => x * y
    | .div => if y = 0 then none else x / y
