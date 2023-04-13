/-
https://timsong-cpp.github.io/cppwp/n4868/basic
-/
import cpp.lex
import cpp.over
set_option autoImplicit false

/-- https://timsong-cpp.github.io/cppwp/n4868/basic#pre-3 -/
inductive entity
  | value
  | object
  | reference
  | structured_binding
  | function
  | enumerator
  | type
  | class_member
  | «bit-field»
  | template
  | template_specialization
  | namespace
  | pack

/-- https://timsong-cpp.github.io/cppwp/n4868/basic#pre-4 -/
inductive name
  /-- [lex.name](https://timsong-cpp.github.io/cppwp/n4868/lex.name) -/
  | id (id: identifier)
  /-- [over.oper](https://timsong-cpp.github.io/cppwp/n4868/over.oper) -/
  | ofid (ofid: «operator-function-id»)
  /-- [over.literal](https://timsong-cpp.github.io/cppwp/n4868/over.literal) -/
  | «literal-operator-id»
  /-- [class.conv.fct](https://timsong-cpp.github.io/cppwp/n4868/class.conv.fct) -/
  | «conversion-function-id»
  /-- [temp.names](https://timsong-cpp.github.io/cppwp/n4868/temp.names) -/
  | «template-id»