# Lambda Calculus

## Capture-avoiding substitutions

Suppose `t`, `s` and `r` are lambda terms, and `x` and `y` are variables. The notation `t[x←r]` indicates substitution of `r` for `x` in `t` in a capture-avoiding manner. This is defined so that:
- `x[x←r] = r`
- `y[x←r] = y` if `x ≠ y`
- `(t s)[x←r] = (t[x←r]) (s[x←r])`
- `(x ↦ t)[x←r] = (x ↦ t)`
- `(y ↦ t)[x←r] = y ↦ t[x←r]` if `x ≠ y` and `y` does not appear among the free variables of `r` (`y` is said to be "fresh" for `r`); substituting a variable which is not bound by an abstraction proceeds in the abstraction's body, provided that the abstracted variable `y` is "fresh" for the substitution term `r`.
