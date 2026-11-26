/-!
# MiniC abstract syntax

This file describes the *shape* of MiniC programs.  It contains no parser and
no execution logic: a value of type `Stmt` is simply a syntax tree that later
modules can interpret concretely or symbolically.

`namespace MiniSym` qualifies the declarations below.  Thus the full name of
`Expr` is `MiniSym.Expr`; after writing `open MiniSym`, the shorter name is
usually available.  Namespaces prevent this project's common names (`Expr`,
`State`, and so on) from colliding with declarations in other libraries.
-/
namespace MiniSym

/-- Arithmetic-expression syntax.

An `inductive` declaration introduces a new datatype by listing every way to
construct a value of that type.  For example, `.int 3` is an `Expr`, while
`.add (.var "x") (.int 1)` is the tree for `x + 1`.  Because subexpressions are
again `Expr`s, `add` and `sub` make this datatype recursive.

These expressions describe mathematical integers, not fixed-width C machine
integers: there is no overflow in this model. -/
inductive Expr where
  | int : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  deriving Repr, DecidableEq

/-- Boolean-expression syntax used for guards, assertions, and path formulas.

This is deliberately an explicit syntax tree rather than a Lean proposition
(`Prop`) or a computed Boolean (`Bool`).  Keeping syntax as data lets both the
concrete evaluator and the symbolic executor inspect the same condition. -/
inductive BoolExpr where
  | eq : Expr → Expr → BoolExpr
  | lt : Expr → Expr → BoolExpr
  | le : Expr → Expr → BoolExpr
  | not : BoolExpr → BoolExpr
  | and : BoolExpr → BoolExpr → BoolExpr
  | or : BoolExpr → BoolExpr → BoolExpr
  deriving Repr, DecidableEq

/-- Statement syntax for the small imperative language.

`seq first second` is sequential composition, and `ite` means
"if-then-else."  Loops have no bound in the syntax; the concrete and symbolic
evaluators receive fuel separately, which makes their execution total. -/
inductive Stmt where
  | skip : Stmt
  | assign : String → Expr → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite : BoolExpr → Stmt → Stmt → Stmt
  | while : BoolExpr → Stmt → Stmt
  | assert : BoolExpr → Stmt
  deriving Repr, DecidableEq

/- `deriving Repr, DecidableEq` asks Lean to generate two routine operations
for each syntax datatype. `Repr` produces debugging output (not polished source
code), and `DecidableEq` gives an executable equality test.  Neither changes
the language semantics. -/

/-- Default loop-unrolling/execution bound used by convenience APIs.

Callers that care about the precise bound should use the fuel-explicit APIs
instead.  This constant is only a convenient default, not a proof assumption. -/
def defaultLoopFuel : Nat := 8

end MiniSym
