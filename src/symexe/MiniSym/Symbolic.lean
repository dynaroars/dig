import MiniSym.Syntax

namespace MiniSym

/--
An arithmetic expression manipulated by the symbolic executor.

Unlike an `Int`, a `SymExpr` need not have a value yet.  For example,
`(.add (.input "x") (.int 1))` records the expression `input_x + 1` without
choosing a value for `input_x`.  This is an *explicit syntax tree* (AST): the
constructors are data that programs can inspect, print, or later translate to
SMT-LIB.

`input` names the unknown value a program variable had initially.  Assignments
do not introduce new input symbols; instead, the symbolic store records an
expression in terms of these initial symbols.
-/
inductive SymExpr where
  | int : Int → SymExpr
  | input : String → SymExpr
  | add : SymExpr → SymExpr → SymExpr
  | sub : SymExpr → SymExpr → SymExpr
  deriving Repr, DecidableEq

/--
Boolean formulas produced while following symbolic paths.

This type is deliberately separate from Lean's `Prop`.  A `Prop` is used by
Lean's logic and proof checker, whereas a `SymBool` is ordinary inspectable
data.  Keeping formulas as an AST lets us print them, retain them as path
conditions, and eventually translate them to an external solver.  We recover
a concrete truth value with `interpretBool` below.
-/
inductive SymBool where
  | true : SymBool
  | false : SymBool
  | eq : SymExpr → SymExpr → SymBool
  | lt : SymExpr → SymExpr → SymBool
  | le : SymExpr → SymExpr → SymBool
  | not : SymBool → SymBool
  | and : SymBool → SymBool → SymBool
  | or : SymBool → SymBool → SymBool
  deriving Repr, DecidableEq

/--
A valuation chooses a concrete integer for every named symbolic input.

It is the bridge between a symbolic execution and one particular concrete
execution.  For example, a valuation with `valuation "x" = 4` interprets
`.input "x"` as `4`.  The function is total, so every string has a value.
-/
abbrev Valuation := String → Int

/-- Evaluate a symbolic arithmetic AST after its inputs have been chosen. -/
def interpretExpr (valuation : Valuation) : SymExpr → Int
  | .int n => n
  | .input name => valuation name
  | .add lhs rhs => interpretExpr valuation lhs + interpretExpr valuation rhs
  | .sub lhs rhs => interpretExpr valuation lhs - interpretExpr valuation rhs

/--
Evaluate a symbolic formula under a valuation.

The result is a computable `Bool`, rather than a proposition.  `decide`
converts Lean's decidable integer comparisons into Boolean values.
-/
def interpretBool (valuation : Valuation) : SymBool → Bool
  | .true => true
  | .false => false
  | .eq lhs rhs => decide (interpretExpr valuation lhs = interpretExpr valuation rhs)
  | .lt lhs rhs => decide (interpretExpr valuation lhs < interpretExpr valuation rhs)
  | .le lhs rhs => decide (interpretExpr valuation lhs ≤ interpretExpr valuation rhs)
  | .not formula => !(interpretBool valuation formula)
  | .and lhs rhs => interpretBool valuation lhs && interpretBool valuation rhs
  | .or lhs rhs => interpretBool valuation lhs || interpretBool valuation rhs

/--
A symbolic store maps each current program variable to an expression over the
initial inputs.

For example, after `x = input + 1`, looking up `"x"` returns an addition AST.
A function is used instead of a finite map because lookup and proofs are very
simple.  `snapshotStore` below provides a finite view for printing.
-/
abbrev SymStore := String → SymExpr

/-- Initially, each program variable denotes the symbolic input of that name. -/
def initialStore : SymStore := SymExpr.input

/--
Functional store update: the assigned name gets `value`, while all other
names retain their old symbolic expressions.
-/
def updateStore (store : SymStore) (name : String) (value : SymExpr) : SymStore :=
  fun queried => if queried = name then value else store queried

/-- Looking up a name immediately after assigning it returns the new value. -/
@[simp] theorem updateStore_same (store : SymStore) (name : String) (value : SymExpr) :
    updateStore store name value name = value := by
  simp [updateStore]

/-- Assigning one name does not change the value stored under a different name. -/
@[simp] theorem updateStore_of_ne (store : SymStore) (name queried : String)
    (h : queried ≠ name) :
    updateStore store name value queried = store queried := by
  simp [updateStore, h]

/--
Everything needed to describe one point in symbolic execution.

`store` describes current program-variable values.  `pc` is the *path
condition*: the accumulated assumptions under which execution reaches this
state.  A branch extends `pc` with its guard or the negation of its guard.
-/
structure SymState where
  store : SymStore
  pc : SymBool

/-- The standard starting state has symbolic inputs and no path restriction. -/
def initialSymState : SymState := ⟨initialStore, .true⟩

/--
Symbolically evaluate a source-language arithmetic expression.

Variable occurrences are replaced by their current symbolic-store entries;
operators merely build new symbolic AST nodes.  No algebraic simplification is
required, so `(input + 1) + 2` may remain syntactically nested.
-/
def symEvalExpr (store : SymStore) : Expr → SymExpr
  | .int n => .int n
  | .var name => store name
  | .add lhs rhs => .add (symEvalExpr store lhs) (symEvalExpr store rhs)
  | .sub lhs rhs => .sub (symEvalExpr store lhs) (symEvalExpr store rhs)

/-- Symbolically evaluate a source Boolean expression using the current store. -/
def symEvalBool (store : SymStore) : BoolExpr → SymBool
  | .eq lhs rhs => .eq (symEvalExpr store lhs) (symEvalExpr store rhs)
  | .lt lhs rhs => .lt (symEvalExpr store lhs) (symEvalExpr store rhs)
  | .le lhs rhs => .le (symEvalExpr store lhs) (symEvalExpr store rhs)
  | .not formula => .not (symEvalBool store formula)
  | .and lhs rhs => .and (symEvalBool store lhs) (symEvalBool store rhs)
  | .or lhs rhs => .or (symEvalBool store lhs) (symEvalBool store rhs)

/--
Make a finite, readable view of a functional store for `#eval` examples.

Because a function `String → SymExpr` cannot be exhaustively printed, callers
choose the variable names of interest.  This changes presentation only; it is
not involved in execution or the soundness proofs.
-/
def snapshotStore (names : List String) (store : SymStore) : List (String × SymExpr) :=
  names.map fun name => (name, store name)

/-- Printable data corresponding to the selected part of a symbolic state. -/
structure SymStateSnapshot where
  store : List (String × SymExpr)
  pc : SymBool
  deriving Repr, DecidableEq

/-- Capture selected store bindings together with the complete path condition. -/
def SymState.snapshot (state : SymState) (names : List String) : SymStateSnapshot :=
  ⟨snapshotStore names state.store, state.pc⟩

end MiniSym
