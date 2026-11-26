import MiniSym.SymExec
import Lean.Elab.Tactic.Omega

namespace MiniSym.Examples

/-!
# Executable examples

Definitions in this file build programs directly as Lean AST values. `#eval`
runs code while compiling the file and prints its result. `#guard` is a checked
regression: compilation fails if its Boolean condition evaluates to false.

These examples are a useful bridge between reading the datatypes and reading the
proofs. Change a program or fuel value, run `lake build MiniSym.Examples`, and
inspect the resulting path conditions.
-/

open MiniSym

def input (name : String) : Expr := .var name
def gt (left right : Expr) : BoolExpr := .lt right left
def ne (left right : Expr) : BoolExpr := .not (.eq left right)
-- MiniC has no dedicated `>` or `!=` constructors; these helpers demonstrate
-- that they are derived forms rather than additional semantic cases.

/-- `x = input + 1; y = x + 2`. Here `input` is a program input name. -/
def straightLine : Stmt :=
  .seq (.assign "x" (.add (input "input") (.int 1)))
       (.assign "y" (.add (input "x") (.int 2)))

def straightLineResults : List SymResultSnapshot :=
  snapshotResults ["x", "y"] (symExec straightLine initialSymState)

#eval straightLineResults

#guard straightLineResults.length == 1

/-- Two paths, guarded respectively by `input < 10` and its negation. -/
def conditional : Stmt :=
  .seq (.assign "x" (input "input"))
    (.ite (.lt (input "x") (.int 10))
      (.assign "y" (.add (input "x") (.int 1)))
      (.assign "y" (.sub (input "x") (.int 1))))

#eval snapshotResults ["x", "y"] (symExec conditional initialSymState)

#guard (symExec conditional initialSymState).length == 2

/-- Includes the deliberately infeasible path `input > 10 ∧ input < 5`. -/
def nestedConditional : Stmt :=
  .seq (.assign "x" (input "input"))
    (.ite (gt (input "x") (.int 10))
      (.ite (.lt (input "x") (.int 5))
        (.assign "y" (.int 1))
        (.assign "y" (.int 2)))
      .skip)

#eval snapshotResults ["x", "y"] (symExec nestedConditional initialSymState)

#guard (symExec nestedConditional initialSymState).length == 3

/-- Lean can certify the arithmetic contradiction independently of execution. -/
theorem greaterTenAndLessFive_infeasible (x : Int)
    (hGreater : 10 < x) (hLess : x < 5) : False := by
  omega

/-- Assertion execution exposes normal and failure results on every control path. -/
def assertionProgram : Stmt :=
  .seq (.assign "x" (input "input"))
    (.seq
      (.ite (gt (input "x") (.int 0))
        (.assign "y" (.add (input "x") (.int 1)))
        (.assign "y" (.sub (input "x") (.int 1))))
      (.assert (ne (input "y") (.int 0))))

#eval snapshotResults ["x", "y"] (symExec assertionProgram initialSymState)

def isAssertionFailure : SymResult → Bool
  | .normal _ => false
  | .assertionFailure _ => true
  | .fuelExhausted _ => false

-- Both control-flow paths expose one safe and one failing assertion outcome.
#guard (symExec assertionProgram initialSymState).length == 4
#guard ((symExec assertionProgram initialSymState).filter isAssertionFailure).length == 2

/-- A bounded loop. At bound three, symbolic execution exposes four exit points
and one path that requires a fourth iteration. -/
def loopProgram : Stmt :=
  .seq (.assign "x" (.int 0))
    (.while (.lt (.var "x") (.int 3))
      (.assign "x" (.add (.var "x") (.int 1))))

#eval snapshotResults ["x"] (symExecFuel 3 loopProgram initialSymState)
#guard (symExecFuel 3 loopProgram initialSymState).length == 5

end MiniSym.Examples
