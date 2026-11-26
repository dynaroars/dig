import MiniSym.Syntax
import Lean.Elab.Tactic.Omega

/-!
# Concrete semantics

This module gives MiniC programs an executable meaning.  A concrete state
assigns an integer to every variable, expression evaluators compute values,
and `execFuel` executes statements.  Later soundness proofs compare this
reference behavior with symbolic execution.
-/
namespace MiniSym

/-- A concrete store maps every program-variable name to an integer.

`abbrev` is a transparent type abbreviation, so a `State` is just a function
`String → Int`.  Looking up `x` is ordinary function application: `state "x"`.
There is consequently no missing-variable case; an initial store supplies a
value for every string, including variables that have not yet been assigned.
This functional representation is especially convenient in proofs. -/
abbrev State := String → Int

/-- Return a new store in which `name` has `value`.

States are immutable.  This operation creates a function that returns the new
value when queried at `name` and delegates every other lookup to the old store.
The equality test is executable because strings have decidable equality. -/
def State.update (state : State) (name : String) (value : Int) : State :=
  fun queried => if queried = name then value else state queried

/-- Looking up the variable just updated returns its new value.

The `@[simp]` attribute registers this theorem with Lean's simplifier, so later
proofs can reduce such lookups automatically. -/
@[simp] theorem State.update_same (state : State) (name : String) (value : Int) :
    state.update name value name = value := by
  simp [State.update]

/-- Updating one variable leaves every differently named variable unchanged.

The hypothesis `h` is a Lean proposition (`Prop`) used as proof evidence; it
is distinct from a runtime `Bool`. -/
@[simp] theorem State.update_of_ne (state : State) (name queried : String)
    (h : queried ≠ name) :
    state.update name value queried = state queried := by
  simp [State.update, h]

/-- Evaluate an arithmetic syntax tree in a concrete store.

The equations after `|` are pattern-matching cases, one for each `Expr`
constructor.  Recursive calls evaluate child trees before Lean's integer
addition or subtraction is applied. -/
def evalExpr (state : State) : Expr → Int
  | .int value => value
  | .var name => state name
  | .add lhs rhs => evalExpr state lhs + evalExpr state rhs
  | .sub lhs rhs => evalExpr state lhs - evalExpr state rhs

/-- Evaluate a Boolean-expression syntax tree to an executable `Bool`.

Lean distinguishes `Bool` (data, with values `true` and `false`) from `Prop`
(logical statements used in proofs).  Integer comparisons naturally form
propositions, so `decide` computes their Boolean answer.  The remaining cases
use Boolean negation, conjunction, and disjunction directly. -/
def evalBool (state : State) : BoolExpr → Bool
  | .eq lhs rhs => decide (evalExpr state lhs = evalExpr state rhs)
  | .lt lhs rhs => decide (evalExpr state lhs < evalExpr state rhs)
  | .le lhs rhs => decide (evalExpr state lhs ≤ evalExpr state rhs)
  | .not condition => !(evalBool state condition)
  | .and lhs rhs => evalBool state lhs && evalBool state rhs
  | .or lhs rhs => evalBool state lhs || evalBool state rhs

/-- The three observable ways bounded concrete execution can finish.

Each constructor retains the store at the stopping point.  Keeping assertion
failure separate from fuel exhaustion matters: the former is program behavior,
whereas the latter says only that this bounded run could not finish exploring
the loop. -/
inductive ExecResult where
  | normal : State → ExecResult
  | assertionFailure : State → ExecResult
  | fuelExhausted : State → ExecResult

/-- A structural size used only to convince Lean that `execFuel` terminates.

`private` keeps this proof-engineering helper out of the public API.  It is not
an execution cost model and has no observable semantic role. -/
private def stmtSize : Stmt → Nat
  | .skip | .assign _ _ | .assert _ => 1
  | .seq first second | .ite _ first second =>
      stmtSize first + stmtSize second + 1
  | .while _ body => stmtSize body + 1

/-- Total, deterministic, fuel-bounded evaluator for MiniC.

Assertion failure is terminal: in a sequence, the second statement is not
executed after the first statement fails. Fuel exhaustion is likewise terminal.
Fuel is consumed only when a true `while` guard begins an iteration; the body
runs at the current bound and the next guard is checked with one less unit.

The definition pattern-matches on both the statement and intermediate results.
Notice that a false loop guard succeeds even with zero fuel: fuel limits
iterations, not guard checks.  When a body finishes normally, execution checks
the loop again; either terminal result is propagated without continuing. -/
def execFuel : Nat → Stmt → State → ExecResult
  | _, .skip, state => .normal state
  | _, .assign name expression, state =>
      .normal (state.update name (evalExpr state expression))
  | fuel, .seq first second, state =>
      match execFuel fuel first state with
      | .normal next => execFuel fuel second next
      | .assertionFailure failed => .assertionFailure failed
      | .fuelExhausted stopped => .fuelExhausted stopped
  | fuel, .ite condition thenBranch elseBranch, state =>
      if evalBool state condition then
        execFuel fuel thenBranch state
      else
        execFuel fuel elseBranch state
  | fuel, .while condition body, state =>
      if evalBool state condition then
        match fuel with
        | 0 => .fuelExhausted state
        | remaining + 1 =>
            match execFuel (remaining + 1) body state with
            | .normal next => execFuel remaining (.while condition body) next
            | .assertionFailure failed => .assertionFailure failed
            | .fuelExhausted stopped => .fuelExhausted stopped
      else
        .normal state
  | _, .assert condition, state =>
      if evalBool state condition then
        .normal state
      else
        .assertionFailure state
termination_by fuel statement _ => fuel + stmtSize statement
decreasing_by
  -- Recursive calls either enter a syntactic substatement or consume one unit
  -- of loop fuel. `simp_wf`, unfolding `stmtSize`, and linear arithmetic via
  -- `omega` discharge the resulting natural-number decrease obligations.
  all_goals simp_wf
  all_goals simp [stmtSize]
  all_goals omega

/-- Concrete execution with the project's default loop bound.

This wrapper is convenient for examples.  Use `execFuel` when the chosen bound
is part of an experiment or theorem statement. -/
def exec (statement : Stmt) (state : State) : ExecResult :=
  execFuel defaultLoopFuel statement state

/- The following `@[simp]` lemmas expose useful equations for the default-bound
wrapper.  They let proofs reason about `exec` without repeatedly unfolding its
implementation.  Conditional and assertion equations require a hypothesis
stating which Boolean result was computed. -/

@[simp] theorem exec_skip (state : State) :
    exec .skip state = .normal state := by simp [exec, execFuel]

@[simp] theorem exec_assign (state : State) (name : String) (expression : Expr) :
    exec (.assign name expression) state =
      .normal (state.update name (evalExpr state expression)) := by
  simp [exec, execFuel]

@[simp] theorem exec_seq_normal (first second : Stmt) (state next : State)
    (h : exec first state = .normal next) :
    exec (.seq first second) state = exec second next := by
  simp [exec] at h
  simp [exec, execFuel, h]

@[simp] theorem exec_seq_failure (first second : Stmt) (state failed : State)
    (h : exec first state = .assertionFailure failed) :
    exec (.seq first second) state = .assertionFailure failed := by
  simp [exec] at h
  simp [exec, execFuel, h]

@[simp] theorem exec_ite_true (condition : BoolExpr) (thenBranch elseBranch : Stmt)
    (state : State) (h : evalBool state condition = true) :
    exec (.ite condition thenBranch elseBranch) state = exec thenBranch state := by
  simp [exec, execFuel, h]

@[simp] theorem exec_ite_false (condition : BoolExpr) (thenBranch elseBranch : Stmt)
    (state : State) (h : evalBool state condition = false) :
    exec (.ite condition thenBranch elseBranch) state = exec elseBranch state := by
  simp [exec, execFuel, h]

@[simp] theorem exec_assert_true (condition : BoolExpr) (state : State)
    (h : evalBool state condition = true) :
    exec (.assert condition) state = .normal state := by
  simp [exec, execFuel, h]

@[simp] theorem exec_assert_false (condition : BoolExpr) (state : State)
    (h : evalBool state condition = false) :
    exec (.assert condition) state = .assertionFailure state := by
  simp [exec, execFuel, h]

end MiniSym
