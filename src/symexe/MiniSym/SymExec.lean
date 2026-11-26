import MiniSym.Symbolic

namespace MiniSym

/--
The three ways a symbolic path can stop.

Each constructor retains the state (including its path condition) at the point
where it stopped.  `assertionFailure` means the assertion is false for values
satisfying that path condition; it does not by itself prove that such values
exist.  `fuelExhausted` makes bounded loop exploration explicit instead of
silently dropping executions that require more iterations.
-/
inductive SymResult where
  | normal : SymState → SymResult
  | assertionFailure : SymState → SymResult
  | fuelExhausted : SymState → SymResult

/--
Bounded symbolic execution, returning every path as a list of results.

The cases mirror the statement syntax:

* `skip` returns its input unchanged.
* assignment symbolically evaluates the right-hand side and updates the store.
* sequence feeds every normal result of its first statement into its second.
* `if` forks and strengthens each path condition with the appropriate guard.
* assertion forks into a successful and a potentially failing result.
* `while` repeatedly forks into entering and exiting paths.

`fuel` is a recursive per-loop unrolling bound; loop-free statements do not
consume it.  At an exhausted loop, we still split the condition: the path on
which the guard is false exits normally, while the path requiring another
iteration is reported as `fuelExhausted`.  The executor deliberately keeps
infeasible paths; feasibility checking is a separate concern.
-/
def symExecFuel : Nat → Stmt → SymState → List SymResult
  | _, .skip, state => [.normal state]
  | _, .assign name expr, state =>
      [.normal { state with store := updateStore state.store name (symEvalExpr state.store expr) }]
  | fuel, .seq first second, state =>
      -- `flatMap` concatenates the result lists produced for every first-step
      -- path.  Only a normal result continues; failures already terminate.
      (symExecFuel fuel first state).flatMap fun result =>
        match result with
        | .normal next => symExecFuel fuel second next
        | .assertionFailure failed => [.assertionFailure failed]
        | .fuelExhausted stopped => [.fuelExhausted stopped]
  | fuel, .ite condition yes no, state =>
      -- Both branches are explored.  Their PCs distinguish the assumptions
      -- under which the concrete execution would choose each branch.
      let symbolicCondition := symEvalBool state.store condition
      let yesState := { state with pc := .and state.pc symbolicCondition }
      let noState := { state with pc := .and state.pc (.not symbolicCondition) }
      symExecFuel fuel yes yesState ++ symExecFuel fuel no noState
  | _, .assert condition, state =>
      -- Keeping both outcomes exposes possible assertion violations.  A later
      -- feasibility checker may discard either path if its PC is impossible.
      let symbolicCondition := symEvalBool state.store condition
      [ .normal { state with pc := .and state.pc symbolicCondition },
        .assertionFailure { state with pc := .and state.pc (.not symbolicCondition) } ]
  | fuel, .while condition body, state =>
      -- As with `if`, entering assumes the guard and exiting assumes its
      -- negation.  One unit of fuel is consumed only when an iteration begins.
      let symbolicCondition := symEvalBool state.store condition
      let enterState := { state with pc := .and state.pc symbolicCondition }
      let exitState := { state with pc := .and state.pc (.not symbolicCondition) }
      match fuel with
      | 0 => [.normal exitState, .fuelExhausted enterState]
      | remaining + 1 =>
          -- A normally completed body loops again with less fuel.  Terminal
          -- body outcomes propagate unchanged and do not continue the loop.
          (symExecFuel (remaining + 1) body enterState).flatMap (fun result =>
            match result with
            | .normal next => symExecFuel remaining (.while condition body) next
            | .assertionFailure failed => [.assertionFailure failed]
            | .fuelExhausted stopped => [.fuelExhausted stopped]) ++
          [.normal exitState]
termination_by fuel statement _ => (fuel, sizeOf statement)
-- Lean checks totality using this lexicographic measure.  Recursive calls
-- either decrease the statement's structural size, or (for another loop
-- iteration) decrease `fuel`.  Thus symbolic execution is executable without
-- using an unchecked escape hatch or assuming termination.

/-- Run symbolic execution with the project's default loop-unrolling bound. -/
def symExec (statement : Stmt) (state : SymState) : List SymResult :=
  symExecFuel defaultLoopFuel statement state

/-- Printable counterpart of `SymResult`, preserving its outcome kind. -/
inductive SymResultSnapshot where
  | normal : SymStateSnapshot → SymResultSnapshot
  | assertionFailure : SymStateSnapshot → SymResultSnapshot
  | fuelExhausted : SymStateSnapshot → SymResultSnapshot
  deriving Repr, DecidableEq

/-- Turn a result into a finite display of the variables selected by `names`. -/
def SymResult.snapshot (result : SymResult) (names : List String) : SymResultSnapshot :=
  match result with
  | .normal state => .normal (state.snapshot names)
  | .assertionFailure state => .assertionFailure (state.snapshot names)
  | .fuelExhausted state => .fuelExhausted (state.snapshot names)

/-- Convenience function used by examples to print a whole result list. -/
def snapshotResults (names : List String) (results : List SymResult) : List SymResultSnapshot :=
  results.map fun result => result.snapshot names

end MiniSym
