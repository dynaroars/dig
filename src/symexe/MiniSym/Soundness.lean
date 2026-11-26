import MiniSym.Concrete
import MiniSym.SymExec

namespace MiniSym

/-!
# Why this file exists

The concrete evaluator and symbolic executor compute in two different worlds:

* a concrete `State` maps every program variable directly to an integer;
* a `SymState` maps variables to symbolic expressions and records a symbolic
  path condition.

This file connects those worlds.  First it defines when a concrete state is an
instance of a symbolic state (`Matches`).  It then proves small reusable facts
about expressions, assignments, and branches.  Finally, `symExecFuel_sound`
assembles those facts into the central end-to-end guarantee.

The comments below are intentionally more detailed than one would normally put
in a small Lean development.  They are meant to make the proof readable as a
worked example for someone learning Lean.
-/

/-- `state` is the concrete instance of `symbolic` under `valuation`.

Besides relating the stores, this requires the valuation to satisfy the path
condition.  Thus an infeasible symbolic state represents no concrete state. -/
def Matches (valuation : Valuation) (state : State) (symbolic : SymState) : Prop :=
  interpretBool valuation symbolic.pc = true ∧
    ∀ name, state name = interpretExpr valuation (symbolic.store name)

/-
`Matches valuation state symbolic` is a pair of facts (Lean's `/\`, written
`∧`):

1. `h.1` says that this choice of symbolic inputs satisfies the path condition.
2. `h.2 name` says that looking up any program variable `name` in the concrete
   store agrees with interpreting its symbolic expression under `valuation`.

Notice that the equality is required for *every* `String`.  This works neatly
because both stores are total functions and therefore have no missing lookup.
Also notice why the first conjunct matters: without it, even an impossible
symbolic path could claim to represent a concrete execution.
-/

/-- The canonical symbolic input state represents the valuation viewed as a
concrete initial store. This also makes the main theorem's premise explicitly
inhabited for every input valuation. -/
theorem initial_matches (valuation : Valuation) :
    Matches valuation valuation initialSymState := by
  constructor
  · rfl
  · intro name
    rfl

/-
In theorem signatures, arguments in braces such as `{state : State}` are
implicit: Lean normally infers them from the other arguments.  Parenthesized
arguments such as `(expression : Expr)` are explicit and are supplied by the
caller.  The hypothesis `h : Matches ...` carries the semantic connection used
throughout the following proofs.
-/

/-- Symbolic evaluation of an arithmetic expression denotes its concrete
evaluation in every pair of matching states. -/
theorem symEvalExpr_sound {valuation : Valuation} {state : State}
    {symbolic : SymState} (h : Matches valuation state symbolic) (expression : Expr) :
    evalExpr state expression =
      interpretExpr valuation (symEvalExpr symbolic.store expression) := by
  induction expression with
  | int value => rfl
  | var name => exact h.2 name
  | add lhs rhs lhsIH rhsIH =>
      simp only [evalExpr, symEvalExpr, interpretExpr]
      rw [lhsIH, rhsIH]

/-
Proof pattern above: `induction expression` creates one goal per constructor of
`Expr`.  Constants are identical by definition (`rfl`).  A variable is exactly
the store part of `Matches` (`h.2 name`).  Addition and subtraction first unfold
the three evaluators with `simp only`, then rewrite both operands with their
induction hypotheses.  Thus the proof follows the syntax tree structurally.
-/
  | sub lhs rhs lhsIH rhsIH =>
      simp only [evalExpr, symEvalExpr, interpretExpr]
      rw [lhsIH, rhsIH]

/-- Symbolic evaluation of a Boolean expression has exactly the same truth
value as concrete evaluation in matching states. -/
theorem symEvalBool_sound {valuation : Valuation} {state : State}
    {symbolic : SymState} (h : Matches valuation state symbolic) (condition : BoolExpr) :
    evalBool state condition =
      interpretBool valuation (symEvalBool symbolic.store condition) := by
  induction condition with
  | eq lhs rhs =>
      simp only [evalBool, symEvalBool, interpretBool]
      rw [symEvalExpr_sound h lhs, symEvalExpr_sound h rhs]
  | lt lhs rhs =>
      simp only [evalBool, symEvalBool, interpretBool]
      rw [symEvalExpr_sound h lhs, symEvalExpr_sound h rhs]
  | le lhs rhs =>
      simp only [evalBool, symEvalBool, interpretBool]
      rw [symEvalExpr_sound h lhs, symEvalExpr_sound h rhs]
  | not condition ih =>
      simp only [evalBool, symEvalBool, interpretBool]
      rw [ih]
  | and lhs rhs lhsIH rhsIH =>
      simp only [evalBool, symEvalBool, interpretBool]
      rw [lhsIH, rhsIH]

/-
Boolean soundness has the same structural shape.  Comparison cases reuse
`symEvalExpr_sound`; logical connectives reuse the induction hypotheses for
their Boolean children.  The theorem proves equality of computed `Bool`s, so it
is useful in both true-branch and false-branch proofs without any classical
logic.
-/
  | or lhs rhs lhsIH rhsIH =>
      simp only [evalBool, symEvalBool, interpretBool]
      rw [lhsIH, rhsIH]

/-- Assignment updates concrete and symbolic stores in lockstep. -/
theorem matches_update {valuation : Valuation} {state : State}
    {symbolic : SymState} (h : Matches valuation state symbolic)
    (name : String) (expression : Expr) :
    Matches valuation
      (state.update name (evalExpr state expression))
      { symbolic with
        store := updateStore symbolic.store name
          (symEvalExpr symbolic.store expression) } := by
  constructor
  · exact h.1
  · intro queried
    change state.update name (evalExpr state expression) queried =
      interpretExpr valuation
        (updateStore symbolic.store name
          (symEvalExpr symbolic.store expression) queried)
    by_cases hname : queried = name
    · subst queried
      simp only [State.update_same, updateStore_same]
      exact symEvalExpr_sound h expression
    · rw [State.update_of_ne _ _ _ hname, updateStore_of_ne _ _ _ hname]
      exact h.2 queried

/-
The interesting part of assignment is a lookup in the updated store.  The
`by_cases` splits on whether `queried` is the assigned name:

* for the assigned variable, expression soundness proves that the new concrete
  integer and new symbolic expression denote the same value;
* every other variable is unchanged, so the old `h.2` fact applies.

The path condition is deliberately unchanged by assignment, which is why its
proof is simply `h.1`.
-/

/-- A concrete true condition selects a satisfiable then-path. -/
theorem matches_then {valuation : Valuation} {state : State}
    {symbolic : SymState} (h : Matches valuation state symbolic)
    (condition : BoolExpr) (hcondition : evalBool state condition = true) :
    Matches valuation state
      { symbolic with
        pc := .and symbolic.pc (symEvalBool symbolic.store condition) } := by
  constructor
  · simp only [interpretBool, h.1, Bool.true_and]
    rw [← symEvalBool_sound h condition]
    exact hcondition
  · exact h.2

/-- A concrete false condition selects a satisfiable else-path. -/
theorem matches_else {valuation : Valuation} {state : State}
    {symbolic : SymState} (h : Matches valuation state symbolic)
    (condition : BoolExpr) (hcondition : evalBool state condition = false) :
    Matches valuation state
      { symbolic with
        pc := .and symbolic.pc (.not (symEvalBool symbolic.store condition)) } := by
  constructor
  · simp only [interpretBool, h.1, Bool.true_and]
    rw [← symEvalBool_sound h condition, hcondition]
    rfl
  · exact h.2

/-
`matches_then` and `matches_else` are the bridge from a concrete branch choice
to a symbolic path.  Expression stores do not change.  The new path condition
is the old condition conjoined with the symbolic guard (or its negation).
`symEvalBool_sound` transfers the known concrete truth value to that symbolic
guard.
-/

/-- Concrete and symbolic results agree on both the outcome tag and the state
represented at normal termination or at the assertion-failure point. -/
inductive ResultMatches (valuation : Valuation) : ExecResult → SymResult → Prop where
  | normal (h : Matches valuation state symbolic) :
      ResultMatches valuation (.normal state) (.normal symbolic)
  | assertionFailure (h : Matches valuation state symbolic) :
      ResultMatches valuation (.assertionFailure state) (.assertionFailure symbolic)
  | fuelExhausted (h : Matches valuation state symbolic) :
      ResultMatches valuation (.fuelExhausted state) (.fuelExhausted symbolic)

/-
This relation is deliberately *tag-sensitive*.  Its constructors permit only
normal/normal, assertionFailure/assertionFailure, and
fuelExhausted/fuelExhausted pairs.  There is no constructor that could match a
concrete assertion failure with a symbolic normal result, for example.  A proof
of `ResultMatches` therefore establishes both state correspondence and agreement
about how execution stopped.
-/

/-- Soundness of bounded symbolic execution.

For every concrete execution starting in a represented state, symbolic
execution generates a result with the same normal/failure outcome whose store
and path condition represent the concrete result under the same valuation. -/
theorem symExecFuel_sound (fuel : Nat) (statement : Stmt)
    {valuation : Valuation} {state : State}
    {symbolic : SymState} (h : Matches valuation state symbolic) :
    ∃ result, result ∈ symExecFuel fuel statement symbolic ∧
      ResultMatches valuation (execFuel fuel statement state) result := by
  -- Outer induction is on fuel because a true `while` branch recurses with a
  -- smaller budget. `generalizing` keeps the statement and states arbitrary,
  -- so the induction hypothesis can be applied after executing a loop body.
  induction fuel generalizing statement state symbolic with
  | zero =>
    -- Even with zero loop fuel, non-loop statements still execute normally.
    -- We therefore perform a second induction over the statement syntax.
    induction statement generalizing state symbolic with
    | skip =>
      -- `skip` returns the unchanged state on both sides.
      exact ⟨.normal symbolic, by simp [symExecFuel],
        by simpa [execFuel] using (ResultMatches.normal h)⟩
    | assign name expression =>
      -- Assignment is exactly the local `matches_update` lemma.
      exact ⟨.normal { symbolic with
                  store := updateStore symbolic.store name
                    (symEvalExpr symbolic.store expression) },
        by simp [symExecFuel], by simpa [execFuel] using
          (ResultMatches.normal (matches_update h name expression))⟩
    | seq first second firstIH secondIH =>
      -- Symbolic sequencing uses `flatMap`: each result of `first` is fed to
      -- `second` only when it is normal.  First obtain the symbolic witness
      -- promised by the induction hypothesis, then inspect the concrete tag.
      obtain ⟨firstResult, hfirstMem, hfirstMatches⟩ := firstIH h
      cases hfirstExec : execFuel 0 first state with
      | normal intermediate =>
          -- A normal first result allows execution of `second`.
          rw [hfirstExec] at hfirstMatches
          cases hfirstMatches with
          | normal hIntermediate =>
              obtain ⟨result, hresultMem, hresultMatches⟩ := secondIH hIntermediate
              refine ⟨result, ?_, ?_⟩
              · simp only [symExecFuel, List.mem_flatMap]
                exact ⟨.normal _, hfirstMem, hresultMem⟩
              · simpa [execFuel, hfirstExec] using hresultMatches
      | assertionFailure failed =>
          -- Failures short-circuit; constructor sensitivity forces the
          -- symbolic first result to carry the same failure tag.
          rw [hfirstExec] at hfirstMatches
          cases hfirstMatches with
          | assertionFailure hFailed =>
              rename_i failedSymbolic
              refine ⟨.assertionFailure failedSymbolic, ?_, ?_⟩
              · simp only [symExecFuel, List.mem_flatMap]
                exact ⟨.assertionFailure failedSymbolic, hfirstMem, by simp⟩
              · simpa [execFuel, hfirstExec] using
                  (ResultMatches.assertionFailure hFailed)
      | fuelExhausted stopped =>
          -- Fuel exhaustion short-circuits in the same way.
          rw [hfirstExec] at hfirstMatches
          cases hfirstMatches with
          | fuelExhausted hStopped =>
              rename_i stoppedSymbolic
              refine ⟨.fuelExhausted stoppedSymbolic, ?_, ?_⟩
              · simp only [symExecFuel, List.mem_flatMap]
                exact ⟨.fuelExhausted stoppedSymbolic, hfirstMem, by simp⟩
              · simpa [execFuel, hfirstExec] using
                  (ResultMatches.fuelExhausted hStopped)
    | ite condition yes no yesIH noIH =>
      -- Concrete evaluation chooses one branch.  Symbolic execution emits
      -- both, and `matches_then`/`matches_else` identify the corresponding one.
      cases hcondition : evalBool state condition with
      | false =>
          obtain ⟨result, hmem, hmatches⟩ :=
            noIH (matches_else h condition hcondition)
          exact ⟨result, by simp [symExecFuel, hmem],
            by simpa [execFuel, hcondition] using hmatches⟩
      | true =>
          obtain ⟨result, hmem, hmatches⟩ :=
            yesIH (matches_then h condition hcondition)
          exact ⟨result, by simp [symExecFuel, hmem],
            by simpa [execFuel, hcondition] using hmatches⟩
    | «while» condition body bodyIH =>
      -- At fuel zero a false guard exits normally.  A true guard cannot be
      -- unfolded, so both semantics explicitly report fuel exhaustion.
      cases hcondition : evalBool state condition with
      | false =>
          refine ⟨.normal { symbolic with pc := (SymBool.and symbolic.pc
              (SymBool.not (symEvalBool symbolic.store condition))) }, ?_, ?_⟩
          · simp [symExecFuel]
          · simpa [execFuel, hcondition] using
              (ResultMatches.normal (matches_else h condition hcondition))
      | true =>
          refine ⟨.fuelExhausted { symbolic with pc := (SymBool.and symbolic.pc
              (symEvalBool symbolic.store condition)) }, ?_, ?_⟩
          · simp [symExecFuel]
          · simpa [execFuel, hcondition] using
              (ResultMatches.fuelExhausted (matches_then h condition hcondition))
    | assert condition =>
      -- Assertions fork symbolically into a normal path guarded by the
      -- condition and a failure path guarded by its negation.  Concrete truth
      -- selects the matching witness.
      cases hcondition : evalBool state condition with
      | false =>
          refine ⟨.assertionFailure { symbolic with pc := (SymBool.and symbolic.pc
              (SymBool.not (symEvalBool symbolic.store condition))) }, by simp [symExecFuel], ?_⟩
          simpa [execFuel, hcondition] using
            (ResultMatches.assertionFailure (matches_else h condition hcondition))
      | true =>
          refine ⟨.normal { symbolic with pc := (SymBool.and symbolic.pc
              (symEvalBool symbolic.store condition)) }, by simp [symExecFuel], ?_⟩
          simpa [execFuel, hcondition] using
            (ResultMatches.normal (matches_then h condition hcondition))
  | succ remaining fuelIH =>
    -- With positive fuel, the non-loop cases mirror the zero-fuel proof.
    -- The loop-true case below additionally uses `fuelIH` for the next
    -- iteration after a normally completed body.
    induction statement generalizing state symbolic with
  | skip =>
      exact ⟨.normal symbolic, by simp [symExecFuel],
        by simpa [execFuel] using (ResultMatches.normal h)⟩
  | assign name expression =>
      exact ⟨.normal { symbolic with
                store := updateStore symbolic.store name
                  (symEvalExpr symbolic.store expression) },
        by simp [symExecFuel], by simpa [execFuel] using
          (ResultMatches.normal (matches_update h name expression))⟩
  | seq first second firstIH secondIH =>
      -- As in the zero-fuel case, analyze how the concrete first statement
      -- stopped.  `rw [...] at hfirstMatches` exposes that same tag inside the
      -- relation, and `cases hfirstMatches` rules out all mismatched tags.
      obtain ⟨firstResult, hfirstMem, hfirstMatches⟩ := firstIH h
      cases hfirstExec : execFuel (remaining + 1) first state with
      | normal intermediate =>
          rw [hfirstExec] at hfirstMatches
          cases hfirstMatches with
          | normal hIntermediate =>
              obtain ⟨result, hresultMem, hresultMatches⟩ := secondIH hIntermediate
              refine ⟨result, ?_, ?_⟩
              · simp only [symExecFuel, List.mem_flatMap]
                exact ⟨.normal _, hfirstMem, hresultMem⟩
              · simpa [execFuel, hfirstExec] using hresultMatches
      | assertionFailure failed =>
          rw [hfirstExec] at hfirstMatches
          cases hfirstMatches with
          | assertionFailure hFailed =>
              rename_i failedSymbolic
              refine ⟨.assertionFailure failedSymbolic, ?_, ?_⟩
              · simp only [symExecFuel, List.mem_flatMap]
                exact ⟨.assertionFailure failedSymbolic, hfirstMem, by simp⟩
              · simpa [execFuel, hfirstExec] using
                  (ResultMatches.assertionFailure hFailed)
      | fuelExhausted stopped =>
          rw [hfirstExec] at hfirstMatches
          cases hfirstMatches with
          | fuelExhausted hStopped =>
              rename_i stoppedSymbolic
              refine ⟨.fuelExhausted stoppedSymbolic, ?_, ?_⟩
              · simp only [symExecFuel, List.mem_flatMap]
                exact ⟨.fuelExhausted stoppedSymbolic, hfirstMem, by simp⟩
              · simpa [execFuel, hfirstExec] using
                  (ResultMatches.fuelExhausted hStopped)
  | ite condition yes no yesIH noIH =>
      -- Membership in symbolic `if` output is membership in an appended list:
      -- the then witness is introduced with `Or.inl`, the else witness with
      -- `Or.inr`.
      cases hcondition : evalBool state condition with
      | false =>
          obtain ⟨result, hmem, hmatches⟩ :=
            noIH (matches_else h condition hcondition)
          refine ⟨result, ?_, ?_⟩
          · simp only [symExecFuel, List.mem_append]
            exact Or.inr hmem
          · simpa [execFuel, hcondition] using hmatches
      | true =>
          obtain ⟨result, hmem, hmatches⟩ :=
            yesIH (matches_then h condition hcondition)
          refine ⟨result, ?_, ?_⟩
          · simp only [symExecFuel, List.mem_append]
            exact Or.inl hmem
          · simpa [execFuel, hcondition] using hmatches
    | «while» condition body bodyIH =>
      -- A false guard exits without consuming an iteration.  For a true guard,
      -- `enterState` strengthens the path condition, `bodyIH` covers the body,
      -- and the outer `fuelIH` covers the recursive loop with one less fuel.
      cases hcondition : evalBool state condition with
      | false =>
          refine ⟨.normal { symbolic with pc := (SymBool.and symbolic.pc
              (SymBool.not (symEvalBool symbolic.store condition))) }, ?_, ?_⟩
          · simp [symExecFuel]
          · simpa [execFuel, hcondition] using
              (ResultMatches.normal (matches_else h condition hcondition))
      | true =>
          -- The local name makes the symbolic state at loop entry readable;
          -- Lean unfolds it automatically where required below.
          let enterState := { symbolic with pc := (SymBool.and symbolic.pc
            (symEvalBool symbolic.store condition)) }
          obtain ⟨bodyResult, hbodyMem, hbodyMatches⟩ :=
            bodyIH (matches_then h condition hcondition)
          cases hbodyExec : execFuel (remaining + 1) body state with
          | normal intermediate =>
              -- Only a normal body result proceeds to another iteration.
              rw [hbodyExec] at hbodyMatches
              cases hbodyMatches with
              | normal hIntermediate =>
                  obtain ⟨result, hresultMem, hresultMatches⟩ :=
                    fuelIH (.while condition body) hIntermediate
                  refine ⟨result, ?_, ?_⟩
                  · simp only [symExecFuel, List.mem_append, List.mem_flatMap]
                    exact Or.inl ⟨.normal _, hbodyMem, hresultMem⟩
                  · simpa [execFuel, hcondition, hbodyExec] using hresultMatches
          | assertionFailure failed =>
              -- An assertion failure in the body is propagated unchanged.
              rw [hbodyExec] at hbodyMatches
              cases hbodyMatches with
              | assertionFailure hFailed =>
                  rename_i failedSymbolic
                  refine ⟨.assertionFailure failedSymbolic, ?_, ?_⟩
                  · simp only [symExecFuel, List.mem_append, List.mem_flatMap]
                    exact Or.inl ⟨.assertionFailure _, hbodyMem, by simp⟩
                  · simpa [execFuel, hcondition, hbodyExec] using
                      (ResultMatches.assertionFailure hFailed)
          | fuelExhausted stopped =>
              -- Nested-loop exhaustion in the body is also propagated.
              rw [hbodyExec] at hbodyMatches
              cases hbodyMatches with
              | fuelExhausted hStopped =>
                  rename_i stoppedSymbolic
                  refine ⟨.fuelExhausted stoppedSymbolic, ?_, ?_⟩
                  · simp only [symExecFuel, List.mem_append, List.mem_flatMap]
                    exact Or.inl ⟨.fuelExhausted _, hbodyMem, by simp⟩
                  · simpa [execFuel, hcondition, hbodyExec] using
                      (ResultMatches.fuelExhausted hStopped)
  | assert condition =>
      -- This is the positive-fuel version of the same assertion argument;
      -- assertions themselves do not consume loop fuel.
      cases hcondition : evalBool state condition with
      | false =>
          refine ⟨.assertionFailure
              { symbolic with
                pc := .and symbolic.pc
                  (.not (symEvalBool symbolic.store condition)) }, ?_, ?_⟩
          · simp [symExecFuel]
          · simpa [execFuel, hcondition] using
              (ResultMatches.assertionFailure
                (matches_else h condition hcondition))
      | true =>
          refine ⟨.normal
              { symbolic with
                pc := .and symbolic.pc (symEvalBool symbolic.store condition) }, ?_, ?_⟩
          · simp [symExecFuel]
          · simpa [execFuel, hcondition] using
              (ResultMatches.normal (matches_then h condition hcondition))

/-- Convenience specialization at the default loop bound. -/
theorem symExec_sound (statement : Stmt) {valuation : Valuation} {state : State}
    {symbolic : SymState} (h : Matches valuation state symbolic) :
    ∃ result, result ∈ symExec statement symbolic ∧
      ResultMatches valuation (exec statement state) result := by
  simpa [symExec, exec] using
    (symExecFuel_sound defaultLoopFuel statement h)

/-
`symExec_sound` is not a second independent proof.  The public `symExec` and
`exec` functions are definitions that choose `defaultLoopFuel`; `simpa` unfolds
those wrappers and specializes the fully general fuel theorem.  Consequently,
the convenient API inherits exactly the same result-tag and state guarantee.

Reading the conclusion from the inside out:

* `exec statement state` is the one concrete outcome;
* `symExec statement symbolic` is a list of symbolic outcomes;
* the existential says there is some `result` in that list;
* `ResultMatches` says that witness has the same stopping tag and represents
  the concrete final (or failure/exhaustion) state under the original valuation.

The theorem does not claim that every generated symbolic path is feasible.  It
claims the essential soundness direction: no represented concrete execution is
missing from the symbolic results.
-/

end MiniSym
