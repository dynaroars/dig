import MiniSym.Parser
import MiniSym.SymExec

namespace MiniSym.Cli

/-!
# Command-line driver

This file contains plumbing rather than semantics or proofs. It reads a file,
calls the parser, chooses which variable names to display, runs `symExecFuel`,
and prints finite snapshots of otherwise functional symbolic stores.
-/

open MiniSym

private def exprNames : Expr → List String
  | .int _ => []
  | .var name => [name]
  | .add lhs rhs | .sub lhs rhs => exprNames lhs ++ exprNames rhs

private def boolNames : BoolExpr → List String
  | .eq lhs rhs | .lt lhs rhs | .le lhs rhs => exprNames lhs ++ exprNames rhs
  | .not condition => boolNames condition
  | .and lhs rhs | .or lhs rhs => boolNames lhs ++ boolNames rhs

private def stmtNames : Stmt → List String
  -- This traversal is only for display. It collects names mentioned anywhere
  -- in the AST so users need not list them manually on the command line.
  | .skip => []
  | .assign name value => name :: exprNames value
  | .seq first second => stmtNames first ++ stmtNames second
  | .ite condition yes no => boolNames condition ++ stmtNames yes ++ stmtNames no
  | .while condition body => boolNames condition ++ stmtNames body
  | .assert condition => boolNames condition

private def uniqueNames (names : List String) : List String :=
  names.foldl (fun found name => if name ∈ found then found else found ++ [name]) []

def usage : String :=
  "Usage: lake exe minisym [--fuel N] <file.c> [variable ...]"

def run (fuel : Nat) (path : String) (requestedNames : List String) : IO UInt32 := do
  /- `IO` marks operations that interact with the outside world. The `do` block
  lets the code read like an ordinary sequence while Lean still tracks errors
  and return values through types. Exit code 0 means success. -/
  let source ← try
    IO.FS.readFile path
  catch error =>
    IO.eprintln s!"minisym: cannot read '{path}': {error}"
    return 1
  match Parser.parseProgram source with
  | .error message =>
      IO.eprintln s!"minisym: parse error in '{path}': {message}"
      return 1
  | .ok statement =>
      let names :=
        if requestedNames.isEmpty then uniqueNames (stmtNames statement)
        else uniqueNames requestedNames
      IO.println s!"Symbolic results for {path}:"
      IO.println (reprStr (snapshotResults names (symExecFuel fuel statement initialSymState)))
      return 0

end MiniSym.Cli

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => do
      IO.eprintln MiniSym.Cli.usage
      pure 2
  | "--fuel" :: fuelText :: path :: names =>
      match fuelText.toNat? with
      | some fuel => MiniSym.Cli.run fuel path names
      | none => do
          IO.eprintln s!"minisym: invalid loop fuel '{fuelText}'"
          pure 2
  | "--fuel" :: _ => do
      IO.eprintln MiniSym.Cli.usage
      pure 2
  | path :: names => MiniSym.Cli.run MiniSym.defaultLoopFuel path names
