import MiniSym.Syntax

namespace MiniSym.Parser

/-!
# The C-like frontend

This module is intentionally outside the verified core. It turns a convenient
piece of source text into the `Stmt` syntax tree defined in `Syntax.lean`. The
soundness theorem proves facts about that resulting tree; it does not prove that
this parser implements ISO C.

The implementation has two phases familiar from compilers:

1. `lexLoop` converts characters into tokens such as `"if"`, `"x"`, and `"<=`".
2. The mutually recursive parsing functions consume tokens and construct ASTs.

Most parsing functions use the abbreviation `P α`: given the remaining tokens,
they either return a value of type `α` plus the unconsumed suffix, or an error.
-/

open MiniSym

structure Token where
  text : String
  pos : Nat
  deriving Repr, DecidableEq

private def isIdentStart (c : Char) : Bool := c.isAlpha || c = '_'
private def isIdentRest (c : Char) : Bool := c.isAlphanum || c = '_'

private def location (source : String) (pos : Nat) : String :=
  let before := (source.toList.take pos)
  let line := before.foldl (fun n c => if c = '\n' then n + 1 else n) 1
  let lastNl := before.reverse.findIdx (· = '\n')
  let column := if before.reverse.any (· = '\n') then lastNl + 1 else before.length + 1
  s!"line {line}, column {column}"

private def lexError (source : String) (pos : Nat) (message : String) : Except String α :=
  .error s!"{location source pos}: {message}"

private def takeWhile (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if p c then
        let (front, rest) := takeWhile p cs
        (c :: front, rest)
      else ([], c :: cs)

private partial def lexLoop (source : String) : List Char → Nat → Except String (List Token)
  | [], _ => .ok []
  | c :: cs, pos =>
      if c.isWhitespace then
        lexLoop source cs (pos + 1)
      else if isIdentStart c then
        let (tail, rest) := takeWhile isIdentRest cs
        let chars := c :: tail
        return { text := String.ofList chars, pos := pos } ::
          (← lexLoop source rest (pos + chars.length))
      else if c.isDigit then
        let (tail, rest) := takeWhile Char.isDigit cs
        let chars := c :: tail
        return { text := String.ofList chars, pos := pos } ::
          (← lexLoop source rest (pos + chars.length))
      else
        match c, cs with
        | '=', '=' :: rest => do return { text := "==", pos } :: (← lexLoop source rest (pos + 2))
        | '!', '=' :: rest => do return { text := "!=", pos } :: (← lexLoop source rest (pos + 2))
        | '<', '=' :: rest => do return { text := "<=", pos } :: (← lexLoop source rest (pos + 2))
        | '>', '=' :: rest => do return { text := ">=", pos } :: (← lexLoop source rest (pos + 2))
        | '&', '&' :: rest => do return { text := "&&", pos } :: (← lexLoop source rest (pos + 2))
        | '|', '|' :: rest => do return { text := "||", pos } :: (← lexLoop source rest (pos + 2))
        | '/', '/' :: rest =>
            let (_, after) := takeWhile (· != '\n') rest
            lexLoop source after (pos + 2 + (rest.length - after.length))
        | '/', '*' :: rest => blockComment rest (pos + 2)
        | _, _ =>
            if "()+-<>=!;{}".toList.contains c then do
              return { text := c.toString, pos := pos } :: (← lexLoop source cs (pos + 1))
            else lexError source pos s!"unexpected character '{c}'"
  where
    blockComment : List Char → Nat → Except String (List Token)
      | [], p => lexError source p "unterminated block comment"
      | '*' :: '/' :: rest, p => lexLoop source rest (p + 2)
      | _ :: rest, p => blockComment rest (p + 1)

private abbrev P (α : Type) := List Token → Except String (α × List Token)

/- `P α` is a small parser type. `Except String` represents either `.ok value`
or `.error message`; the pair carries both the parsed value and leftover tokens.
Lean's `do` notation below sequences these error-producing computations. -/

private def failAt (source : String) (tokens : List Token) (message : String) : Except String α :=
  let pos := match tokens with | t :: _ => t.pos | [] => source.length
  .error s!"{location source pos}: {message}"

private def expect (source expected : String) : P Unit
  | t :: ts => if t.text = expected then .ok ((), ts)
      else failAt source (t :: ts) s!"expected '{expected}', found '{t.text}'"
  | [] => failAt source [] s!"expected '{expected}', found end of input"

private def isIdentifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentStart c && cs.all isIdentRest &&
      !["if", "else", "while", "assert", "int"].contains s

private def identifier (source : String) : P String
  | t :: ts => if isIdentifier t.text then .ok (t.text, ts)
      else failAt source (t :: ts) s!"expected identifier, found '{t.text}'"
  | [] => failAt source [] "expected identifier, found end of input"

private def numeral? (s : String) : Option Int :=
  if !s.isEmpty && s.toList.all Char.isDigit then s.toInt? else none

private partial def parseExpr (source : String) : P Expr := parseAddSub
where
  /- Arithmetic precedence is simple because MiniC has only `+` and `-`.
  `parseAtom` handles constants, variables, negative literals, and parentheses;
  `loop` then folds a chain left, so `a - b - c` means `(a - b) - c`. -/
  parseAtom : P Expr
    | { text := "(", .. } :: ts => do
        let (e, ts) ← parseExpr source ts
        let (_, ts) ← expect source ")" ts
        return (e, ts)
    | { text := "-", .. } :: t :: ts =>
        match numeral? t.text with
        | some n => .ok (.int (-n), ts)
        | none => failAt source (t :: ts) "unary '-' is supported only on integer literals"
    | t :: ts =>
        match numeral? t.text with
        | some n => .ok (.int n, ts)
        | none => if isIdentifier t.text then .ok (.var t.text, ts)
            else failAt source (t :: ts) s!"expected arithmetic expression, found '{t.text}'"
    | [] => failAt source [] "expected arithmetic expression, found end of input"
  parseAddSub : P Expr := fun ts => do
    let (first, rest) ← parseAtom ts
    loop first rest
  loop (left : Expr) : P Expr
    | { text := "+", .. } :: ts => do
        let (right, ts) ← parseAtom ts
        loop (.add left right) ts
    | { text := "-", .. } :: ts => do
        let (right, ts) ← parseAtom ts
        loop (.sub left right) ts
    | ts => .ok (left, ts)

private partial def parseBool (source : String) : P BoolExpr := parseOr
where
  /- Boolean precedence, from tightest to loosest, is comparison, `!`, `&&`,
  then `||`. Greater-than operations need no core constructors: `a > b` becomes
  `b < a`, while `a >= b` becomes `b <= a`. -/
  parseComparison : P BoolExpr := fun ts => do
    let (left, ts) ← parseExpr source ts
    match ts with
    | op :: rest =>
      if ["==", "!=", "<", "<=", ">", ">="].contains op.text then do
        let (right, rest) ← parseExpr source rest
        let b := match op.text with
          | "==" => BoolExpr.eq left right
          | "!=" => .not (.eq left right)
          | "<" => .lt left right
          | "<=" => .le left right
          | ">" => .lt right left
          | _ => .le right left
        return (b, rest)
      else failAt source ts s!"expected comparison operator, found '{op.text}'"
    | [] => failAt source [] "expected comparison operator, found end of input"
  parseUnary : P BoolExpr
    | { text := "!", .. } :: ts => do
        let (b, ts) ← parseUnary ts
        return (.not b, ts)
    | all@({ text := "(", .. } :: ts) =>
        -- Parentheses can group either a Boolean formula or the left side of a
        -- comparison, as in `(x + 1) < y`; try Boolean grouping first.
        match parseBool source ts with
        | .ok (b, ts) => match expect source ")" ts with
            | .ok (_, ts) => .ok (b, ts)
            | .error _ => parseComparison all
        | .error _ => parseComparison all
    | ts => parseComparison ts
  parseAnd : P BoolExpr := fun ts => do
    let (first, rest) ← parseUnary ts
    andLoop first rest
  andLoop (left : BoolExpr) : P BoolExpr
    | { text := "&&", .. } :: ts => do
        let (right, ts) ← parseUnary ts
        andLoop (.and left right) ts
    | ts => .ok (left, ts)
  parseOr : P BoolExpr := fun ts => do
    let (first, rest) ← parseAnd ts
    orLoop first rest
  orLoop (left : BoolExpr) : P BoolExpr
    | { text := "||", .. } :: ts => do
        let (right, ts) ← parseAnd ts
        orLoop (.or left right) ts
    | ts => .ok (left, ts)

private def sequence : List Stmt → Stmt
  | [] => .skip
  | s :: ss => ss.foldl Stmt.seq s

private partial def parseStmt (source : String) : P Stmt
  /- Statement parsing is recursive because blocks contain statements and the
  bodies of `if` and `while` are themselves statements. An initialized `int`
  declaration is deliberately lowered to assignment; no C scope or type is
  introduced into the verified language. -/
  | { text := ";", .. } :: ts => .ok (.skip, ts)
  | { text := "{", .. } :: ts => do
      let (ss, ts) ← parseMany source true ts
      return (sequence ss, ts)
  | { text := "if", .. } :: ts => do
      let (_, ts) ← expect source "(" ts
      let (condition, ts) ← parseBool source ts
      let (_, ts) ← expect source ")" ts
      let (yes, ts) ← parseStmt source ts
      let (_, ts) ← expect source "else" ts
      let (no, ts) ← parseStmt source ts
      return (.ite condition yes no, ts)
  | { text := "while", .. } :: ts => do
      let (_, ts) ← expect source "(" ts
      let (condition, ts) ← parseBool source ts
      let (_, ts) ← expect source ")" ts
      let (body, ts) ← parseStmt source ts
      return (.while condition body, ts)
  | { text := "assert", .. } :: ts => do
      let (_, ts) ← expect source "(" ts
      let (condition, ts) ← parseBool source ts
      let (_, ts) ← expect source ")" ts
      let (_, ts) ← expect source ";" ts
      return (.assert condition, ts)
  | { text := "int", .. } :: ts => do
      let (name, ts) ← identifier source ts
      match ts with
      | { text := ";", .. } :: _ =>
          failAt source ts "uninitialized declarations are unsupported; provide an initializer"
      | { text := "=", .. } :: rest => do
          let (e, rest) ← parseExpr source rest
          let (_, rest) ← expect source ";" rest
          return (.assign name e, rest)
      | _ => failAt source ts "expected '=' or ';' after declaration"
  | ts => do
      let (name, ts) ← identifier source ts
      let (_, ts) ← expect source "=" ts
      let (e, ts) ← parseExpr source ts
      let (_, ts) ← expect source ";" ts
      return (.assign name e, ts)
where
  parseMany (source : String) (inBlock : Bool) : P (List Stmt)
    | [] => if inBlock then failAt source [] "expected '}' before end of input" else .ok ([], [])
    | token@{ text := "}", .. } :: ts =>
        if inBlock then .ok ([], ts) else failAt source (token :: ts) "unexpected '}'"
    | ts => do
        let (s, ts) ← parseStmt source ts
        let (ss, ts) ← parseMany source inBlock ts
        return (s :: ss, ts)

/-- Parse the supported C-like MiniC subset into the verified core AST. -/
def parseProgram (source : String) : Except String Stmt := do
  -- A successful top-level parse must consume every token. This prevents an
  -- accepted prefix from hiding unsupported syntax at the end of a file.
  let tokens ← lexLoop source source.toList 0
  let (statements, rest) ← parseStmt.parseMany source false tokens
  match rest with
  | [] => return sequence statements
  | t :: _ => failAt source rest s!"unexpected token '{t.text}'"

end MiniSym.Parser
