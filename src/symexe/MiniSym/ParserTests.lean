import MiniSym.Parser

namespace MiniSym.ParserTests

open MiniSym MiniSym.Parser

private def parsesAs (source : String) (expected : Stmt) : Bool :=
  match parseProgram source with
  | .ok actual => decide (actual = expected)
  | .error _ => false

#guard parsesAs "x = a - b - c;"
    (.assign "x" (.sub (.sub (.var "a") (.var "b")) (.var "c")))

#guard parsesAs "if ((x + 1) < y && !(z == 0)) x = 1; else x = -1;"
    (.ite
      (.and (.lt (.add (.var "x") (.int 1)) (.var "y"))
        (.not (.eq (.var "z") (.int 0))))
      (.assign "x" (.int 1))
      (.assign "x" (.int (-1))))

-- An `else` belongs to the nearest unmatched `if`.
#guard parsesAs
    "if (x < 0) if (y < 0) z = 1; else z = 2; else z = 3;"
    (.ite (.lt (.var "x") (.int 0))
      (.ite (.lt (.var "y") (.int 0))
        (.assign "z" (.int 1)) (.assign "z" (.int 2)))
      (.assign "z" (.int 3)))

#guard parsesAs "/* input */ int x = input + 1; // check\nassert(x != 0);"
    (.seq
      (.assign "x" (.add (.var "input") (.int 1)))
      (.assert (.not (.eq (.var "x") (.int 0)))))

private def failed {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

#guard failed (parseProgram "int x;")
#guard parsesAs "while (x < 2) x = x + 1;"
  (.while (.lt (.var "x") (.int 2))
    (.assign "x" (.add (.var "x") (.int 1))))
#guard failed (parseProgram "for (;;) x = x + 1;")
#guard failed (parseProgram "assert(x < y < z);")
#guard failed (parseProgram "x = 1; trailing")
#guard failed (parseProgram "/* unterminated")

end MiniSym.ParserTests
