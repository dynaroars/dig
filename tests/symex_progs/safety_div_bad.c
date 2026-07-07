/* symex feature test: auto division-by-zero check (check_safety) — no
   vassert needed; the engine itself must report the reachable division
   by zero (y == 0 is allowed by the vassume) with a concrete
   counterexample input. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int q){}

int mainQ(int x, int y){
    vassume(y >= 0);       /* y == 0 still possible */
    int q = x / y;         /* BUG: division by zero when y == 0 */
    vtrace1(q);
    return q;
}
