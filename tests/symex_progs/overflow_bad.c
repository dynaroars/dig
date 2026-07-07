/* symex feature test: signed-overflow check (check_overflow) — inputs
   are constrained to the 32-bit int range, and the engine must report
   that x * x can exceed INT_MAX, with a concrete large x. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int sq){}

int mainQ(int x, int y){
    vassume(x > 0);
    int sq = x * x;    /* BUG: overflows for x > 46340 */
    vtrace1(sq);
    return sq;
}
