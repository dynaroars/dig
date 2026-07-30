/* symex feature test: multiphase ranking synthesis — x first RISES
   (while y > 0) and then falls, so no single linear ranking function
   exists; the loop is ranked by the auto-synthesized 2-phase nested
   pair <y + 1, x> (f1 strictly decreases; once f1 < 0, f2 = x
   decreases and is bounded). Verify with:  --terminates auto
   The vassert keeps it self-checking. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int x, int y){}

int mainQ(int x, int y){
    while (x > 0) {
        x = x + y;
        y = y - 1;
    }
    vtrace1(x, y);
    vassert(x <= 0);
    return x;
}
