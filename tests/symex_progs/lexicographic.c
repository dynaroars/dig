/* symex feature test: lexicographic termination — the inner counter y
   counts down, and only when it hits 0 does the outer counter x step
   (resetting y to an arbitrary unknown() value). No single linear
   expression decreases on every path, but the tuple <x, y> does
   lexicographically: y's path leaves x unchanged, x's path may reset
   y freely. Verify with:  --terminates "x ; y"
   The vassert keeps it self-checking. */
void vassume(int b){}
void vassert(int b){}
int unknown(void);
void vtrace1(int x, int y){}

int mainQ(int x, int y){
    vassume(y >= 0);
    while (x > 0 && y >= 0) {
        if (y > 0) { y = y - 1; }
        else       { x = x - 1; y = unknown(); }
    }
    vtrace1(x, y);
    vassert(x <= 0 || y < 0);
    return x;
}
