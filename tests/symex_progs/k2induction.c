/* symex feature test: k>1 induction — x alternates between 0 and -0
   conceptually, but from an arbitrary havoc state x = -x flips sign, so
   "x != 1" is NOT 1-inductive (havoc x = -1 breaks the step) yet IS
   2-inductive: two consecutive heads satisfying x != 1 force x != -1
   too, and after two flips x returns to itself. See TestKInduction.
   The bounded vasserts keep the program self-checking. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int x, int i){}

int mainQ(int n, int y){
    int x = 0;
    int i = 0;
    while (i < n) {
        x = -x;
        i = i + 1;
        vassert(x != 1);      /* bounded check of the same property */
    }
    vassert(x != 1);
    vtrace1(x, i);
    return x;
}
