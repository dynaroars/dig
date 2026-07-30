/* symex feature test: non-termination proving — for any input with
   x >= 1 the loop runs forever (x only grows). --nonterm proves this
   by synthesizing the recurrent set {x >= 1}: it contains the
   reachable state x = 1, implies the guard, and every iteration stays
   inside it, so the printed diverging input is a genuine witness
   (exit code 1). The vassert self-checks the terminating inputs. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int x, int y){}

int mainQ(int x, int y){
    while (x > 0) {
        x = x + 1;
    }
    vtrace1(x, y);
    vassert(x <= 0);
    return x;
}
