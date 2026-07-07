/* symex feature test: switch with fallthrough, default, no-match fall-off,
   and break/continue interplay inside a loop (break exits the switch only;
   continue targets the loop). All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int r, int sum){}

int mainQ(int x){
    vassume(x >= 0 && x <= 5);

    int r = 0;
    switch (x) {
        case 0: r = 10; break;
        case 1:                    /* falls through to case 2 */
        case 2: r = 12; break;
        case 3: r = 13;            /* falls through into default */
        default: r = r + 100; break;
    }
    vassert(x != 0 || r == 10);
    vassert(!(x == 1 || x == 2) || r == 12);
    vassert(x != 3 || r == 113);
    vassert(x < 4 || r == 100);

    int nm = 0;
    switch (x) {                   /* no default: no-match falls off */
        case 0: nm = 1; break;
    }
    vassert(nm == (x == 0 ? 1 : 0));

    int sum = 0;
    for (int i = 0; i < 4; i++) {
        switch (i) {
            case 1: continue;      /* continue targets the for loop */
            case 3: break;         /* break exits the switch only */
        }
        sum += i;                  /* runs for i = 0, 2, 3 */
    }
    vassert(sum == 5);

    vtrace1(r, sum);
    return r;
}
