/* symex feature test: global variables — zero-initialized without an
   initializer (C static storage), explicit initializers, persistence
   across statements, and writes from inlined helper calls (the only
   shared state without pointers). All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int t, int g){}

int g;              /* implicitly 0 */
int total = 10;

void add(int k){
    total = total + k;
    g = g + 1;
}

int mainQ(int x, int y){
    vassert(g == 0 && total == 10);

    add(5);
    add(7);
    vassert(total == 22 && g == 2);   /* helper writes persist */

    total = total + x;
    vassert(total == 22 + x);

    vtrace1(total, g);
    return total;
}
