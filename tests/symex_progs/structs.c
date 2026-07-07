/* symex feature test: structs by value — tag structs, typedefs, nested
   structs, {…} initializers, whole-struct copy, field increments, and an
   array field. All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int x, int y){}

struct Inner { int v; };
struct Point { int x; int y; struct Inner in; };
typedef struct { int w; int h; } Rect;
struct Buf { int data[4]; int len; };

int mainQ(int u, int v){
    struct Point p;
    p.x = u;
    p.y = v;
    p.in.v = u + v;                 /* nested field */
    vassert(p.in.v == p.x + p.y);

    struct Point q;
    q = p;                          /* whole-struct copy */
    p.x = 99;                       /* later writes don't leak into q */
    vassert(q.x == u && q.in.v == u + v && p.x == 99);

    Rect r = {3, 4};                /* typedef + positional initializer */
    vassert(r.w * r.h == 12);
    r.w++;                          /* field increment statement */
    vassert(r.w == 4);

    struct Buf buf;                 /* array field */
    buf.len = 0;
    buf.data[0] = 42;
    buf.len++;
    vassert(buf.data[0] == 42 && buf.len == 1);

    vtrace1(q.x, r.w);
    return 0;
}
