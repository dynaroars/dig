/* symex feature test: preprocessing — #define constants and function-like
   macros are expanded via cpp before parsing (includes are stripped
   first, so no system headers are pulled in). All vasserts must be
   valid. Skipped by the test runner if cpp is not installed. */
#define N 4
#define DOUBLE(a) ((a) + (a))

void vassume(int b){}
void vassert(int b){}
void vtrace1(int s, int x){}

int mainQ(int x, int y){
    int s = 0;
    int i;
    for (i = 0; i < N; i++) { s = s + 1; }
    vassert(s == N);
    vassert(DOUBLE(x) == 2 * x);
    vtrace1(s, x);
    return s;
}
