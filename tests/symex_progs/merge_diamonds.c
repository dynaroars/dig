/* symex feature test: state merging (merge_states) — six sequential
   if/else diamonds yield 16 feasible paths normally (the conditions per
   variable are monotone) but merge to a single state with If-valued
   variables; the vassert holds either way. TestStateMerging checks the
   16-vs-1 path counts. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int s){}

int mainQ(int a, int b){
    int s = 0;
    if (a > 0) { s = s + 1; } else { s = s - 1; }
    if (b > 0) { s = s + 1; } else { s = s - 1; }
    if (a > 1) { s = s + 1; } else { s = s - 1; }
    if (b > 1) { s = s + 1; } else { s = s - 1; }
    if (a > 2) { s = s + 1; } else { s = s - 1; }
    if (b > 2) { s = s + 1; } else { s = s - 1; }
    vassert(s >= -6 && s <= 6);
    vtrace1(s);
    return s;
}
