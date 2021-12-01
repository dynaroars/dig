## NLA

### Bresenham
From "From Program Verification to Program Synthesis", Popl10, Srivasta et al

Computes and writes to tye output array `out` the discrete best-fit line from (0,0) to (X,Y), where the point is in the NE half-quadrant. The best-fit line is the one that does not divate more than half a pixel away from the realine,  i.e., `|y -(Y/X)x| <= 1/2`.  For efficiency, the algorithm computes the pixel values (x,y) of this best-fit line using on linear operations.  

Loop invariants:

```txt
Loop invariants
1. 2*Y*x - 2*X*y - X + 2*Y - v == 0
2. -y <= 0
3. -x + y <= 0
4. (y - 1) - max(Y, 0) <= 0
5. (x - 1) - max(X, 0) <= 0
```

## Min/Max Programs

### OddEven2
```text
Invariants (Post conds)
1. x1 - max(t0, t1) == 0
2. x0 - min(t0, t1) == 0
3. t1^2 - t1*x0 - t1*x1 + x0*x1 == 0
4. t0 + t1 - x0 - x1 == 0
```

### OddEven3
```text
Invariants (Post conds)
1. x2 - max(t0, t1, t2) == 0
2. t2^3 - t2^2*x0 - t2^2*x1 + t2*x0*x1 - t2^2*x2 + t2*x0*x2 + t2*x1*x2 - x0*x1*x2 == 0
3. t1^2 + t1*t2 + t2^2 - t1*x0 - t2*x0 - t1*x1 - t2*x1 + x0*x1 - t1*x2 - t2*x2 + x0*x2 + x1*x2 == 0
4. t0 + t1 + t2 - x0 - x1 - x2 == 0
5. min(t0, t1, t2) - x0 == 0
```

### OddEven4
```text
Invariants (Post conds)
1. x0 - min(t0, t1, t2, t3) == 0
2. t2^3 + t2^2*t3 + t2*t3^2 + t3^3 - t2^2*x0 - t2*t3*x0 - t3^2*x0 - t2^2*x1 - t2*t3*x1 - t3^2*x1 + t2*x0*x1 + t3*x0*x1 - t2^2*x2 - t2*t3*x2 - t3^2*x2 + t2*x0*x2 + t3*x0*x2 + t2*x1*x2 + t3*x1*x2 - x0*x1*x2 - t2^2*x3 - t2*t3*x3 - t3^2*x3 + t2*x0*x3 + t3*x0*x3 + t2*x1*x3 + t3*x1*x3 - x0*x1*x3 + t2*x2*x3 + t3*x2*x3 - x0*x2*x3 - x1*x2*x3 == 0
3. t1^2 + t1*t2 + t2^2 + t1*t3 + t2*t3 + t3^2 - t1*x0 - t2*x0 - t3*x0 - t1*x1 - t2*x1 - t3*x1 + x0*x1 - t1*x2 - t2*x2 - t3*x2 + x0*x2 + x1*x2 - t1*x3 - t2*x3 - t3*x3 + x0*x3 + x1*x3 + x2*x3 == 0
4. t0 + t1 + t2 + t3 - x0 - x1 - x2 - x3 == 0
5. max(t0, t1, t2, t3) - x3 == 0
6. x1 - max(t1, t2) <= 0
7. x1 - max(t0, t3) <= 0
8. x1 - max(t0, t1, 0) <= 0
9. min(t2, t3, 0) - x2 <= 0
10. min(t1, t3) - x2 <= 0
11. min(t0, t2) - x2 <= 0
12. min(t0, t1) - x2 <= 0
```