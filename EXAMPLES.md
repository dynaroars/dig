# Examples Demonstrating DIG

- Most examples taken from [TSE'21](https://dynaroars.github.io/pubs/nguyen2021using.pdf) paper


## General Nonlinear and Linear Loop Invariants
 - examples taken from [nla](./benchmark/c/nla) dir

### CohenDiv
 - nested loop
 - inferred loop invariants of the two loops
 - nonlinear equalities and several linear inequalities

```c
int cohendiv(int x, int y){
    vassume(x >= 1 && y >= 1);
    
    int q=0;
    int r=x;
    int a=0;
    int b=0;
    while(1) {
        // DIG
        // q*y + r == x; a*y == b
        // b <= x;  y <= r; 0 <= q;  1 <= b; 1 <= y
        
	    if(!(r>=y))
	        break;
	    a=1;
	    b=y;
	  
	    while (1){
            // DIG
            // x == q**y + r;  a**y == b
            // r <= y − 1 ; 0 <= r;  r <= x
            
	        if(!(r >= 2*b))
		    break;
	       
            a = 2*a;
	        b = 2*b;x
	    }
	
        r=r-b;
        q=q+a;
    }
    return q;
}
```


### Breseham
- drawing algorithm
- found nonlinear loop inv and postcondition 

```c
int breseham(int X, int Y){

    int v, x, y;
    v = 2 * Y - X;
    y = 0;
    x = 0;
    while (1) {
        // DIG: 2*Y*x - 2*X*y - X + 2*Y - v == 0
        vtrace1(X,Y, x,y,v);
        if (!(x <= X))
            break;
	
        if (v < 0) {
            v = v + 2 * Y;
	    } else {
            v = v + 2 * (Y - X);
            y++;
        }
	    x++;
    }
    // DIG: 2*Y*x - 2*x*y + 2*Y - v - x + 2*y + 1 == 0
    return 0;
}
```



## Complexity Analysis and Disjunctive invariants
 - show how nonlinear invariants can be useful to capture program complexity
 - examples taken from [complexity](./benchmark/c/complexity) dir
 - in the below, the `t` counter keeps track of executed instructions, and we want to find the relation between `t` and input values.

### `cav09_fig1a`
- simple program showing now nonlinear invariants give disjunction
- solving for `t` from the obtained invariant `m*t - (t*t) - 100*m + 200*t - 10000 == 0`
  - we get `t == m + 100` or `t == 100`
  
```c
int program(int m){
    int x = 0;
    int y = 0;
    int t = 0;
    while(x < 100){
	    if (y < m){
	        y++;
	    }
	    else{	       
	        x++;
	    }
	    t++;
    }

    
    //dig: m*t - (t*t) - 100*m + 200*t - 10000 == 0
    //solve for t: t == m + 100, t == 100
    return 0;
}
```




### tripple (`pldi_fig2`)
- tripple nested loops
- discovers postcond
  - `-N <= 0, -m <= 0, -n <= 0, n - t <= 0`
  - `N*N)*m*n + N*(m*m)*n - N*m*(n*n) - (m*m)*(n*n) - N*m*n*t + m*(n*n)*t + N*m*n - N*(n*n) - 2*m*(n*n) + N*n*t + m*n*t + (n*n)*t - n*(t*t) - (n*n) + n*t == 0`
  - `(N*N)*m*t + N*(m*m)*t - N*m*n*t - (m*m)*n*t - N*m*(t*t) + m*n*(t*t) + N*m*t - N*n*t - 2*m*n*t + N*(t*t) + m*(t*t) + n*(t*t) - (t*t*t) - n*t + (t*t) ==0` 
- Solve for t from the above equations we get the following 3 cases:
   1. `N = 0 => t = 0`    # when `N = 0`, no instruction executed
   2. `N-P <= 0 => t = P + M + 1`  # when `N <= P`, `P+M+1` instructions executed (linear in the inputs `M, P`) 
   3. ` N > P (-N+P < 0)  =>  t = N -M(P-N)`   # when `N > P`, `N-M(P-N)` instructions executed (quadratic in the inputs `M, N, P`, i.e., `O(N+MN)`) 

  
```c
int tripple(int M, int N, int P){
    vassume(0 <= M);
    vassume(0 <= N);
    vassume(0 <= P);
     
    int t = 0; // counter var
    int i = 0;
    int j = 0;
    int k = 0;
    while(i < N){
	    j = 0;  
	    while(j < M){	       
	        j = j + 1;
	        k = i;
	        t++;
	        while(k < P){		    
		        k = k + 1;
                t++;
            }
	        i = k;
	    }
	    i = i + 1;
	    t++;
    }
    
    //DIG:
    //-N <= 0, -m <= 0, -n <= 0, n - t <= 0,
    //(N*N)*m*n + N*(m*m)*n - N*m*(n*n) - (m*m)*(n*n) - N*m*n*t + m*(n*n)*t + N*m*n - N*(n*n) - 2*m*(n*n) + N*n*t + m*n*t + (n*n)*t - n*(t*t) - (n*n) + n*t == 0, (N*N)*m*t + N*(m*m)*t - N*m*n*t - (m*m)*n*t - N*m*(t*t) + m*n*(t*t) + N*m*t - N*n*t - 2*m*n*t + N*(t*t) + m*(t*t) + n*(t*t) - (t*t*t) - n*t + (t*t) == 0

    /*
      N = 0 => t = 0 
      N <= P (N-P <= 0) => t = P + M + 1
      N > P (-N+P < 0)  =>  t = N -M(P-N)  // -N +P < 0
    */

    return 0;
}

``` 


### `popl09_fig3_4`



## Disjunctive Invariants through Min/Max-Plus Relations




## Using Invariants to check Assertions
