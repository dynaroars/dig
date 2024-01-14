# Examples Demonstrating the DIG Invariant Generator

- Most examples taken from our [TSE'21](https://dynaroars.github.io/pubs/nguyen2021using.pdf) paper


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
int cav09_fig1a(int m){
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
    
    //DIG: m*t - (t*t) - 100*m + 200*t - 10000 == 0
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
- DIG infered the nonlinear equality `m*n*t - m*(t*t) - n*(t*t) + (t*t*t) == 0` and a couple of inequalities  `m - t <= 0; n - t <= 0; -t <= 0`
  - solve for `t` from the equality, we get a disjunction `t == n` or ` t == m` or `t == 0` 
  - combining these three disjuncts with the obtained inequalities `t>= n` and `t >=m`, we get `t = max(n,m)`, which is the correct bound for this program

```c
int popl09_fig3_4(int n, int m){
    int x = 0;
    int y = 0;
    int tCtr = 0;
    while((x < n || y < m)){
	if(x < n){
	    x++;
	    y++;
	}
	else if(y < m){
	    x++;
	    y++;
	}
	else{
	    //assert(0);
	    break;
	}
	tCtr++;
    }
    vtrace_post(n, m, tCtr);
     
    //%%%traces: int n, int m, int t
    //DIG: m*n*t - m*(t*t) - n*(t*t) + (t*t*t) == 0, 
    //DIG: m - t <= 0, n - t <= 0, -t <= 0
    return 0;
}
```





## Disjunctive Invariants through Min/Max-Plus Relations

### strncpy
- simulates the C `strncpys` function to copy the first `n` chars from a null-terminated source to a destination buffer.
- in the following `s` represents length of the source buffer, `d` is the length of the destination buffer
- DIG obtained the invs `d >= min(n,s)`; `s >= min(d,n)`, which represent the disjunction
  - `(n >= s && d = s)  ||   (n < s ∧ d >= n)`
  - This captures the desired semantics of strncpy: if `n >= |s|`,
then the copy stops at the null terminator of `s`, which is
also copied to `d`, so d ends up with the same length as `s`. 
However, if `n < |s|`, then the terminator is not copied to `d`, so `|d| >= n`.

```c
int mylen(const int k,int arr[], const int arr_siz){
  int i = 0;
  for(; i < arr_siz; ++i){
    if (arr[i] == '\0'){return i;}
  }

  return arr_siz - 1 ;
  //return randrange_i(k, arr_siz - 1, INCLUDE);
}


void mk_rand_list(int arr[], const int arr_siz){
  int i = 0 ;
  for (;i< arr_siz; ++i){arr[i] = ' ';}


  int null_idx = randrange_i(0, arr_siz -1, INCLUDE);
  arr[null_idx]='\0';
}

void strncpy(int siz, int n){
	vassume (1 <= siz);
	vassume (0 <= n);
	vassume (n <= siz-1);
 
	int src[siz];
	int dst[siz];
	mk_rand_list(src, siz);
	mk_rand_list(dst, siz);

	int i = 0;
	while(i < n && src[i] != '\0'){
	    dst[i] = src[i];
	    i = i + 1;
	}
	while(i < n){
	    dst[i] = '\0';
	    i = i + 1;
	}

	int ls = mylen(n,src,siz);
	int ld = mylen(n,dst,siz);

	printf("l_post: n s d\n");
	printf("l_post: %d %d %d\n", n, ls, ld);

	//inv
	assert(!(n <= ls) || ld >= n);
	assert(!(n > ls) || ld == ls);

	/*
	  DIG:
	  11: lambda d,n,s: d >= min(n,s)  ***
	  12: lambda d,n,s: s >= min(d,n)  ***
	*/
	
}  
```



## Using Invariants to check Assertions
TODO 
