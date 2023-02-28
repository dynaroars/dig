
/*
Arithmetic Algorithms
http://www.lsi.upc.edu/~erodri/webpage/polynomial_invariants/list.html : Enric Carbonell 'sinvariants
*/


void cohendiv_dummy(int x, int y, int q, int a, int b,int r){}
int cohendiv(int x, int y){
  //Cohen's integer division
  //returns x % y
  assert(x>0 && y>0);
  int q=0;
  int r=x;

  printf("#inv: r>=y*a && b==y*a && x==q*y+r && r>=0\n");
  printf("x y q a b r\n");
  while( r>=y ) {
    int a=1;
    int b=y;
      
    while (r>= 2*b){
      a = 2*a;
      b = 2*b;

      assert(r>=y*a && b==y*a && x==q*y+r && r>=0);
      printf("%d %d %d %d %d %d\n",x,y,q,a,b,r);
      cohendiv_dummy(x,y,q,a,b,r);

      if (r == y*a){
        printf("#get here\n");
      }
    }
    r=r-b;
    q=q+a;
  }

  assert(r == x % y);
  assert(q == x / y);
  return q;
}

void divbin_1_dummy(int A, int B,int q,int b, int r){}
void divbin_2_dummy(int A, int B,int q,int b, int r){}
int divbin (int A, int B){
  //binary division algorithm, by Kaldewaij
  //returns A//B
  //tvn: 2 whiles

  assert(A > 0 && B > 0);
  int q = 0;
  int r = A;
  int b = B;

  //printf("#inv_l1: don't care");
  //printf("A B q b r\n");
  while(r>=b){
    b=2*b;
    assert(q == 0 && r == A  &&  A >= 0  &&  B > 0);
  }

  printf("#inv_l2: A == q*b + r && r >= 0 && B > 0 &&  b > r\n");
  printf("A B q b r\n");
  while(b!=B){
    q = 2*q;
    b = b/2;
    if (r >= b) {
      q = q + 1;
      r = r - b;
    }
    assert(A == q*b + r && r >= 0  &&  B > 0  &&  b > r);
    printf("%d %d %d %d %d\n",A,B,q,b,r);
    divbin_2_dummy(A,B,q,b,r);
  }
  
  assert(q==A/B);
  assert(r==A%B);
  
  return q;
}

void hard_dummy(int d1, int A, int D, int p, int r){}
int hard(int A, int D) {
  //hardware integer division program, by Manna
  //returns q==A//D

  int r,d1,p,q;

  r=A;
  d1=D;
  p=1;
  q=0;

  while ( r>= d1 ){
    assert( A >= 0 && D > 0 && q == 0 && r == A && d1 == D*p );
    
    d1=2*d1;
    p=2*p;
  }

  printf("#inv: d1 == D*p, A == q*D+r");
  printf("d1 A D p r\n");
  while(p!=1){
    d1=d1/2;
    p=p/2;
      
    if(r>=d1){
      r=r-d1;
      q=q+p;
    }

    assert( D > 0 && A == q*D+r && d1 > r && r >= 0 && d1 == D*p );
    printf("%d %d %d %d %d\n", d1, A,D, p, r);
    hard_dummy(d1, A,D, p, r);
  }

  assert(r == A % D);
  assert(q == A / D);

  return q;
}

void mannadiv_dummy(y1,y2,y3,x1,x2){}
int mannadiv (int x1, int x2){
  //Division algorithm from
  //"Z. Manna, Mathematical Theory of Computation, McGraw-Hill, 1974"
  //return x1 // x2

  int y1,y2,y3;
  y1 = 0;
  y2 = 0;
  y3 = x1;
  
  printf("#inv: y1* x2 + y2 + y3 == x1\n");
  printf("y1 y2 y3 x1 x2 \n");
  while(y3 != 0) {

    if (y2 + 1 == x2) {
      y1 = y1 + 1;
      y2 = 0;
      y3 = y3 - 1;
    }
    else {
      y2 = y2 + 1;
      y3 = y3 - 1;
    }

    assert(y1* x2 + y2 + y3 == x1 );
    printf("%d %d %d %d %d\n",y1,y2,y3,x1,x2);
    mannadiv_dummy(y1,y2,y3,x1,x2);
  }

  assert(y1 == x1 / x2);
  return y1;
}

void wensley_dummy(float x, float y, float t, float z, 
                   float d, float u, float v){}
float wensley (float x, float y, float t){
  /* Wensley's algorithm for real division */
  //from http://www.cs.indiana.edu/classes/c241-john/post/Wensley.pdf
  /*
    some inputs don't work properly due to floating point imprecision
    e.g., wensley 0.85 0.93 0.02
    u 0.813750, z 0.875000, y 0.930000
    even though  0.813750 == 0.875000 *  0.93000,
    computer gives 0.813750 < 0.875000 *  0.93000
   */
  
  assert(0 <= x);
  assert(x<y);
  assert(y <= 1);
  
  float z,d,u,v;
  z = 0.0;
  d = 1.0;
  u = 0.0;
  v = y/2.0;

  printf("#inv: yz <= x & u >= z*y & v == d/2.0*y\n");
  printf("x y t z d u v\n");
  while (d > t){
    d = d/2.0;

    if (u + v <= x) {
      z = z + d; 
      u = u + v; 
    }
    v = v/2.0;

    assert(x >= y*z);  //ineq
    assert(u >= y*z);
    assert(x/y < z + d);
    assert(2.0*v == d*y);
    printf("%g %g %g %g %g %g %g\n",x, y, t, z, d, u, v);
    wensley_dummy(x, y, t, z, d, u, v);
  }

  assert(z <= x/y &&  x/y < z + t);
  return z;
}



void sqrt1_dummy(int a, int n,int t,int s){}
int sqrt1(int n){
  /* computing the floor of the square root of a natural number */
     
  int a,s,t;
  a=0;
  s=1;
  t=1;

  printf("#inv: a^2 <= n && t == 2*a + 1 && s == (a + 1)^2\n");
  printf("a n t s\n");
  while ( s <= n ){
    a=a+1;
    t=t+2;
    s=s+t;

    assert(a*a <= n);
    assert(t == 2*a + 1);
    assert(s == ( a + 1 ) * (a+1));
    printf("%d %d %d %d\n",a,n,t,s);
    sqrt1_dummy(a,n,t,s);
  }

  assert(a==(int)floor(sqrt(n)));
  return a;
}

void dijkstra_dummy(int r, int p, int n, int q, int h){}
int dijkstra(int n){
  /* program computing the floor of the square root, by Dijkstra */
  int p,q,r,h;

  p=0;
  q=1;
  r=n;
  
  while (q<=n){
    q=4*q;
    assert(   n >= 0   &&   p == 0   &&   r==n );
  }

  printf("#inv: r < 2*p + q,  p*p + r*q == n*q\n");
  printf("r p n q h\n");
  while (q!=1){
    q=q/4;
    h=p+q;
    p=p/2;
    if (r>=h){
      p=p+q;
      r=r-h;
    } 

    assert(r >= 0   && r < 2*p + q &&  p*p + r*q == n*q); 
    printf("%d %d %d %d %d\n",r,p,n,q,h);
    dijkstra_dummy(r,p,n,q,h);
  }

  assert(p == (int)floor(sqrt(n)));
  return p;
}


void z3sqrt_dummy(float a, float err, float r, float p, float q){}
float z3sqrt (float a, float err){
  //program for computing square roots, by Zuse
  //todo: seems to work only when a <= 4
  //todo: cannot get invs because of rounding err
  //todo: ask newsgroup or something ?

  assert( a>= 1.0 && err > 0.0 );

  float r,q,p;

  r = a-1.0;
  q = 1.0;
  p = 1.0/2.0;
  
  printf("#inv: q*q + 2*r*p == a && err > 0 && p >= 0 && r >= 0\n");
  printf("a err r p q\n");

  while ( 2.0*p*r >= err ){
    if ( 2.0*r-2*q-p >= 0.0 ){
      r = 2.0*r-2.0*q-p;
      q = q+p;
      p = p/2.0;
    }
    else{
      r = 2.0*r;
      p = p/2.0;
    }
    
    //tvn:  changed to 'q*q + 2.0*r*p >= a' from '=='
    assert(q*q + 2.0*r*p == a);
    assert(err > 0.0);
    assert(p >= 0.0);
    assert(r >= 0.0 );
    printf("%f %f %f %f %f\n",a,err,r,p,q);
    z3sqrt_dummy(a,err,r,p,q);
  }

  assert( pow(q,2) <= a);
  assert( pow(q,2)+err >= a );
  //post( q^2 >= a && q^2+err < a );
  return q;
  
}


void freire1_dummy(float a,float x,int r){}
int freire1 (float a ){
  //algorithm for finding the closest integer to the square root,
  //from  www.pedrofreire.com/crea2_en.htm?

  float x;
  int r;

  x=a/2.0;
  r=0.0;

  printf("#inv: a == 2*x + r*r - r   &&   x>0\n");
  printf("a x r\n");
  while( x>r ){
    x=x-r;
    r=r+1.0;
    
    assert(a == 2.0*x + r*r - r   &&   x>0.0);
    printf("%g %g %d\n",a,x,r);
    freire1_dummy(a,x,r);
  }

  assert(r==(int)round(sqrt(a)));

  return r;
}

void freire2_dummy(float a,float x,float s, int r){}
int freire2(float a){
  //algorithm for finding the closest integer to the cubic root,
  //from www.pedrofreire.com/crea2_en.htm? */ 
  //a is a float

  float x,s;
  int r;
  
  x=a;
  r=1;
  s=3.25;

  printf("#inv: 4*r*r*r - 6*r*r + 3*r + 4*x - 4*a == 1, -12*r*r + 4*s== 1\n");
           
  printf("a x s r\n");
  while ( x-s > 0.0){
    x = x - s;
    s = s + 6 * r + 3;
    r = r + 1;

    assert(4*r*r*r - 6*r*r + 3*r + 4*x - 4*a == 1);
    assert(-12*r*r + 4*s== 1);
    assert(x>0);
    printf("%g %g %g %d\n",a,x,s,r);
    freire2_dummy(a,x,s,r);
  }

  assert(r == (int)round(pow(a,(1.0/3.0))));
  return r;
}


float mygcd_n(float a,float b) {
  //can take neg inputs (e.g., a = -2, b = -8)
  float x,r;
  a=(float) (int)(fabs(a));
  b=(float) (int)(fabs(b));
  if (a>1e10 || b>1e10) return 1;
  if (a==0 || b==0) return 1;
  if (a<b) {
    x=a; a=b; b=x;
  }
  do {
    r=a-b*(int)(a/b);
    a=b; b=r;
  } while (fabs(r)>1e-10);
  return a;
}

int mygcd (int x, int y){
  int a,b,p,q,r,s;

  a=x;
  b=y;
  p=1;
  q=0;
  r=0;
  s=1;
  
  while( b!=0 ) {
    int c,k;
    
    c=a;
    k=0;
    
    while( c>=b ){
      c=c-b;
      k=k+1;
    }
    

    a=b;
    b=c;
    
    int temp;
    
    temp=p;
    p=q;
    q=temp-q*k;
    temp=r;
    r=s;
    s=temp-s*k;
  }
  return a;
}

void euclidex1_dummy(int a , int b , int c ,int p , 
                     int q, int r ,int s, int x ,int y ,
                     int k){}    

int euclidex1 (int x, int y){
  /* extended Euclid's algorithm */
  int a,b,p,q,r,s;

  a=x;
  b=y;
  p=1;
  q=0;
  r=0; 
  s=1;

  printf("#inv: a == k*b+c, a==y*r+x*p, b==x*q+y*s\n");
  printf("a b c p q r s x y k\n");
  
  while( b!=0 ) { 
    int c,k;
    
    c=a;
    k=0;

    while( c>=b ){
      c=c-b;
      k=k+1;

      assert(a == k*b+c);
      assert(a==y*r+x*p);
      assert(b==x*q+y*s );
      printf("%d %d %d %d %d %d %d %d %d %d\n",
             a ,b ,c ,p , q,r ,s, x ,y ,k);
      euclidex1_dummy(a ,b ,c ,p , q,r ,s, x ,y ,k);
    }


    a=b;
    b=c;

    int temp;
    temp=p;
    p=q;
    q=temp-q*k;
    temp=r;
    r=s;
    s=temp-s*k;
  }

  assert(mygcd(x,y)==y*r+x*p );

  return a;
}


void euclidex2_dummy(int a, int b,int y,int r,int x,int p,int q, int s){}
int euclidex2 (int x, int y){
  /* extended Euclid's algorithm */
  int a,b,p,q,r,s;
    
  a=x;
  b=y;
  p=1;
  q=0;
  r=0;
  s=1;
  
  printf("#inv:  a == y*r + x*p, b == x*q + y*s \n");
  printf("a b y r x p q s\n");
  
  while(a!=b) { 
    if (a>b) {a = a-b; p = p-q; r=r-s;}
    else {b = b-a; q = q-p; s = s-r;}

    assert(a == y*r + x*p);
    assert(b == x*q + y*s);
    printf("%d %d %d %d %d %d %d %d\n",a,b,y,r,x,p,q,s);
    euclidex2_dummy(a,b,y,r,x,p,q,s);
  }

  return a;
}


void euclidex3_dummy(int a,int b,int y,int r,int x,int p,
                     int q,int s,int d,int v, int k, int c){}
int euclidex3 (int x, int y){
  /* extended Euclid's algorithm */
  int a,b,p,q,r,s;

  a=x; b=y;  p=1;  q=0;  r=0;   s=1;

  assert(a==y*r+x*p);
  assert(b==x*q+y*s);

  printf("#inv: a==y*r+x*p, b==x*q+y*s, a==k*b+c, v==b*d, d*a==v*k+d*c\n");
  printf("a b y r x p q s d v k c\n");
  while( b!=0 ) { 
    int c,k;
    c=a;
    k=0;
      
    while( c>=b ){
      int d,v;
      d=1;
      v=b;
        
      while ( c>= 2*v ) {
        d = 2*d;
        v = 2*v;

        assert(a==y*r+x*p);
        assert(b==x*q+y*s);
        assert(a==k*b+c);
        assert(v==b*d);
        assert(d*a == v*k + d*c);
        printf("%d %d %d %d %d %d %d %d %d %d %d %d\n", 
               a, b, y, r, x, p, q, s, d, v, k, c);
        euclidex3_dummy(a, b, y, r, x, p, q, s, d, v, k, c);
      }
      c=c-v;
      k=k+d;

      assert(a==y*r+x*p && b==x*q+y*s && a==k*b+c );
             
    }
      
    a=b;
    b=c;
    int temp;
    temp=p;
    p=q;
    q=temp-q*k;
    temp=r;
    r=s;
    s=temp-s*k;
  }
      
  assert(mygcd(x,y)==y*r+x*p );
      
  return a;
}
    

void lcm1_dummy(int a, int b, int x, int y, int u, int v){}
int lcm1(int a, int b){
  /* algorithm for computing simultaneously the GCD and the LCM, 
     by Sankaranarayanan */
  /*tvn: 2 whiles*/

  int x,y,u,v;

  x=a;
  y=b;
  u=b;
  v=0;
  
  assert(x*u + y*v == a*b );
  printf("#inv: x*u + y*v == a*b\n");
  printf("a b x y u v\n");
  while(x!=y) {

    while (x>y){
      x=x-y;
      v=v+u;
    }
    
    while (x<y){
      y=y-x;
      u=u+v;
    }

    assert(x*u + y*v == a*b );
    printf("%d %d %d %d %d %d\n", a,b,x,y,u,v); //todo: printf("l2")
    lcm1_dummy(a,b,x,y,u,v);
  }

  //x==gcd(a,b)
  return u+v; //lcm
}



void lcm2_dummy(int a,int b,int x,int y,int u,int v){}
int lcm2 (int a, int b){
  /* algorithm for computing simultaneously the GCD and the LCM, by Dijkstra */
  int x,y,u,v;

  x=a;
  y=b;
  u=b;
  v=a;

  printf("#inv: x*u + y*v == 2*a*b\n");
  printf("a b x y u v\n");
    
  while(x!=y) { 
    if (x>y){
      x=x-y;
      v=v+u;
    }
    else {
      y=y-x;
      u=u+v;
    }
    assert(x>0   &&   y>0   &&   x*u + y*v == 2*a*b  );
    printf("%d %d %d %d %d %d\n", a,b,x,y,u,v);
    lcm2_dummy(a,b,x,y,u,v);
  }

  //x==gcd(a,b)
  return (u+v)/2; //lcm
}


void prodbin_dummy(int a, int b, int x, int y, int z){}
int prodbin (int a,int b){
  /* algorithm for computing the product of two natural numbers */
  /* shift_add */
  int x,y,z;
  
  x = a;
  y = b;
  z = 0;
  
  printf("#inv:  z+x*y==a*b\n");
  printf("a b x y z\n");

  while( y!=0 ) { 
    if (y%2 ==1 ){
      z = z+x;
      y = y-1;
    }
    x = 2*x;
    y = y/2;

    assert( z+x*y==a*b );
    printf("%d %d %d %d %d\n", a,b,x,y,z);
    prodbin_dummy(a,b,x,y,z);
  }
  assert(z == a*b);
  return z; 
}


void prod4br_dummy(int x, int y, int a, int b, int p, int q){}
int prod4br(int x, int y){
  /* algorithm for computing the product of two natural numbers */
  int a,b,p,q;
  
  a = x;
  b = y;
  p = 1;
  q = 0;
  printf("#inv: q+a*b*p==x*y\n");
  printf("x y a b p q\n");

  while(a!=0 && b!=0 ) { 
    
    if (a % 2 ==0 && b % 2 ==0 ){
      a =a/2;
      b = b/2;
      p = 4*p;
    }
    else if (a % 2 ==1 && b % 2 ==0 ){
      a =a-1;
      q = q+b*p;
    }
    else if (a % 2 ==0 && b % 2 ==1 ){
      b =b-1;
      q = q+a*p;
    }
    else {
      a =a-1;
      b =b-1;
      q = q+(a+b+1)*p;  /*dammit I am good ---  was (a+b-1)*/
    }

    assert( q+a*b*p==x*y );
    printf("%d %d %d %d %d %d\n", x, y, a, b, p, q);
    prod4br_dummy(x, y, a, b, p, q);

  }

  assert(q == x*y);
  return q; 
}

void fermat1_dummy(int A, int R, int u, int v, int r){}
int fermat1(int A, int R){
  // program computing a divisor for factorisation, by Knuth 4.5.4 Alg C ?
  /*tvn: run forever -- but ok because we can just capture those values*/
  //tvn: 2 whiles

  int u,v,r;
  u=2*R+1;
  v=1;
  r=R*R-A;
  
  assert( 4*(A+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && A>=1 );
  printf("#inv: 4*(A+r) = u*u-v*v-2*u+2*v, v mod 2 = 1, u mod 2 = 1, A >= 1\n");
  printf("A R u v r\n");

  int ctr = 0;
  while ( r!=0 && ctr < 250){
    ctr++;
    while ( r<0 ) {
      r=r-v;
      v=v+2;

    }
    
    while ( r<0 ){
      r=r+u;
      u=u+2;
    }

    assert(4*(A+r)==u*u-v*v-2*u+2*v);
    assert(v%2==1 && u%2==1 && A>=1 );
    printf("%d %d %d %d %d\n", A, R, u, v, r);
    fermat1_dummy(A, R, u, v, r );    
  }
  
  assert( u!=v );
  return((u-v)/2);
}

void fermat2_dummy(int A, int R, int u, int v, int r){}
int fermat2(int A, int R){
  /* program computing a divisor for factorisation, by Bressoud */
  int u,v,r;
    
  u=2*R+1;
  v=1;
  r=R*R-A;

  assert( 4*(A+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && A>=1 );
  printf("#inv: 4*(A + r) == u*u - v*v - 2*u + 2*v &&  v mod 2 == 1 && u mod 2 == 1   &&   A >= 1 \n");
           
  printf("A R u v r\n");
  
  int ctr = 0;
  while (r!=0 && ctr < 250){
    ctr++;
    if (r>0) {
      r=r-v;
      v=v+2;
    }
    else{
      r=r+u;
      u=u+2;
    }

    assert(4*(A + r) == u*u - v*v - 2*u + 2*v);
    assert(v % 2 == 1   &&   u % 2 == 1   &&   A >= 1  );
    printf("%d %d %d %d %d\n", A, R, u, v, r);
    fermat2_dummy(A, R, u, v, r);

  }
  
  assert(u!=v);
  return((u-v)/2);
}

void knuth_dummy(int n, int d1, int r, int k, int q, int d, 
                 int s, int t){}
int knuth (int n, int d1){
  //algorithm searching for a divisor for factorization, by Knuth
  //had to comment out one of the invariants

  int r,k,q,d,s,t;

  d=d1;
  r= n % d;

  if (d <= 2){
    printf("d - 2 <= 0.  Use a diff val\n");
    return 0;
  }
  k=n % (d-2);
  q=4*(n/(d-2) - n/d);
  s=sqrt(n);

  printf("#inv: d*d*q - 4*r*d + 4*k*d - 2*q*d + 8*r == 8*n  &&  d mod 2 == 1\n");
  printf("n d1 r k q d s t\n");

  while((s>=d)&&(r!=0)){
    if (2*r-k+q<0){
      t=r;
      r=2*r-k+q+d+2;
      k=t;
      q=q+4;
      d=d+2;
    } 
    else if ((2*r-k+q>=0)&&(2*r-k+q<d+2)){
      t=r;
      r=2*r-k+q;
      k=t;
      d=d+2;
    }
    else if ((2*r-k+q>=0)&&(2*r-k+q>=d+2)&&(2*r-k+q<2*d+4)){
      t=r;
      r=2*r-k+q-d-2;
      k=t;
      q=q-4;
      d=d+2;
    }
    else {/* ((2*r-k+q>=0)&&(2*r-k+q>=2*d+4)) */
      t=r;
      r=2*r-k+q-2*d-4;
      k=t;
      q=q-8;
      d=d+2;
    }

    assert(d*d*q - 4*r*d + 4*k*d - 2*q*d + 8*r == 8*n);
    printf("%d %d %d %d %d %d %d %d\n", n, d1, r, k, q, d, s, t);
    knuth_dummy(n, d1, r, k, q, d, s, t);
  }
  
  return d;
}

void cohencu_dummy(int a, int n, int x,int y,int z){}
int cohencu(int a) {
  /* printing consecutive cube, by Cohen */
  int n,x,y,z;

  n=0; x=0; y=1; z=6;
  
  printf("#inv: z == 6*n + 6 && y == 3*n*n + 3*n + 1   &&   x == n*n*n\n");
  printf("a n x y z\n");
  
  while(n<=a){
    n=n+1;
    x=x+y;
    y=y+z;
    z=z+6;
    
    assert(z == 6*n + 6   &&
           y == 3*n*n + 3*n + 1   &&
           x == n*n*n  );
    printf("%d %d %d %d %d\n", a,n,x,y,z);
    cohencu_dummy(a,n,x,y,z);
  }

  return x;
}



int f1(int a){
  assert (a >= 0);
  int b = 0; 
  int c = 1;

  while (c*c <= a){
    c = 2*c;
  }

  while (c >= 2){
    
    c = c/2;
    if ((int)pow((b + c),2.0) <= a){
      assert ((int)pow((2*b + c),2.0) <= 4*a);
      b = b + c;
    }
    else{
      printf("%d %d %d, %d , %d\n",a,b,c,(int)pow((2*b + c),2.0),4*a+4);
      assert ((int)pow((2*b + c),2.0) >= 4*a+4);
    }
  }

  assert(b == (int)floor(sqrt(a)));
  return b;
}


void readers_writers_dummy(int r, int w, int k, int a1, int a2, int k0){}
int readers_writers(int a1, int a2, int k0){
  //generalization of the readers-writers problem, by Sankaranarayanan
  assert ( a1 >= 0 && a2 >= 0 && k0 >=0 ) ;
  int r,w,k;
  r = 0;
  w = 0;
  k = k0;

  int ctr = 0;
  printf("#inv: r*a1 + w*a2 + k == k0 && r*w==0\n");
  printf("r w k a1 a2 k0\n");

  while(ctr < MAX_LOOP){ 
    ctr++;

    if(w==0){
      r = r+1;
      k = k-a1;
    }
    if(r==0){
      w = w+1;
      k = k-a2;
    }
    if( w==0){
      r = r-1;
      k = k+a1;
    }
    if(r==0){
      w = w-1;
      k = k+a2;
    }

    assert(r*a1 + w*a2 + k == k0);
    assert(r*w==0);
    printf("%d %d %d %d %d %d\n",r, w, k, a1, a2, k0);
    readers_writers_dummy(r, w, k, a1, a2, k0);
  }
  return k;
}

void petter(k){  
  //geo
  int x = 0;
  int y = 0;
  printf("x y k\n");
  while( y != k ){
    x = x + pow(y,5);
    y = y + 1;
    printf("%d %d %d\n",x,y,k);
  }
}


/*from petter"s master thesis
  http://www2.cs.tum.edu/~petter/da/da.pdf*/
int geoReihe1 (int z, int k){
  //todo: probably not use, since no loop inv
  assert(k>0);
  int x = 1;
  int y = z;
  int k1 = 1;

  printf("#inv: 1 + x - y ==0\n");
  printf("x y z\n");
  while (k1 < k){
    k1 = k1 + 1;
    x = x*z + 1;
    y = z*y;

    x = x *(z -1);
    assert(1 + x - y == 0);  //invariant, equation
    printf("%d %d %d\n",x,y,z);
    assert(y == pow(z,k));
  }



  //note the paper says x = (z-1)* sum(z^k)[k=0..k] is not correct
  //this code produces  x = (z-1)* sum(z^k)[k=0..k-1]
  //assert(x == (z-1) * sum([z**k_ for k_ in range(k)]));
  //return x,y
  return x;
}

void geoReihe2_dummy(int x, int y, int z, int k){}
int geoReihe2(int z, int k){
  assert (k>0);
  int x = 1;
  int y = 1;
  int c = 1;

  printf("#inv: 1+x*z-x-z*y==0\n");
  printf("x y z k\n");
  while (c < k){
    c = c + 1;
    x = x*z + 1;
    y = y*z;

    assert(1+x*z-x-z*y==0);// #invariant, #equation
    printf("%d %d %d %d\n",x, y, z, k);
    geoReihe2_dummy(x, y, z, k);
  }
  
  assert(y == pow(z,(k-1)));
  //assert(x == sum([z**k_ for k_ in range(k)]))
  //return x,y
  return x;
}

void geoReihe3_dummy(int x, int y, int z, int a, int k){}
int geoReihe3(int z,int a, int k){
  int x = a;
  int y = 1;
  int c = 1;

  printf("#inv:zx-x+a-azy == 0\n");
  printf("x y z a k\n");
  while (c < k){
    c = c + 1;
    x = x*z + a;
    y = y*z;

    assert(z*x-x+a-a*z*y == 0);// #invariant, equation
    printf("%d %d %d %d %d\n", x, y, z, a,k) ;
    geoReihe3_dummy( x, y, z, a,k);
  }

  assert(y == pow(z,(k-1)));
  //assert(x == sum([a*(z**k_) for k_ in range(k)]));
  //return x,y
  return x;
}

/*
  # // yielding x=y
  # //todo: too easy, not worth doing
  # def potSumm1 ( String []
  # y = 0
  # x = 0
  # while ( args !=null){
  # y=y +1
  # x=x +1
*/

void potSumm2_dummy(int x, int y, int k){}
int potSumm2(int k){
  int y = 0;
  int x = 0;
  int c = 0;

  printf("#inv: 2*x-y**2-y == 0\n");
  printf("x y k\n");
  while (c < k){
    c = c + 1;
    y=y +1;
    x=x+y;

    assert(2*x-pow(y,2)-y == 0);//  #invariant equation
    printf("%d %d %d\n",x,y,k);
    potSumm2_dummy(x,y,k);
  }

  assert(y == 1*k);
  //assert(x == sum(range(k+1)))
  
  //return x,y
  return x;
}

void potSumm3_dummy(int x, int y, int k){}
int potSumm3(int k){
  int y = 0;
  int x = 0;
  int c = 0;
  
  printf("#inv: 6*x-2*y**3-3*y**2-y == 0\n");
  printf("x y k\n");
  
  while (c < k){
    c = c + 1;
    y=y +1;
    x=y*y+x;

    assert(6*x-2*pow(y,3)-3*pow(y,2)-y == 0);// #invariant equation
    printf("%d %d %d\n",x,y,k);
    potSumm2_dummy(x,y,k);
  }

  assert(y == 1*k);
  //assert(x == sum(k_**2 for k_ in range(k+1)))

  //return x,y
  return x;
}
  

void potSumm4_dummy(int x,int y,int k){}
int potSumm4 (int k){
  int y = 0;
  int x = 0;
  int c = 0;
  
  printf("#inv: 4*x-y**4-2*y**3-y**2 == 0\n");
  printf("x y k");
  
  while (c < k){
    c = c +1 ;
    y=y +1;
    x=y*y*y+x;

    // #invariant equation
    assert(4*x-pow(y,4)-2*pow(y,3)-pow(y,2) == 0);
    printf("%d %d %d\n",x,y,k);
  }

  assert(y == 1*k);
  //assert(x == sum(k_**3 for k_ in range(k+1)))
  //return x,y
  return x;
}







int knuth_test(int u, int v){
  return u;
}

int knuth_gcd_n(int *arr, int n){
  //Knuth 4.5.2 Alg C
  //gcd of n integers

  int d=arr[n-1];
  int k = n-1;
  while(d != 1 && k > 0){
    d = knuth_gcd_bin(d,arr[k-1]);
    k = k - 1;
  }
  return d;
}


int knuth_gcd_bin(int u, int v){
  //Knuth 4.5.2 Alg B
  //binary gcd

  int u_inp = u;
  int v_inp = v;
  
  int g = 1;
  while(myeven(u) && myeven(v)){
    g=2*g;
    u = u / 2;
    v = v / 2;
  }
  
  while(u > 0){
    if (myeven(u)){
      u = u / 2;
    }
    else if (myeven(v)){
      v = v / 2;
    }
    else{
      int t = abs(u-v) / 2;
      if (u < v){
        v = t;
      }
      else{
        u = t;
      }
    }
  }

  assert(v*g==mygcd(u_inp,v_inp));
  return v*g;
}


int knuth_gcd_euclid(int u, int v){
  // Knuth 4.5.2 Alg A
  // Euclid's gcd
  int r = 0; 
  while(v != 0){
    r = u % v;
    u = v;
    v = r;
  }
  
  assert(u==mygcd(u,v));
  return u;
}


int knuth_factor_fermat(int N){
  //Kuth 4.5.4 C
  //input an odd number N returns the largest factor of N <= sqrt(N)
  //using fermat method
  assert(N % 2 == 1); //N has to be an odd number
   
  int x = 2*floor(sqrt(N)) + 1;
  int y = 1;
  int r = pow(floor(sqrt(N)),2) - N;
  while(r != 0){
    while(r<0){
      r = r + x ;
      x = x + 2 ;
    }
    
    while(r>0){
      r = r - y ;
      y = y + 2 ;
    }
    assert(4*(N+r) == pow(x,2) - pow(y,2) - 2*x + 2*y); //inv
    
  }
  
  int res = (x-y)/2;
  assert((float)res<=sqrt(N));
  return res;

  
}


int f_rand(int x,int n){
  return (int)(pow(x,2)+1) % n;
}

int knuth_factor_rho(int N){
  //4.5.4 B   Factoring by the rho method
  //tvn: don't think it is correct .. yet

  if(myisprime(N)) return 1;

  int x= 2;
  int y= 2;
  int d= 1;
  
  while(d == 1)  {
    x = f_rand(x,N);
    y = f_rand(f_rand(y,N),N);
    d = mygcd(abs(x - y), N);
  }
  if (d == N){
    return -1;
  }
  else{
    return d;
  }
  
}


