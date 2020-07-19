/*
NLA testsuite

Consists of small, nontrivial arithmetic programs.
Mostly from Enric Carbonell 's invariants website at 
http://www.lsi.upc.edu/~erodri/webpage/polynomial_invariants/list.html

Some programs are collected elsewhere
*/


void divbin_dummy_l0(int A, int B,int q,int b, int r){}
void divbin_dummy_l1(int A, int B,int q,int b, int r){}
void divbin_dummy_l2(int A, int B,int q,int b, int r){}
int divbin(int A, int B){
  /*
  binary division algorithm, by Kaldewaij
  returns A//B
  tvn: 2 whiles
  */

  printf("l_init: A B\n");
  printf("l_init: %d %d\n",A,B);

  assert(A > 0 && B > 0);
  int q = 0;
  int r = A;
  int b = B;


  while(r>=b){
    assert(q == 0 && r == A  &&  A >= 0  &&  B > 0);
    b=2*b;
  }
  printf("l2: A B q b r\n");
  printf("l2: %d %d %d %d %d\n",A,B,q,b,r);  
  divbin_dummy_l2(A,B,q,b,r);

  int ctr = 0;
  while(b!=B){

    assert(A == q*b + r && r >= 0);
    printf("l0: A B q b r dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d\n",A,B,q,b,r,ctr++);
    divbin_dummy_l0(A,B,q,b,r);

    q = 2*q;

    b = b/2;
    if (r >= b) {
      q = q + 1;
      r = r - b;
    }
  }
  
  assert(q==A/B);
  assert(r==A%B);
  printf("l1: A B q b r\n");
  printf("l1: %d %d %d %d %d\n",A,B,q,b,r);  
  divbin_dummy_l1(A,B,q,b,r);
  return q;
}

void cohendiv_dummy_l0(int x, int y, int q, int a, int b,int r){}
void cohendiv_dummy_l1(int x, int y, int q, int a, int b,int r){}
int cohendiv(int x, int y){
  //Cohen's integer division
  //returns x % y
  assert(x>0 && y>0);

  printf("l_init: x y\n");
  printf("l_init: %d %d\n",x,y);

  int q=0;
  int r=x;

  int ctr0 = 0;
  int ctr1 = 0;
  while(r>=y) {
    int a=1;
    int b=y;

    ctr1 = 0;
    while (r >= 2*b){

      assert(r>=2*y*a && b==y*a && x==q*y+r && r>=0);
      printf("l0: x y q a b r dummy_ctr0, dummy_ctr0\n");
      printf("l0: %d %d %d %d %d %d %d\n",x,y,q,a,b,r,ctr0++);
      cohendiv_dummy_l0(x,y,q,a,b,r);

      a = 2*a;
      b = 2*b;

    }
    r=r-b;
    q=q+a;
    
    printf("l1: x y q a b r dummy_ctr1\n");
    printf("l1: %d %d %d %d %d %d %d\n",x,y,q,a,b,r,ctr1++);
    cohendiv_dummy_l1(x,y,q,a,b,r);
  }

  assert(r == x % y);
  assert(q == x / y);
  printf("l2: x y q r\n");
  printf("l2: %d %d %d %d\n",x,y,q,r);
  return q;

}


void mannadiv_dummy_l0(y1,y2,y3,x1,x2){}
void mannadiv_dummy_l1(y1,y2,y3,x1,x2){}
int mannadiv (int x1, int x2){
  //Division algorithm from
  //"Z. Manna, Mathematical Theory of Computation, McGraw-Hill, 1974"
  //return x1 // x2

  printf("l_init: x1 x2\n");
  printf("l_init: %d %d\n",x1,x2);


  int y1,y2,y3;
  y1 = 0;
  y2 = 0;
  y3 = x1;
  
  int ctr = 0;
  while(y3 != 0) {
    assert(y1* x2 + y2 + y3 == x1);
    printf("l0: y1 y2 y3 x1 x2 dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d\n",y1,y2,y3,x1,x2,ctr++);
    mannadiv_dummy_l0(y1,y2,y3,x1,x2);

    if (y2 + 1 == x2) {
      y1 = y1 + 1;
      y2 = 0;
      y3 = y3 - 1;
    }
    else {
      y2 = y2 + 1;
      y3 = y3 - 1;
    }
  }

  assert(y1 == x1 / x2);
  printf("l1: y1 y2 y3 x1 x2\n");
  printf("l1: %d %d %d %d %d\n",y1,y2,y3,x1,x2);
  mannadiv_dummy_l1(y1,y2,y3,x1,x2);
  return y1;
}


void hard_dummy_l0(int d, int A, int B, int p, int r){}
void hard_dummy_l1(int d, int A, int B, int p, int r){}
void hard_dummy_l2(int d, int A, int B, int p, int r){}
int hard(int A, int B) {
  //hardware integer division program, by Manna
  //returns q==A//D
  assert(A >= 0);
  assert(B >= 1);

  printf("l_init: A B\n");
  printf("l_init: %d %d\n",A,B);

  int r,d,p,q;

  r=A;
  d=B;
  p=1;
  q=0;
  
  int ctr0 = 0;
  while (r >= d){
    assert( A >= 0 && B > 0 && q == 0 && r == A && d == B*p );
    printf("l2: d A B q p r dummy_ctr0\n");
    printf("l2: %d %d %d %d %d %d %d\n", d, A, B, q, p, r, ctr0++);
    hard_dummy_l2(d, A, B, p, r);
    d = 2 * d;
    p  = 2 * p;
  }

  int ctr1 = 0;
  while(p!=1){
    assert(A == q*B+r);
    assert(d == B*p);
    printf("l0: d A B q p r dummy_ctr1\n");
    printf("l0: %d %d %d %d %d %d %d\n", d, A, B, q, p, r, ctr1++);
    hard_dummy_l0(d, A, B, p, r);

    d=d/2;
    p=p/2;
      
    if(r>=d){
      r=r-d;
      q=q+p;
    }
  }

  assert(r == A % B);
  assert(q == A / B);

  printf("l1: d A B q p r\n");
  printf("l1: %d %d %d %d %d %d\n", d, A, B, q, p, r);
  hard_dummy_l1(d, A, B, p, r);
  return q;
}



//tvn: todo :  rerurn wensley with new set of inputs
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



  while (d > t){
    assert(y*z <= x);
    //assert(u == z*y);  //should be == instead of  u>= z*y
    assert(v == d/2.0*y);

    printf("l0: x y t z d u v\n");
    printf("l0:  %f %f %f %f %f %f %f\n",x, y, t, z, d, u, v);

    wensley_dummy(x, y, t, z, d, u, v);

    d = d/2.0;

    if (u + v <= x) {
      z = z + d; 
      u = u + v; 
    }
    v = v/2.0;
    //2v == d*y
  }

  assert(z <= x/y); 
  assert(x/y < z + t);
  printf("l1: x y t z d u v\n");
  printf("l1: %f %f %f %f %f %f %f\n",x, y, t, z, d, u, v);
  return z;
}//wensley


/*
Enrique's version

Wensley's algorithm for real division

float division (float P, float Q, float E)
pre(   Q > P  &&  P >= 0  &&  E > 0   );
    {
    float a,b,d,y;

    a=0;
    b=Q/2;
    d=1;
    y=0;

    inv(   a == Q*y   &&   b == Q*d/2   &&   P/Q - d < y   &&   y <= P/Q   );
    while( d>= E)
        {
        if (P< a+b)
            {
            b=b/2;
            d=d/2;
            }
        else
            {
            a=a+b;
            y=y+d/2;
            b=b/2;
            d=d/2;
            }
        }
return y;
}
post(   P/Q >= result   &&   result > P/Q - E   );
*/

void sqrt1_dummy_l0(int a, int n,int t,int s){}
void sqrt1_dummy_l1(int a, int n,int t,int s){}
int sqrt1(int n){
  /* computing the floor of the square root of a natural number */
  assert(n >= 0);
  printf("l_init: n\n");
  printf("l_init: %d\n",n);
  
  int a,s,t;
  a=0;
  s=1;
  t=1;

  int ctr = 0;
  while(s <= n ){
    assert(a*a <= n);
    assert(t == 2*a + 1);
    assert(s == (a + 1)*(a + 1));
    printf("l0: a n t s dummy_ctr\n");
    printf("l0: %d %d %d %d %d\n",a,n,t,s,ctr++);
    sqrt1_dummy_l0(a,n,t,s);

    a=a+1;
    t=t+2;
    s=s+t;
  }

  assert(a==(int)floor(sqrt(n)));
  printf("l1: a n t s\n");
  printf("l1: %d %d %d %d\n",a,n,t,s);
  sqrt1_dummy_l1(a,n,t,s);
  return a;

}//sqrt1

void freire1_dummy_l0(float a,float x,int r){}
void freire1_dummy_l1(float a,float x,int r){}
int freire1 (float a){
  //algorithm for finding the closest integer to the square root,
  //from  www.pedrofreire.com/crea2_en.htm?

  printf("l_init: a\n");
  printf("l_init: %f\n",a);

  float x;
  int r;

  x=a/2.0;
  r=0.0;

  int ctr = 0;
  while( x>r ){
       assert(a == 2*x + r*r - r); //Vu: added 2/18/2013
    printf("l0: a x r dummy_ctr\n");
    printf("l0: %f %f %d %d\n",a,x,r,ctr++);
    freire1_dummy_l0(a,x,r);

    x=x-r;
    r=r+1.0;
  }

  assert(r==(int)round(sqrt(a)));

  printf("l1: a x r\n");
  printf("l1: %f %f %d\n",a,x,r);
  freire1_dummy_l1(a,x,r);
  return r;
}//freire1

void freire2_dummy_l0(float a,float x,float s, int r){}
void freire2_dummy_l1(float a,float x,float s, int r){}
int freire2(float a){
  //algorithm for finding the closest integer to the cubic root,
  //from www.pedrofreire.com/crea2_en.htm? */ 
  //a is a float

  printf("l_init: a\n");
  printf("l_init: %f\n",a);

  float x,s;
  int r;
  
  x=a;
  r=1;
  s=3.25;

  int ctr = 0;
  while ( x-s > 0.0){
    
    //Vu: added 2/18/2013
    //this inv won't hold without proper conversion to int as below
    //e.g. using freire2 127.96

    assert(((int)(4*r*r*r - 6*r*r + 3*r) + (int)(4*x - 4*a)) == 1);
    assert((int)(4*s) -12*r*r == 1);

    //assert((int)-1728*a^2 + 64*s^3 - 1728*a*s + 3456*a*x - 192*s^2 + 1728*s*x - 1728*x^2 - 432*a - 24*s + 432*x - 91 == 0);

    //DIG: spurious
    //assert(-1728*a*a + 64*s*s*s - 1728*a*s + 3456*a*x - 192*s*s + 1728*s*x - 1728*x*x - 432*a - 24*s + 432*x - 91 == 0);
    //assert(144*a*r - 144*r*x - 16*s*s + 216*a - 126*r + 80*s - 216*x + 35 == 0);
    
    printf("l0: a x s r dummy_ctr\n");
    printf("l0: %f %f %f %d %d\n",a,x,s,r,ctr++);
    freire2_dummy_l0(a,x,s,r);

    x = x - s;
    s = s + 6 * r + 3;
    r = r + 1;
  }

  assert(r == (int)round(pow(a,(1.0/3.0))));
  printf("l1: a x s r\n");
  printf("l1: %f %f %f %d\n",a,x,s,r);
  freire2_dummy_l1(a,x,s,r);
  return r;

}//freire2

void dijkstra_dummy_l0(int r, int p, int n, int q, int h){}
void dijkstra_dummy_l1(int r, int p, int n, int q, int h){}
void dijkstra_dummy_l2(int r, int p, int n, int q, int h){}
int dijkstra(int n){
  /* program computing the floor of the square root, by Dijkstra */

  printf("l_init: n\n");
  printf("l_init: %d\n",n);

  int p,q,r,h;

  p=0;
  q=1;
  r=n;
  h= 0;
  
  int ctr0 = 0;
  while (q<=n){
    printf("l3: r p n q h dummy_ctr0\n");
    printf("l3: %d %d %d %d %d %d\n",r,p,n,q,h,ctr0++);

    q=4*q;
    assert(   n >= 0   &&   p == 0   &&   r==n );
  }
  //q = 4^n


  /*interesting, Nanjun suggests this assignment will make inv marked (3) below correct
  h = p + q; 
  But becareful of overflow, e.g.  h^3 would be too big for large numbers
  */

  printf("l2: r p n q h\n");
  printf("l2: %d %d %d %d %d\n",r,p,n,q,h);
  dijkstra_dummy_l2(r,p,n,q,h);
  //printf("#inv: r < 2*p + q,  p*p + r*q == n*q\n");

  int ctr1 = 0;
  while (q!=1){

    assert(r < 2*p + q);
    assert(p*p + r*q == n*q);

    //DIG SPURIOUS
    //assert((pow(h,2))*p - 4*h*n*q + 4*h*q*r + 4*n*p*q - p*pow(q,2) - 4*p*q*r == 0.0);
    //assert(((int)pow(h,2))*n - ((int)pow(h,2))*r - 4*h*n*p + 4*h*p*r + 4*((int)pow(n,2))*q - n*((int)pow(q,2)) - 8*n*q*r + ((int)pow(q,2))*r + 4*q*((int)pow(r,2)) == 0);
    //assert(((int)pow(h,3)) - 12*h*n*q - h*((int)pow(q,2)) + 12*h*q*r + 16*n*p*q - 4*p*((int)pow(q,2)) - 16*p*q*r == 0);
    

    //h^2*p - 4*h*n*q + 4*h*q*r + 4*n*p*q - p*q^2 - 4*p*q*r == 0
    //h^2*n - h^2*r - 4*h*n*p + 4*h*p*r + 4*n^2*q - n*q^2 - 8*n*q*r + q^2*r + 4*q*r^2 == 0
    //h^3 - 12*h*n*q - h*q^2 + 12*h*q*r + 16*n*p*q - 4*p*q^2 - 16*p*q*r == 0

    printf("l0: r p n q h dummy_ctr1\n");
    printf("l0: %d %d %d %d %d %d\n",r,p,n,q,h,ctr1++);
    dijkstra_dummy_l0(r,p,n,q,h);

    q=q/4;
    h=p+q;
    p=p/2;
    if (r>=h){
      p=p+q;
      r=r-h;
    } 
  }

  assert(p == (int)floor(sqrt(n)));
  printf("l1: r p n q h\n");
  printf("l1: %d %d %d %d %d\n",r,p,n,q,h);
  dijkstra_dummy_l1(r,p,n,q,h);

  return p;
}//dijkstra


void cohencu_dummy_l0(int a, int n, int x,int y,int z){}
void cohencu_dummy_l1(int a, int n, int x,int y,int z){}
int cohencu(int a) {
  /* printing consecutive cube, by Cohen */
  printf("l_init: a\n");
  printf("l_init: %d\n",a);

  int n,x,y,z;

  n=0; x=0; y=1; z=6;

  int ctr = 0;
  while(n<=a){

    assert(z == 6*n + 6);
    assert(y == 3*n*n + 3*n + 1);
    assert(x == n*n*n);
    printf("l0: a n x y z dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d\n", a,n,x,y,z,ctr++);
    cohencu_dummy_l0(a,n,x,y,z);

    n=n+1;
    x=x+y;
    y=y+z;
    z=z+6;
  }

  printf("l1: a n x y z\n");
  printf("l1: %d %d %d %d %d\n", a,n,x,y,z);
  cohencu_dummy_l1(a,n,x,y,z);
  return x;
}//cohencu



void euclidex1_dummy_l0(int a, int b,int y,int r,int x,int p,int q, int s){}
void euclidex1_dummy_l1(int a, int b,int y,int r,int x,int p,int q, int s){}
int euclidex1 (int x, int y){
  /* extended Euclid's algorithm */
  /* Used as motivation example in proposal and TOSEM, see egcd program */

  printf("l_init: x y\n");
  printf("l_init: %d %d\n",x,y);


  int a,b,p,q,r,s;
    
  a=x;
  b=y;
  p=1;
  q=0;
  r=0;
  s=1;
  
  int ctr = 0 ;
  while(a!=b) { 
    assert(1 == p*s - r*q); //VU: added 2/18/2013
    assert(a == y*r + x*p);
    assert(b == x*q + y*s);
    printf("l0: x y a b p q r s dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d %d %d %d\n",x,y,a,b,p,r,q,s,ctr++);
    euclidex1_dummy_l0(x,y,a,b,p,r,q,s);

    if (a>b) {
      a = a-b; 
      p = p-q; 
      r = r-s;
    }
    else {
      b = b-a; 
      q = q-p; 
      s = s-r;}
  }

  printf("l1: x y a b p q r s\n");
  printf("l1: %d %d %d %d %d %d %d %d\n",x,y,a,b,p,r,q,s);
  euclidex1_dummy_l1(x,y,a,b,p,r,q,s);
  return a;
}//euclidex1


void euclidex2_dummy_l0(int a , int b , int c ,int p, int q, 
			int r ,int s, int x ,int y ,int k){}    
void euclidex2_dummy_l2(int a , int b , int c ,int p, int q, 
			int r ,int s, int x ,int y ,int k){}    
void euclidex2_dummy_l1(int a , int b , int p, int q, int r ,int s){}    
			
int euclidex2 (int x, int y){
  /* extended Euclid's algorithm */
  printf("l_init: x y\n");
  printf("l_init: %d %d\n",x,y);

  int a,b,p,q,r,s;

  a=x;
  b=y;
  p=1;
  q=0;
  r=0; 
  s=1;

  int ctr0 = 0;
  int ctr1 = 0;
  while( b!=0 ) { 
    int c,k;
    
    c=a;
    k=0;

    ctr1 = 0;
    while( c>=b ){

      assert(a == k*b+c);
      assert(a == y*r+x*p);
      assert(b == x*q+y*s);
      printf("l0: a b c p q r s x y k dummy_ctr1\n");
      printf("l0: %d %d %d %d %d %d %d %d %d %d %d\n",
             a, b, c, p, q, r, s, x, y, k, ctr1++);
      euclidex2_dummy_l0(a, b, c, p, q, r, s, x, y, k);

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
    
    printf("l2: a b c p q r s x y k dummy_ctr0\n");
    printf("l2: %d %d %d %d %d %d %d %d %d %d %d\n",
	   a, b, c, p, q, r, s, x, y, k, ctr0++);
    euclidex2_dummy_l2(a ,b ,c ,p , q,r ,s, x ,y ,k);

  }

  assert(mygcd(x,y)==y*r+x*p );
  printf("l1: a b p q r s\n");
  printf("l1: %d %d %d %d %d %d\n", a ,b ,p , q,r ,s);
  euclidex2_dummy_l1(a ,b ,p , q,r ,s);

  return a;
}//euclidex2



/* def xgcd(a,b): */
/* if b == 0: */
/* return [1,0,a] */
/* else: */
/* x,y,d = xgcd(b, a%b) */
/* return [y, x - (a//b)*y, d] # Note that a//b is floor(a/b) in Python. */


/*
Todo:
lots of good euclid like algorithms here

http://www.di-mgt.com.au/euclidean.html
http://cs.ucsb.edu/~koc/ec/project/2004/lai.pdf
*/
int egcd(int A, int B){
  /* extended Euclid's algorithm, similar to euclidex1, just diff var names*/
  /* Used as motivation example in proposal and TOSEM paper */

  int x,y,i,j,k,m;
    
  x=A;
  y=B;
  i=1;
  j=0;
  k=0;
  m=1;
  
  
  
  while(1) { 
    printf("l0: A B x y i j k m\n");    
    printf("l0: %d %d %d %d %d %d %d %d\n",A,B,x,y,i,j,k,m);
    if (x==y){
      break;
    }
    assert(x == A*i + B*j);
    assert(y == A*k + B*m);
    assert(1 == i*m - j*k); 

    if (x>y) {
      x = x-y; 
      i = i-k; 
      j = j-m;
    }
    else {
      y = y-x; 
      k = k-i; 
      m = m-j;}

  }
  printf("l1: A B x y i j k m\n");    
  printf("l1: %d %d %d %d %d %d %d %d\n",A,B,x,y,i,j,k,m);
  return x;
}//egcd



void euclidex3_dummy_l0(int a,int b,int y,int r,int x,int p,
			int q,int s,int d,int v, int k, int c){}
void euclidex3_dummy_l1(int a,int b,int y,int r,int x,int p,int q,int s){}
			

int euclidex3 (int x, int y){
  /* extended Euclid's algorithm */

  printf("l_init: x y\n");
  printf("l_init: %d %d\n",x,y);


  int a,b,p,q,r,s;

  a=x; b=y;  p=1;  q=0;  r=0;   s=1;

  assert(a==y*r+x*p);
  assert(b==x*q+y*s);

  int ctr0 = 0;
  int ctr1 = 0;
  while( b!=0 ) { 
    int c,k;
    c=a;
    k=0;
      
    while( c>=b ){
      int d,v;
      d=1;
      v=b;

      ctr1 = 0;
      while ( c>= 2*v ) {

        assert(a == y*r+x*p);
        assert(b == x*q+y*s);
        assert(a == k*b+c);
        assert(v == b*d);
	printf("l0: a b y r x p q s d v k c dummy_ctr1\n");
        printf("l0: %d %d %d %d %d %d %d %d %d %d %d %d %d\n", 
               a, b, y, r, x, p, q, s, d, v, k, c, ctr1++);
        euclidex3_dummy_l0(a, b, y, r, x, p, q, s, d, v, k, c);

        d = 2*d;
        v = 2*v;

      }
      c=c-v;
      k=k+d;

      printf("l2: a b y r x p q s d v k c dummy_ctr0\n");
      printf("l2: %d %d %d %d %d %d %d %d %d %d %d %d %d\n", 
               a, b, y, r, x, p, q, s, d, v, k, c, ctr0++);

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

  printf("l1: a b y r x p q s\n");
  printf("l1: %d %d %d %d %d %d %d %d\n", 
	 a, b, y, r, x, p, q, s);
  euclidex3_dummy_l1(a, b, y, r, x, p, q, s);
  return a;
}//euclidex3
    

void lcm1_dummy_l0(int a, int b, int x, int y, int u, int v){}
void lcm1_dummy_l1(int a, int b, int x, int y, int u, int v, int r){}
int lcm1(int a, int b){
  /* algorithm for computing simultaneously the GCD and the LCM, 
     by Sankaranarayanan */
  /*tvn: 2 whiles*/

  printf("l_init: a b\n");
  printf("l_init: %d %d\n",a,b);


  int x,y,u,v;

  x=a;
  y=b;
  u=b;
  v=0;

  int ctr = 0;
  while(x!=y) {
    assert(x*u + y*v == a*b);

    printf("l0: a b x y u v dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d %d\n", a,b,x,y,u,v,ctr++);
    lcm1_dummy_l0(a,b,x,y,u,v);

    while (x>y){
      x=x-y;
      v=v+u;
    }
    
    while (x<y){
      y=y-x;
      u=u+v;
    }

  }

  //x==gcd(a,b)
  int r = u+v; 
  printf("l1: a b x y u v r\n");
  printf("l1: %d %d %d %d %d %d %d\n", a,b,x,y,u,v,r);
  lcm1_dummy_l1(a,b,x,y,u,v,4);
  return r; //lcm

}//lcm1



void lcm2_dummy_l0(int a,int b,int x,int y,int u,int v){}
void lcm2_dummy_l1(int a,int b,int x,int y,int u,int v, int r){}
int lcm2 (int a, int b){
  /* algorithm for computing simultaneously the GCD and the LCM, by Dijkstra */
  printf("l_init: a b\n");
  printf("l_init: %d %d\n",a,b);

  int x,y,u,v;

  x=a;
  y=b;
  u=b;
  v=a;
  
  int ctr = 0;
  while(x!=y) { 

    assert(x*u + y*v == 2*a*b);
    printf("l0: a b x y u v dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d %d\n", a,b,x,y,u,v,ctr++);
    lcm2_dummy_l0(a,b,x,y,u,v);

    if (x>y){
      x=x-y;
      v=v+u;
    }
    else {
      y=y-x;
      u=u+v;
    }
    
  }

  //x==gcd(a,b)
  int r = (u+v)/2;
  printf("l1: a b x y u v r\n");
  printf("l1: %d %d %d %d %d %d %d\n", a,b,x,y,u,v,r);
  lcm2_dummy_l1(a,b,x,y,u,v,r);
  return r; //lcm

}//lcm2


void prodbin_dummy_l0(int a, int b, int x, int y, int z){}
void prodbin_dummy_l1(int a, int b, int x, int y, int z){}
int prodbin (int a,int b){
  /* algorithm for computing the product of two natural numbers */
  /* shift_add */

  printf("l_init: a b\n");
  printf("l_init: %d %d\n",a,b);

  int x,y,z;
  
  x = a;
  y = b;
  z = 0;

  int ctr = 0;
  while( y!=0 ) { 

    assert(z+x*y==a*b);
    printf("l0: a b x y z dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d\n", a,b,x,y,z,ctr++);
    prodbin_dummy_l0(a,b,x,y,z);


    if (y%2 ==1 ){
      z = z+x;
      y = y-1;
    }
    x = 2*x;
    y = y/2;

  }
  assert(z == a*b);
  printf("l1: a b x y z\n");
  printf("l1: %d %d %d %d %d\n", a,b,x,y,z);
  prodbin_dummy_l1(a,b,x,y,z);
  return z; 

}//prodbin


void prod4br_dummy_l0(int x, int y, int a, int b, int p, int q){}
void prod4br_dummy_l1(int x, int y, int a, int b, int p, int q){}
int prod4br(int x, int y){
  /* algorithm for computing the product of two natural numbers */

  printf("l_init: x y\n");
  printf("l_init: %d %d\n",x,y);

  int a,b,p,q;

  a = x;
  b = y;
  p = 1;
  q = 0;

  int ctr = 0;
  while(a!=0 && b!=0 ) { 

    assert(q+a*b*p==x*y);
    printf("l0: x y a b p q dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d %d\n", x, y, a, b, p, q, ctr++);
    prod4br_dummy_l0(x, y, a, b, p, q);

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

  }

  assert(q == x*y);
  printf("l1: x y a b p q\n");
  printf("l1: %d %d %d %d %d %d\n", x, y, a, b, p, q);
  prod4br_dummy_l1(x, y, a, b, p, q);
  return q; 
}

void fermat1_dummy_l0(int A, int R, int u, int v, int r){}
void fermat1_dummy_l1(int A, int R, int u, int v, int r){}
int fermat1(int A, int R){
  // program computing a divisor for factorisation, by Knuth 4.5.4 Alg C ?
  /*tvn: run forever, but ok because we can just capture those values*/
  //tvn: 2 whiles

  printf("l_init: A R\n");
  printf("l_init: %d %d\n",A,R);

  assert(A >= 1);
  assert((R-1)*(R-1) < A);
  assert(A <= R*R);
  assert(A%2 ==1); 

  int u,v,r;
  u=2*R+1;
  v=1;
  r=R*R-A;
  
  //assert( 4*(A+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && A>=1 );
  int ctr0 = 0;
  int ctr1 = 0;
  while (r!=0){
    assert(4*(A+r) == u*u-v*v-2*u+2*v);
    printf("l0: A R u v r dummy_ctr0\n");
    printf("l0: %d %d %d %d %d %d\n", A, R, u, v, r, ctr0++);
    fermat1_dummy_l0(A, R, u, v, r); 

    while ( r>0 ) {
      r=r-v;
      v=v+2;
    }
    
    ctr1 = 0;
    while ( r<0 ){
      r=r+u;
      u=u+2;
      printf("l1: A R u v r dummy_ctr1\n");  
      printf("l1: %d %d %d %d %d %d\n", A, R, u, v, r, ctr1++);
      fermat1_dummy_l1(A, R, u, v, r); 

    }

  }
  
  assert(u!=v); 
  int o = (u-v)/2;
  return o;

}//fermat1

void fermat2_dummy_l0(int A, int R, int u, int v, int r){}
void fermat2_dummy_l1(int A, int R, int u, int v, int r){}
int fermat2(int A, int R){
  /* program computing a divisor for factorisation, by Bressoud */

  printf("l_init: A R\n");
  printf("l_init: %d %d\n",A,R);

  assert(A >= 1);
  assert((R-1)*(R-1) < A);
  assert(A <= R*R);
  assert(A%2 ==1); 

  int u,v,r;
    
  u=2*R+1;
  v=1;
  r=R*R-A;

  //assert( 4*(A+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && A>=1 );
  int ctr = 0;
  while (r!=0){

    printf("l0: A R u v r dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d\n", A, R, u, v, r, ctr++);
    fermat2_dummy_l0(A, R, u, v, r);

    assert(4*(A + r) == u*u - v*v - 2*u + 2*v);

    if (r>0) {
      r=r-v;
      v=v+2;
      printf("l1: A R u v r\n");
      printf("l1: %d %d %d %d %d\n", A, R, u, v, r);
      fermat2_dummy_l1(A, R, u, v, r);

    }

    else{
      r=r+u;
      u=u+2;
    }

  }
  
  assert(u!=v);
  int o = (u-v)/2;
  return o;

}//fermat2

void knuth_dummy_l0(int n, int d1, int r, int k, int q, int d, int s, int t){}
void knuth_dummy_l1(int n, int d1, int r, int k, int q, int d, int s, int t){}
                 
int knuth(int n, int d1){
  //algorithm searching for a divisor for factorization, by Knuth
  //had to comment out one of the invariants

  printf("l_init: n d1\n");
  printf("l_init: %d %d\n",n,d1);

  int r,k,q,d,s,t;

  d=d1;
  r= n % d;
  t = 0;

  if (d <= 2){
    printf("#E: d - 2 <= 0.  Use a diff val for d\n");
    return 0;
  }
  k=n % (d-2);
  q=4*(n/(d-2) - n/d);
  s=sqrt(n);


  int ctr = 0;
  while((s>=d)&&(r!=0)){
       assert(d*d*q - 2*q*d - 4*r*d + 4*k*d  + 8*r == 8*n);

    assert(k*t == t*t);
    assert(d*d*q - 2*d*q - 4*d*r + 4*d*t + 4*d1*k - 4*d1*t - 8*n + 8*r == 0);
    assert(d*k - d*t - d1*k + d1*t == 0);

    printf("l0: n d1 r k q d s t dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d %d %d %d\n", 
	   n, d1, r, k, q, d, s, t, ctr++);
    knuth_dummy_l0(n, d1, r, k, q, d, s, t);

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

  }
  printf("l1: n d1 r k q d s t\n");
  printf("l1: %d %d %d %d %d %d %d %d\n", n, d1, r, k, q, d, s, t);
  knuth_dummy_l1(n, d1, r, k, q, d, s, t);

  return d;

}//knuth




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


/*from Petter"s master thesis
  http://www2.cs.tum.edu/~petter/da/da.pdf

IMPORTANT: don't try with very large power (k) 
which makes the number *very* large and becomes problematic.
e.g. 15*8 = -1732076671 on my Macbook Pro
This is a _computer_dependent_problem, not mathematics problem
*/



void geo1_dummy_l0(int x, int y, int z, int k){}
void geo1_dummy_l1(int x, int y, int z, int k){}
int geo1 (int z, int k){
  /* computes x=(z-1)* sum(z^k)[k=0..k-1] , y = z^k
     returns 1+x-y == 0

     The loop is same as geo2 but the result is different.
  */

  printf("l_init: z k\n");
  printf("l_init: %d %d\n",z,k);


  assert(k>0);
  int x = 1; int y = z; int c = 1;


  int ctr = 0;
  while (c < k){
    assert(x*z - x - y + 1 == 0);
    printf("l0: x y z  dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,z,ctr++);
    geo1_dummy_l0(x, y, z, k);
    
    c = c + 1;
    x = x*z + 1;
    y = y*z;

  }//geo1

  x = x *(z - 1);


  printf("# y=%d\n",y);
  assert(y == pow(z,k));
  

  int i = 0; int s = 0;
  for(i =0 ; i<k ; ++i){s = s  + pow(z,i);}
  s = s * (z-1);

  assert(s == x);
  assert(1+x-y == 0); //documented inv

  printf("l1: x y z k \n");
  printf("l1: %d %d %d %d\n",x,y,z, k);
  geo1_dummy_l1(x, y, z, k);

  return x;
}

void geo2_dummy_l0(int x, int y, int z, int k){}
void geo2_dummy_l1(int x, int y, int z, int k){}
int geo2(int z, int k){
  //computes x = sum(z^k)[k=0..k-1], y = z^(k-1)

  printf("l_init: z k\n");
  printf("l_init: %d %d\n",z,k);

  assert (k>0);
  int x = 1; int y = 1; int c = 1;

  int ctr = 0;
  while (c < k){
    assert(1+x*z-x-z*y==0);
    printf("l0: x y z k  dummy_ctr\n");
    printf("l0: %d %d %d %d %d\n",x, y, z, k, ctr++);
    geo2_dummy_l0(x, y, z, k);

    c = c + 1;
    x = x*z + 1;
    y = y*z;
  }
  
  assert(y == pow(z,(k-1)));

  int i = 0; int s = 0;
  for(i =0 ; i<k ; ++i){s = s  + pow(z,i);}
  assert(s == x);

  printf("l1: x y z k\n");
  printf("l1: %d %d %d %d\n",x, y, z, k);
  geo2_dummy_l1(x, y, z, k);
  return x;

}//geo2

void geo3_dummy_l0(int x, int y, int z, int a, int k){}
void geo3_dummy_l1(int x, int y, int z, int a, int k){}
int geo3(int z,int a, int k){
  //computes x = sum(a*z^k)[k=0..k-1], y = z^(k-1)

  printf("l_init: z a k\n");
  printf("l_init: %d %d %d\n",z,a,k);

  int x = a; int y = 1;  int c = 1;
  int ctr = 0;
  while (c < k){

    assert(z*x-x+a-a*z*y == 0);
    printf("l0: x y z a k dummy_ctr\n");
    printf("l0: %d %d %d %d %d %d\n", x, y, z, a,k, ctr++);
    geo3_dummy_l0( x, y, z, a,k);

    c = c + 1;
    x = x*z + a;
    y = y*z;

  }

  assert(y == pow(z,(k-1)));
  int i = 0; int s = 0;
  for(i =0 ; i<k ; ++i){s = s  + a*pow(z,i);}
  assert(s == x);

  printf("l1: x y z a k\n");
  printf("l1: %d %d %d %d %d\n", x, y, z, a,k) ;
  geo3_dummy_l1( x, y, z, a,k);
  return x;
}//geo3


/*
  # // yielding x=y
  # //todo: too easy, not worth doing
  # def ps1 ( String []
  # y = 0
  # x = 0
  # while ( args !=null){
  # y=y +1
  # x=x +1
*/

int ps_test(n,k){
  // computes 0^k + ... + n^k

  int i = 1;
  int s = 0;
  for(; i <= n; ++i){
    s = s + pow(i,k);
  }
  return s;
}


void ps1_dummy_l0(int x, int y, int k){}
void ps1_dummy_l1(int x, int y, int k){}
int ps1(int k){

  printf("l_init: k\n");
  printf("l_init: %d\n",k);

  int y = 0; int x = 0;int c = 0;
  int ctr = 0;
  while (c < k){
    assert(y-x ==0);
    printf("l0: x y k dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,k,ctr++);
    ps1_dummy_l0(x,y,k);

    c = c + 1;
    y = y + 1;
    x = x + 1;
  }

  assert(y == 1*k);
  assert(x == ps_test(k,0));
  printf("l1: x y k\n");
  printf("l1: %d %d %d\n",x,y,k);
  ps1_dummy_l1(x,y,k);
  return x;
}//ps1


void ps2_dummy_l0(int x, int y, int k){}
void ps2_dummy_l1(int x, int y, int k){}
int ps2(int k){

  printf("l_init: k\n");
  printf("l_init: %d\n",k);

  int y = 0; int x = 0; int c = 0;

  int ctr = 0;
  while (c < k){
    assert(2*x-y*y-y == 0);
    printf("l0: x y k dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,k,ctr++);
    ps2_dummy_l0(x,y,k);

    c = c + 1;
    y=y +1;
    x=x+y;

  }

  assert(y == 1*k);
  assert(x == ps_test(k,1));
  printf("l1: x y k\n");
  printf("l1: %d %d %d\n",x,y,k);
  ps2_dummy_l1(x,y,k);
  return x;
}//ps2

void ps3_dummy_l0(int x, int y, int k){}
void ps3_dummy_l1(int x, int y, int k){}
int ps3(int k){
  printf("l_init: k\n");
  printf("l_init: %d\n",k);

  int y = 0;
  int x = 0;
  int c = 0;

  int ctr = 0;  
  while (c < k){
    assert(6*x-2*y*y*y-3*y*y-y == 0);
    printf("l0: x y k dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,k,ctr++);
    ps3_dummy_l0(x,y,k);

    c = c + 1;
    y=y +1;
    x=y*y+x;

  }

  assert(y == 1*k);
  assert(x == ps_test(k,2));
  printf("l1: x y k\n");
  printf("l1: %d %d %d\n",x,y,k);
  ps3_dummy_l1(x,y,k);
  return x;
}//ps3
  

void ps4_dummy_l0(int x,int y,int k){}
void ps4_dummy_l1(int x,int y,int k){}
int ps4 (int k){

  printf("l_init: k\n");
  printf("l_init: %d\n",k);

  int y = 0;
  int x = 0;
  int c = 0;
  
  int ctr = 0;
  while (c < k){
    assert(4*x-(y*y*y*y)-2*(y*y*y)-(y*y) == 0);
    printf("l0: x y k dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,k,ctr++);
    ps4_dummy_l0(x,y,k);
    c = c +1 ;
    y=y +1;
    x=y*y*y+x;

  }

  assert(y == 1*k);
  assert(x == ps_test(k,3));
  printf("l1: x y k\n");
  printf("l1: %d %d %d\n",x,y,k);
  ps4_dummy_l1(x,y,k);

  return x;
}//ps4



void ps5_dummy_l0(int x,int y,int k){}
void ps5_dummy_l1(int x,int y,int k){}
int ps5 (int k){

  printf("l_init: k\n");
  printf("l_init: %d\n",k);

  int y = 0;
  int x = 0;
  int c = 0;
  
  int ctr = 0;
  while (c < k){
       assert(6*(int)pow(y,5) + 15*(int)pow(y,4) + 10*(int)pow(y,3) - 30*x - y == 0); //DIG Generated
    printf("l0: x y k dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,k,ctr++);
    ps5_dummy_l0(x,y,k);
    c = c +1 ;
    y=y +1;
    x=y*y*y*y+x;
  }

  assert(y == 1*k);
  assert(x == ps_test(k,4));
  printf("l1: x y k\n");
  printf("l1: %d %d %d\n",x,y,k);
  ps5_dummy_l1(x,y,k);
  return x;
}//ps5



void ps6_dummy_l0(int x,int y,int k){}
void ps6_dummy_l1(int x,int y,int k){}
int ps6 (int k){

  printf("l_init: k\n");
  printf("l_init: %d\n",k);

  int y = 0;
  int x = 0;
  int c = 0;
  
  int ctr = 0;  
  while (c < k){
       //assert(-2*pow(y,6) - 6*pow(y,5) - 5*pow(y,4) + pow(y,2) + 12*x == 0.0); //DIG Generated  (but don't uncomment, assertion will fail because of int overflow)
    printf("l0: x y k dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,k,ctr++);
    ps6_dummy_l0(x,y,k);
    c = c +1 ;
    y=y +1;
    x=y*y*y*y*y+x;
  }

  assert(y == 1*k);
  assert(x == ps_test(k,5));
  printf("l1: x y k\n");
  printf("l1: %d %d %d\n",x,y,k);
  ps6_dummy_l1(x,y,k);
  return x;
}//ps6


void ps7_dummy_l0(int x,int y,int k){}
void ps7_dummy_l1(int x,int y,int k){}
int ps7 (int k){

  printf("l_init: k\n");
  printf("l_init: %d\n",k);

  int y = 0;
  int x = 0;
  int c = 0;

  int ctr = 0;    
  while (c < k){
    //assert(-6*pow(y,7) - 21*pow(y,6) - 21*pow(y,5) + 7*pow(y,3) + 42*x - y == 0); //DIG generated (but don't uncomment, assertion will fail because of int overflow)
    printf("l0: x y k dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,k,ctr++);
    ps7_dummy_l0(x,y,k);
    c = c +1 ;
    y=y +1;
    x=y*y*y*y*y*y+x;
  }

  assert(y == 1*k);
  assert(x == ps_test(k,6));
  printf("l1: x y k\n");
  printf("l1: %d %d %d\n",x,y,k);
  ps7_dummy_l1(x,y,k);
  return x;
}//ps7


/*The following ps will cause int overflow*/
void ps8_dummy(int x,int y,int k){}
int ps8 (int k){

  printf("l_init: k\n");
  printf("l_init: %d\n",k);


  int y = 0;
  int x = 0;
  int c = 0;
  
  int ctr = 0;  
  while (c < k){
    //assert(4*x-(y*y*y*y)-2*(y*y*y)-(y*y) == 0);
    printf("l0: x y k dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,k,ctr++);
    c = c +1 ;
    y=y +1;
    x=y*y*y*y*y*y*y+x;
  }

  assert(y == 1*k);
  assert(x == ps_test(k,7));

  return x;
}//ps4


void ps9_dummy(int x,int y,int k){}
int ps9 (int k){
  /*
    computes very large number, so might cause overflow
    and thus cannot capture not enough traces
   */

  printf("l_init: k\n");
  printf("l_init: %d\n",k);


  int y = 0;
  int x = 0;
  int c = 0;
  
  int ctr = 0;  
  while (c < k){
    //assert(4*x-(y*y*y*y)-2*(y*y*y)-(y*y) == 0);

    printf("l0: x y k dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,k,ctr++);
    c = c +1 ;
    y=y +1;
    x=y*y*y*y*y*y*y*y+x;
  }

  assert(y == 1*k);
  assert(x == ps_test(k,8));

  return x;
}//ps4

void ps10_dummy(int x,int y,int k){}
int ps10 (int k){
  /*
    computes very large number, so might cause overflow
    and thus cannot capture not enough traces
   */

  printf("l_init: k\n");
  printf("l_init: %d\n",k);

  int y = 0;
  int x = 0;
  int c = 0;
  
  int ctr = 0;
  while (c < k){
    //assert(4*x-(y*y*y*y)-2*(y*y*y)-(y*y) == 0);

    printf("l0: x y k dummy_ctr\n");
    printf("l0: %d %d %d %d\n",x,y,k,ctr++);
    c = c +1 ;
    y=y +1;
    x=y*y*y*y*y*y*y*y*y+x;
  }

  assert(y == 1*k);
  assert(x == ps_test(k,9));


  return x;
}//ps4



void readers_writers_dummy(int r, int w, int k, int a1, int a2, int k0){}
int readers_writers(int a1, int a2, int k0){
  //generalization of the readers-writers problem, by Sankaranarayanan
  assert ( a1 >= 0 && a2 >= 0 && k0 >=0 ) ;
  int r,w,k;
  r = 0;
  w = 0;
  k = k0;

  int ctr = 0;

  printf("r w k a1 a2 k0\n");
  while(ctr < MAX_LOOP){ 
    
    // r*a1 + w*a2 + k == k0
    //r*w==0
    printf("%d %d %d %d %d %d\n",r, w, k, a1, a2, k0);
    readers_writers_dummy(r, w, k, a1, a2, k0);

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

  }
  return k;
}//readers_writers

void z3sqrt_dummy(float a, float err, float r, float p, float q){}
float z3sqrt (float a, float err){
  //program for computing square roots, by Zuse

  //todo: due to rounding imprec
  assert(1.0 <= a && a <= 4.0 && 0.005 <= err );

  float r,q,p;

  r = a-1.0;
  q = 1.0;
  p = 1.0/2.0;
  


  while ( 2.0*p*r >= err ){
    printf("l0: a err r p q\n");
    printf("l0: %f %f %f %f %f\n",a,err,r,p,q);
    z3sqrt_dummy(a,err,r,p,q);

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
    //assert(q*q + 2.0*r*p == a);
    //assert(err > 0.0);
    //assert(p >= 0.0);
    //assert(r >= 0.0 );
    
  }

  assert( pow(q,2) <= a);
  assert( pow(q,2)+err >= a );
  printf("l1: a err r p q\n");
  printf("l1: %f %f %f %f %f\n",a,err,r,p,q);
  return q;
  
}//z3



double byz_sqrt(double x) {
  //Byzantine's method to calc square root
  //Also known as Newton's method
  assert(x>=0);
  double eps = 0.00001;  //can change this
  double n = x / 2.0; 
  n = (n + x / n) / 2.0;
  while (abs(n * n - x) > eps){
    printf("%f %f %f\n",n,x,eps);
    n = (n + x / n) / 2.0;
  }

  assert(abs(n*n - x) <= eps);
  return n;
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






/* void divbin0_dummy(int A, int B,int q,int b, int r){} */
/* int divbin0 (int A, int B){ */
/*   //binary division algorithm, by Kaldewaij */
/*   //returns A//B */
/*   //tvn: 2 whiles */

/*   assert(A > 0 && B > 0); */
/*   int q = 0; */
/*   int r = A; */
/*   int b = B; */

/*   printf("l0: A B q b r\n"); */
/*   printf("l0: %d %d %d %d %d\n",A,B,q,b,r); */
/*   while(r>=b){ */
/*     //assert((exists(int k;k >= 0  &&  b == 2^k*B)); */
/*     assert(q == 0 && r == A  &&  A >= 0  &&  B > 0); */
/*     b=2*b; */
/*   } */

/*   while(b!=B){ */

/*     assert(A == q*b + r && r >= 0); */
/*     divbin0_dummy(A,B,q,b,r); */

/*     q = 2*q; */

/*     b = b/2; */
/*     if (r >= b) { */
/*       q = q + 1; */
/*       r = r - b; */
/*     } */
/*   } */
  
/*   assert(q==A/B); */
/*   assert(r==A%B); */

/*   printf("l1: A B q b r\n");   */
/*   printf("l1: %d %d %d %d %d\n",A,B,q,b,r); */
/*   return q; */
/* } */


/* void hard0_dummy(int d1, int A, int D, int p, int r){} */
/* int hard0(int A, int D) { */
/*   //hardware integer division program, by Manna */
/*   //returns q==A//D */
/*   assert(A >= 0); */
/*   assert(D >= 1); */
/*   int r,d1,p,q; */

/*   r=A; */
/*   d1=D; */
/*   p=1; */
/*   q=0; */

/*   while (r >= d1){ */
/*     assert( A >= 0 && D > 0 && q == 0 && r == A && d1 == D*p ); */
/*     //exists( int k; k>=0 && d1==D*2^k) && exists( int l; l>=0 && p==2^l ) */
    
/*     d1 = 2 * d1; */
/*     p  = 2 * p; */
/*   } */


/*   printf("l0: d1 A D q p r\n"); */
/*   printf("l0: %d %d %d %d %d %d\n", d1, A,D, q, p, r); */

/*   while(p!=1){ */
/*     assert(A == q*D+r); */
/*     assert(d1 == D*p); */

    
/*     hard0_dummy(d1, A,D, p, r); */

/*     d1=d1/2; */
/*     p=p/2; */
      
/*     if(r>=d1){ */
/*       r=r-d1; */
/*       q=q+p; */
/*     } */

/*   } */

/*   assert(r == A % D); */
/*   assert(q == A / D); */

/*   printf("l1: d1 A D q p r\n"); */
/*   printf("l1: %d %d %d %d %d %d\n", d1, A,D, q, p, r); */
/*   return q; */
/* } */
