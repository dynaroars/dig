/*
NLA testsuite

Consists of small, nontrivial arithmetic programs.
Mostly from Enric Carbonell 's invariants website at 
http://www.lsi.upc.edu/~erodri/webpage/polynomial_invariants/list.html

Some programs are collected elsewhere
*/


void cohendiv_dummy_l1a(int x, int y, int q, int a, int b,int r){}
int cohendiv(int x, int y){
  //Cohen's integer division
  //returns x % y

  assert(x>0 && y>0);

  printf("l_pre: x y\n");
  printf("l_pre: %d %d\n",x,y);

  int q=0;
  int r=x;

  while(1){

    printf("li0: x y q r\n");
    printf("li0: %d %d %d %d\n",x,y,q,r);

    if (!(r>=y)) break;

    int a=1;
    int b=y;

    while(1){
      printf("li1: x y q a b r\n");
      printf("li1: %d %d %d %d %d %d\n",x,y,q,a,b,r);

      if (!(r >= 2*b)) break;

      assert(r>=2*y*a && b==y*a && x==q*y+r && r>=0);
      printf("l1a: x y q a b r\n");
      printf("l1a: %d %d %d %d %d %d\n",x,y,q,a,b,r);
      cohendiv_dummy_l1a(x,y,q,a,b,r);

      a = 2*a;
      b = 2*b;

    }
    r=r-b;
    q=q+a;
    
  }

  assert(r == x % y);
  assert(q == x / y);
  printf("l_post: x y q r\n");
  printf("l_post: %d %d %d %d\n",x,y,q,r);
  return q;

}

void divbin_dummy_l1a(int A, int B,int q,int b, int r){}
int divbin(int A, int B){
  /*
  binary division algorithm, by Kaldewaij
  returns A//B
  tvn: 2 whiles
  */

  printf("l_pre: A B\n");
  printf("l_pre: %d %d\n",A,B);

  assert(A > 0 && B > 0);
  int q = 0;
  int r = A;
  int b = B;

  while(1){
    printf("li0: A B q b r\n");
    printf("li0: %d %d %d %d %d\n",A,B,q,b,r); 

    if (!(r>=b)) break;

    assert(q == 0 && r == A  &&  A >= 0  &&  B > 0);
    b=2*b;
  }


  while(1){
    printf("li1: A B q b r\n");
    printf("li1: %d %d %d %d %d\n",A,B,q,b,r);
    if (!(b!=B)) break;

    assert(A == q*b + r && r >= 0);
    printf("l1a: A B q b r\n");
    printf("l1a: %d %d %d %d %d\n",A,B,q,b,r);
    divbin_dummy_l1a(A,B,q,b,r);

    q = 2*q;
    b = b/2;
    if (r >= b) {
      q = q + 1;
      r = r - b;
    }
  }
  
  assert(q==A/B);
  assert(r==A%B);
  printf("l_post: A B q b r\n");
  printf("l_post: %d %d %d %d %d\n",A,B,q,b,r);  
  return q;
}


void mannadiv_dummy_li0(y1,y2,y3,x1,x2){}
int mannadiv (int x1, int x2){
  //Division algorithm from
  //"Z. Manna, Mathematical Theory of Computation, McGraw-Hill, 1974"
  //return x1 // x2

  printf("l_pre: x1 x2\n");
  printf("l_pre: %d %d\n",x1,x2);

  int y1,y2,y3;
  y1 = 0;
  y2 = 0;
  y3 = x1;
  
  while(1){
    printf("li0: y1 y2 y3 x1 x2\n");
    printf("li0: %d %d %d %d %d\n",y1,y2,y3,x1,x2);
    if(!(y3 != 0)) break;

    assert(y1* x2 + y2 + y3 == x1);
    printf("l0a: y1 y2 y3 x1 x2\n");
    printf("l0a: %d %d %d %d %d\n",y1,y2,y3,x1,x2);
    mannadiv_dummy_li0(y1,y2,y3,x1,x2);

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
  printf("l_post: y1 y2 y3 x1 x2\n");
  printf("l_post: %d %d %d %d %d\n",y1,y2,y3,x1,x2);
  return y1;
}


void hard_dummy_l0a(int d, int A, int B, int p, int r){}
void hard_dummy_l1a(int d, int A, int B, int p, int r){}

int hard(int A, int B) {
  //hardware integer division program, by Manna
  //returns q==A//B
  assert(A >= 0);
  assert(B >= 1);

  printf("l_pre: A B\n");
  printf("l_pre: %d %d\n",A,B);

  int r,d,p,q;

  r=A;
  d=B;
  p=1;
  q=0;
  
  while(1){
    printf("li0: d A B q p r\n");
    printf("li0: %d %d %d %d %d %d\n", d, A, B, q, p, r);

    if (!(r >= d)) break;
    assert( A >= 0 && B > 0 && q == 0 && r == A && d == B*p );

    printf("l0a: d A B q p r\n");
    printf("l0a: %d %d %d %d %d %d\n", d, A, B, q, p, r);
    hard_dummy_l0a(d, A, B, p, r);
    d = 2 * d;
    p  = 2 * p;
  }

  while(1){
    printf("li1: d A B q p r\n");
    printf("li1: %d %d %d %d %d %d\n", d, A, B, q, p, r);
    if (!(p!=1)) break;

    assert(A == q*B+r);
    assert(d == B*p);
    printf("l1a: d A B q p r\n");
    printf("l1a: %d %d %d %d %d %d\n", d, A, B, q, p, r);
    hard_dummy_l1a(d, A, B, p, r);

    d=d/2;
    p=p/2;
      
    if(r>=d){
      r=r-d;
      q=q+p;
    }
  }

  assert(r == A % B);
  assert(q == A / B);

  printf("l_post: d A B q p r\n");
  printf("l_post: %d %d %d %d %d %d\n", d, A, B, q, p, r);
  return q;
}


void sqrt1_dummy_l0a(int a, int n,int t,int s){}
int sqrt1(int n){
  /* computing the floor of the square root of a natural number */
  assert(n >= 0);
  printf("l_pre: n\n");
  printf("l_pre: %d\n",n);
  
  int a,s,t;
  a=0;
  s=1;
  t=1;

  while(1){
    printf("li0: a n t s\n");
    printf("li0: %d %d %d %d\n",a,n,t,s);

    if(!(s <= n)) break;

    assert(a*a <= n);
    assert(t == 2*a + 1);
    assert(s == (a + 1)*(a + 1));
    printf("l0a: a n t s\n");
    printf("l0a: %d %d %d %d\n",a,n,t,s);
    sqrt1_dummy_l0a(a,n,t,s);

    a=a+1;
    t=t+2;
    s=s+t;
  }

  assert(a==(int)floor(sqrt(n)));
  printf("l_post: a n t s\n");
  printf("l_post: %d %d %d %d\n",a,n,t,s);

  return a;
}//sqrt1


void dijkstra_dummy_l0a(int r, int p, int n, int q, int h){}
int dijkstra(int n){
  /* program computing the floor of the square root, by Dijkstra */
  assert(n>=0);

  printf("l_pre: n\n");
  printf("l_pre: %d\n",n);

  int p,q,r,h;

  p=0;
  q=1;
  r=n;
  h= 0;

  while(1){
    printf("li0: r p n q h\n");
    printf("li0: %d %d %d %d %d\n",r,p,n,q,h);

    if (!(q<=n)) break;

    q=4*q;
    assert(n >= 0 && p == 0 && r==n );
  }
  //q = 4^n


  /*interesting, Nanjun suggests this assignment will make inv marked (3) below correct
  h = p + q; 
  But becareful of overflow, e.g.  h^3 would be too big for large numbers
  */

  while(1){
    printf("li1: r p n q h\n");
    printf("li1: %d %d %d %d %d\n",r,p,n,q,h);

    if (!(q!=1)) break;

    assert(r < 2*p + q);
    assert(p*p + r*q == n*q);

    //DIG SPURIOUS
    //assert((pow(h,2))*p - 4*h*n*q + 4*h*q*r + 4*n*p*q - p*pow(q,2) - 4*p*q*r == 0.0);
    //assert(((int)pow(h,2))*n - ((int)pow(h,2))*r - 4*h*n*p + 4*h*p*r + 4*((int)pow(n,2))*q - n*((int)pow(q,2)) - 8*n*q*r + ((int)pow(q,2))*r + 4*q*((int)pow(r,2)) == 0);
    //assert(((int)pow(h,3)) - 12*h*n*q - h*((int)pow(q,2)) + 12*h*q*r + 16*n*p*q - 4*p*((int)pow(q,2)) - 16*p*q*r == 0);
    

    //h^2*p - 4*h*n*q + 4*h*q*r + 4*n*p*q - p*q^2 - 4*p*q*r == 0
    //h^2*n - h^2*r - 4*h*n*p + 4*h*p*r + 4*n^2*q - n*q^2 - 8*n*q*r + q^2*r + 4*q*r^2 == 0
    //h^3 - 12*h*n*q - h*q^2 + 12*h*q*r + 16*n*p*q - 4*p*q^2 - 16*p*q*r == 0

    printf("l1a: r p n q h\n");
    printf("l1a: %d %d %d %d %d\n",r,p,n,q,h);
    dijkstra_dummy_l0a(r,p,n,q,h);

    q=q/4;
    h=p+q;
    p=p/2;
    if (r>=h){
      p=p+q;
      r=r-h;
    } 
  }

  assert(p == (int)floor(sqrt(n)));
  printf("l_post: r p n q h\n");
  printf("l_post: %d %d %d %d %d\n",r,p,n,q,h);

  return p;
}//dijkstra


void freire1_dummy_l0a(float a,float x,int r){}

int freire1 (float a){
  //algorithm for finding the closest integer to the square root,
  //from  www.pedrofreire.com/crea2_en.htm?

  printf("l_pre: a\n");
  printf("l_pre: %f\n",a);

  float x;
  int r;

  x=a/2.0;
  r=0;

  while(1){
    printf("li0: a x r\n");
    printf("li0: %f %f %d\n",a,x,r);
    
    if (!(x>r)) break;

    printf("l0a: a x r\n");
    printf("l0a: %f %f %d\n",a,x,r);
    freire1_dummy_l0a(a,x,r);

    x=x-r;
    r=r+1;
  }

  assert(r==(int)round(sqrt(a)));

  printf("l_post: a x r\n");
  printf("l_post: %f %f %d\n",a,x,r);

  return r;
}//freire1

void freire2_dummy_l0a(float a,float x,float s, int r){}
int freire2(float a){
  //algorithm for finding the closest integer to the cubic root,
  //from www.pedrofreire.com/crea2_en.htm? */ 
  //a is a float

  printf("l_pre: a\n");
  printf("l_pre: %f\n",a);

  float x,s;
  int r;
  
  x=a;
  r=1;
  s=3.25;

  while(1){
    printf("li0: a x s r\n");
    printf("li0: %f %f %f %d\n",a,x,s,r);

    if (!(x-s > 0.0)) break;
    //Vu: added 2/18/2013
    //this inv won't hold without proper conversion to int as below
    //e.g. using freire2 127.96

    assert(((int)(4*r*r*r - 6*r*r + 3*r) + (int)(4*x - 4*a)) == 1);
    assert((int)(4*s) -12*r*r == 1);

    //assert((int)-1728*a^2 + 64*s^3 - 1728*a*s + 3456*a*x - 192*s^2 + 1728*s*x - 1728*x^2 - 432*a - 24*s + 432*x - 91 == 0);

    //DIG: spurious
    //assert(-1728*a*a + 64*s*s*s - 1728*a*s + 3456*a*x - 192*s*s + 1728*s*x - 1728*x*x - 432*a - 24*s + 432*x - 91 == 0);
    //assert(144*a*r - 144*r*x - 16*s*s + 216*a - 126*r + 80*s - 216*x + 35 == 0);
    
    printf("l0a: a x s r\n");
    printf("l0a: %f %f %f %d\n",a,x,s,r);
    freire2_dummy_l0a(a,x,s,r);

    x = x - s;
    s = s + 6 * r + 3;
    r = r + 1;
  }

  assert(r == (int)round(pow(a,(1.0/3.0))));
  printf("l_post: a x s r\n");
  printf("l_post: %f %f %f %d\n",a,x,s,r);

  return r;
}//freire2


void cohencu_dummy_l0a(int a, int n, int x,int y,int z){}
int cohencu(int a){
  /* printing consecutive cube, by Cohen */
  printf("l_pre: a\n");
  printf("l_pre: %d\n",a);

  int n,x,y,z;

  n=0; x=0; y=1; z=6;

  while(1){
    printf("li0: a n x y z\n");
    printf("li0: %d %d %d %d %d\n", a,n,x,y,z);

    if (!(n<=a)) break;
    assert(z == 6*n + 6);
    assert(y == 3*n*n + 3*n + 1);
    assert(x == n*n*n);
    printf("l0a: a n x y z\n");
    printf("l0a: %d %d %d %d %d\n", a,n,x,y,z);
    cohencu_dummy_l0a(a,n,x,y,z);

    n=n+1;
    x=x+y;
    y=y+z;
    z=z+6;
  }

  printf("l_post: a n x y z\n");
  printf("l_post: %d %d %d %d %d\n", a,n,x,y,z);

  return x;
}//cohencu



void euclidex1_dummy_l0a(int a, int b,int y,int r,int x,int p,int q, int s){}
int euclidex1 (int x, int y){
  /* extended Euclid's algorithm */
  /* Used as motivation example in proposal and TOSEM, see egcd program */

  printf("l_pre: x y\n");
  printf("l_pre: %d %d\n",x,y);

  int a,b,p,q,r,s;
    
  a=x;
  b=y;
  p=1;
  q=0;
  r=0;
  s=1;
  
  while(1){ 
    printf("li0: x y a b p q r s\n");
    printf("li0: %d %d %d %d %d %d %d %d\n",x,y,a,b,p,r,q,s);
    if (!(a!=b)) break;

    assert(1 == p*s - r*q); //VU: added 2/18/2013
    assert(a == y*r + x*p);
    assert(b == x*q + y*s);
    printf("l0a: x y a b p q r s\n");
    printf("l0a: %d %d %d %d %d %d %d %d\n",x,y,a,b,p,r,q,s);
    euclidex1_dummy_l0a(x,y,a,b,p,r,q,s);

    if (a>b){
      a = a-b; 
      p = p-q; 
      r = r-s;
    }
    else {
      b = b-a; 
      q = q-p; 
      s = s-r;}
  }

  printf("l_post: x y a b p q r s\n");
  printf("l_post: %d %d %d %d %d %d %d %d\n",x,y,a,b,p,r,q,s);

  return a;
}//euclidex1


void euclidex2_dummy_l1a(int a, int b, int c, int p, int q, 
			 int r, int s, int x, int y, int k){}
			
int euclidex2 (int x, int y){
  /* extended Euclid's algorithm */
  printf("l_pre: x y\n");
  printf("l_pre: %d %d\n",x,y);

  int a,b,p,q,r,s;

  a=x; b=y; p=1; q=0; r=0; s=1;

  while(1){
      printf("li0: a b p q r s x y\n");
      printf("li0: %d %d %d %d %d %d %d %d\n",
             a, b, p, q, r, s, x, y);

    if (!(b!=0)) break;
  
    int c=a,k=0;

    while(1){
      printf("li1: a b c p q r s x y k\n");
      printf("li1: %d %d %d %d %d %d %d %d %d %d\n",
             a, b, c, p, q, r, s, x, y, k);

      if (!(c>=b)) break;
      
      assert(a == k*b+c);
      assert(a == y*r+x*p);
      assert(b == x*q+y*s);
      printf("l1a: a b c p q r s x y k\n");
      printf("l1a: %d %d %d %d %d %d %d %d %d %d\n",
             a, b, c, p, q, r, s, x, y, k);
      euclidex2_dummy_l1a(a, b, c, p, q, r, s, x, y, k);

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

  assert(mygcd(x,y)==y*r+x*p );
  printf("l_post: a b p q r s\n");
  printf("l_post: %d %d %d %d %d %d\n", a, b, p, q, r, s);

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


void euclidex3_dummy_l2a(int a,int b,int y,int r,int x,int p,
			int q,int s,int d,int v, int k, int c){}
			

int euclidex3(int x, int y){
  /* extended Euclid's algorithm */

  printf("l_pre: x y\n");
  printf("l_pre: %d %d\n",x,y);

  int a,b,p,q,r,s;

  a=x; b=y;  p=1;  q=0;  r=0;   s=1;

  assert(a==y*r+x*p);
  assert(b==x*q+y*s);

  while(1){ 
    
    printf("li0: a b y r x p q s\n");
    printf("li0: %d %d %d %d %d %d %d %d\n", 
	   a, b, y, r, x, p, q, s);

    if(!(b!=0)) break;

    int c=a,k=0;
      
    while(1){
      printf("li1: a b y r x p q s k c\n");
      printf("li1: %d %d %d %d %d %d %d %d %d %d\n", 
	     a, b, y, r, x, p, q, s, k, c);

      if (!(c>=b)) break;
      int d=1,v=b;

      while(1){

	printf("li2: a b y r x p q s d v k c\n");
        printf("li2: %d %d %d %d %d %d %d %d %d %d %d %d\n", 
               a, b, y, r, x, p, q, s, d, v, k, c);

	if (!(c>= 2*v)) break;
        assert(a == y*r+x*p);
        assert(b == x*q+y*s);
        assert(a == k*b+c);
        assert(v == b*d);
	printf("l2a: a b y r x p q s d v k c\n");
        printf("l2a: %d %d %d %d %d %d %d %d %d %d %d %d\n", 
               a, b, y, r, x, p, q, s, d, v, k, c);
        euclidex3_dummy_l2a(a, b, y, r, x, p, q, s, d, v, k, c);

        d = 2*d;
        v = 2*v;

      }
      c=c-v;
      k=k+d;

      //assert(a==y*r+x*p && b==x*q+y*s && a==k*b+c );
             
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

  printf("l_post: a b y r x p q s\n");
  printf("l_post: %d %d %d %d %d %d %d %d\n", 
	 a, b, y, r, x, p, q, s);

  return a;
}//euclidex3
    

void lcm1_dummy_l0a(int a, int b, int x, int y, int u, int v){}
int lcm1(int a, int b){
  /* algorithm for computing simultaneously the GCD and the LCM, 
     by Sankaranarayanan */
  /*tvn: 2 whiles*/

  printf("l_pre: a b\n");
  printf("l_pre: %d %d\n",a,b);

  int x,y,u,v;

  x=a;
  y=b;
  u=b;
  v=0;

  while(1){
    printf("li0: a b x y u v\n");
    printf("li0: %d %d %d %d %d %d\n", a,b,x,y,u,v);

    if (!(x!=y)) break;

    assert(x*u + y*v == a*b);

    printf("l0a: a b x y u v\n");
    printf("l0a: %d %d %d %d %d %d\n", a,b,x,y,u,v);
    lcm1_dummy_l0a(a,b,x,y,u,v);

    while(1){
      printf("li1: a b x y u v\n");
      printf("li1: %d %d %d %d %d %d\n", a,b,x,y,u,v);

      if (!(x>y)) break;

      x=x-y;
      v=v+u;
    }
    
    while(1){
      printf("li2: a b x y u v\n");
      printf("li2: %d %d %d %d %d %d\n", a,b,x,y,u,v);

      if (!(x<y)) break;

      y=y-x;
      u=u+v;
    }
  }
  //x==gcd(a,b)
  int r = u+v; 
  printf("l_post: a b x y u v r\n");
  printf("l_post: %d %d %d %d %d %d %d\n", a,b,x,y,u,v,r);

  return r; //lcm
}//lcm1


void lcm2_dummy_l0a(int a,int b,int x,int y,int u,int v){}
int lcm2 (int a, int b){
  /* algorithm for computing simultaneously the GCD and the LCM, by Dijkstra */
  printf("l_pre: a b\n");
  printf("l_pre: %d %d\n",a,b);

  int x,y,u,v;

  x=a;
  y=b;
  u=b;
  v=a;
  
  while(1){ 
    printf("li0: a b x y u v\n");
    printf("li0: %d %d %d %d %d %d\n", a,b,x,y,u,v);

    if (!(x!=y)) break;

    assert(x*u + y*v == 2*a*b);
    printf("l0a: a b x y u v\n");
    printf("l0a: %d %d %d %d %d %d\n", a,b,x,y,u,v);
    lcm2_dummy_l0a(a,b,x,y,u,v);

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
  printf("l_post: a b x y u v r\n");
  printf("l_post: %d %d %d %d %d %d %d\n", a,b,x,y,u,v,r);

  return r; //lcm
}//lcm2


void prodbin_dummy_l0a(int a, int b, int x, int y, int z){}
int prodbin (int a, int b){
  /* algorithm for computing the product of two natural numbers */
  /* shift_add */

  assert(b>=0);

  printf("l_pre: a b\n");
  printf("l_pre: %d %d\n",a,b);

  int x,y,z;
  
  x = a;
  y = b;
  z = 0;

  while(1){ 
    printf("li0: a b x y z\n");
    printf("li0: %d %d %d %d %d\n", a,b,x,y,z);

    if (!(y!=0)) break;

    assert(z+x*y==a*b);
    printf("l0a: a b x y z\n");
    printf("l0a: %d %d %d %d %d\n", a,b,x,y,z);
    prodbin_dummy_l0a(a,b,x,y,z);


    if (myodd(y)){
      z = z + x;
      y = y - 1;
    }
    x = 2 * x;
    y = y / 2;

  }
  assert(z == a*b);
  printf("l_post: a b x y z\n");
  printf("l_post: %d %d %d %d %d\n", a,b,x,y,z);

  return z; 
}//prodbin


void prod4br_dummy_l0a(int x, int y, int a, int b, int p, int q){}
int prod4br(int x, int y){
  /* algorithm for computing the product of two natural numbers */

  printf("l_pre: x y\n");
  printf("l_pre: %d %d\n",x,y);

  int a,b,p,q;

  a = x;
  b = y;
  p = 1;
  q = 0;

  while(1){ 
    printf("li0: x y a b p q\n");
    printf("li0: %d %d %d %d %d %d\n", x, y, a, b, p, q);

    if (!(a!=0 && b!=0)) break;

    assert(q+a*b*p==x*y);
    printf("l0a: x y a b p q\n");
    printf("l0a: %d %d %d %d %d %d\n", x, y, a, b, p, q);
    prod4br_dummy_l0a(x, y, a, b, p, q);

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
  printf("l_post: x y a b p q\n");
  printf("l_post: %d %d %d %d %d %d\n", x, y, a, b, p, q);

  return q; 

}//prod4br

void fermat1_dummy_li0(int A, int R, int u, int v, int r){}
void fermat1_dummy_li1(int A, int R, int u, int v, int r){}
int fermat1(int A, int R){
  // program computing a divisor for factorisation, by Knuth 4.5.4 Alg C ?
  /*tvn: run forever, but ok because we can just capture those values*/
  //tvn: 2 whiles
  
  printf("l_pre: A R\n");
  printf("l_pre: %d %d\n",A,R);

  assert(A >= 1);
  assert((R-1)*(R-1) < A);
  assert(A <= R*R);
  assert(A%2 ==1); 

  int u,v,r;
  u=2*R+1;
  v=1;
  r=R*R-A;
  
  //assert( 4*(A+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && A>=1 );
  while(1){
    printf("li0: A R u v r\n");
    printf("li0: %d %d %d %d %d\n", A, R, u, v, r);

    if (!(r!=0)) break;
    
    assert(4*(A+r) == u*u-v*v-2*u+2*v);
    printf("l0a: A R u v r\n");
    printf("l0a: %d %d %d %d %d\n", A, R, u, v, r);
    fermat1_dummy_li0(A, R, u, v, r); 

    while(1){
      printf("li1: A R u v r\n");
      printf("li1: %d %d %d %d %d\n", A, R, u, v, r);

      if (!(r>0)) break;
      r=r-v;
      v=v+2;
    }
    
    while(1){
      printf("li2: A R u v r\n");
      printf("li2: %d %d %d %d %d\n", A, R, u, v, r);

      if (!(r<0)) break;
      r=r+u;
      u=u+2;
    }

  }
  
  assert(u!=v); 
  int o = (u-v)/2;
  printf("l_post: A R u v r\n");
  printf("l_post: %d %d %d %d %d\n", A, R, u, v, r);

  return o;
}//fermat1


void fermat2_dummy_li0(int A, int R, int u, int v, int r){}
int fermat2(int A, int R){
  /* program computing a divisor for factorisation, by Bressoud */

  printf("l_pre: A R\n");
  printf("l_pre: %d %d\n",A,R);

  assert(A >= 1);
  assert((R-1)*(R-1) < A);
  assert(A <= R*R);
  assert(A%2 ==1); 

  int u,v,r;
    
  u=2*R+1;
  v=1;
  r=R*R-A;

  //assert( 4*(A+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && A>=1 );
  while(1){
    printf("li0: A R u v r\n");
    printf("li0: %d %d %d %d %d\n", A, R, u, v, r);
    fermat2_dummy_li0(A, R, u, v, r);

    if (!(r!=0)) break;

    assert(4*(A + r) == u*u - v*v - 2*u + 2*v);

    if (r>0){
      r=r-v;
      v=v+2;
    }
    else{
      r=r+u;
      u=u+2;
    }
  }
  
  assert(u!=v);
  int o = (u-v)/2;
  printf("l_post: A R u v r o\n");
  printf("l_post: %d %d %d %d %d %d\n", A, R, u, v, r, o);

  return o;
}//fermat2

void knuth_dummy_li0(int n, int a, int r, int k, int q, int d, int s, int t){}
int knuth(int n, int a){
  //algorithm searching for a divisor for factorization, by Knuth

  printf("l_pre: n a\n");
  printf("l_pre: %d %d\n",n,a);

  int r,k,q,d,s,t;

  d=a;
  r= n % d;
  t = 0;

  if (d <= 2){
    printf("#E: d - 2 <= 0.  Use a diff val for d\n");
    return 0;
  }
  k=n % (d-2);
  q=4*(n/(d-2) - n/d);
  s=sqrt(n);

  while(1){
    printf("li0: n a r k q d s t\n");
    printf("li0: %d %d %d %d %d %d %d %d\n", 
	   n, a, r, k, q, d, s, t);
    knuth_dummy_li0(n, a, r, k, q, d, s, t);

    if (!((s>=d)&&(r!=0))) break;

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
  printf("l_post: n a r k q d s t\n");
  printf("l_post: %d %d %d %d %d %d %d %d\n", n, a, r, k, q, d, s, t);

  return d;
}//knuth




void petter(k){  
  //geo
  int x = 0;
  int y = 0;

  while(1){
    printf("x y k\n");
    printf("%d %d %d\n",x,y,k);

    if (!(y != k)) break;

    x = x + pow(y,5);
    y = y + 1;
  }
}

/*from Petter"s master thesis
  http://www2.cs.tum.edu/~petter/da/da.pdf

IMPORTANT: don't try with very large power (k) 
which makes the number *very* large and becomes problematic.
e.g. 15*8 = -1732076671 on my Macbook Pro
This is a _computer_dependent_problem, not mathematics problem
*/

int geo_pw(const int a, const int z, const int k){
  //computes (z-1) * sum(z^i)[k=0..k-1]

  int i = 0; int s = 0;
  for(; i<k ; ++i) s = s + a*pow(z,i);
  return s;
}

void geo1_dummy_li0(int x, int y, int z, int k){}
int geo1(const int z, const int k){
  /* computes x=(z-1)* sum(z^k)[k=0..k-1] , y = z^k
     returns 1+x-y == 0

     The loop is same as geo2 but the result is different.
  */

  assert(k>0);

  printf("l_pre: z k\n");
  printf("l_pre: %d %d\n",z,k);
  
  int x = 1; int y = z; int c = 1;

  while(1){
    printf("li0: x y z\n");
    printf("li0: %d %d %d\n",x,y,z);
    geo1_dummy_li0(x, y, z, k);
    
    if (!(c < k)) break;

    c = c + 1;
    x = x*z + 1;
    y = y*z;

  }//geo1

  x = x *(z - 1);

  assert(y == pow(z,k));
  assert(geo_pw(1,z,k)*(z-1) == x);
  assert(1+x-y == 0); //documented inv

  printf("l_post: x y z k \n");
  printf("l_post: %d %d %d %d\n",x,y,z, k);

  return x;
}

void geo2_dummy_li0(int x, int y, int z, int k){}
int geo2(const int z, const int k){
  //computes x = sum(z^k)[k=0..k-1], y = z^(k-1)
  assert (k>0);

  printf("l_pre: z k\n");
  printf("l_pre: %d %d\n",z,k);

  int x = 1; int y = 1; int c = 1;

  while(1){
    printf("li0: x y z k\n");
    printf("li0: %d %d %d %d\n",x, y, z, k);
    geo2_dummy_li0(x, y, z, k);

    if (!(c < k)) break;


    c = c + 1;
    x = x*z + 1;
    y = y*z;
  }
  
  assert(y == pow(z,(k-1)));
  assert(geo_pw(1,z,k) == x);

  printf("l_post: x y z k\n");
  printf("l_post: %d %d %d %d\n",x, y, z, k);

  return x;
}//geo2

void geo3_dummy_li0(int x, int y, int z, int a, int k){}
int geo3(const int z, const int a, const int k){
  //computes x = sum(a*z^k)[k=0..k-1], y = z^(k-1)
  assert (k>0);

  printf("l_pre: z a k\n");
  printf("l_pre: %d %d %d\n",z,a,k);

  int x = a; int y = 1;  int c = 1;
  while(1){

    printf("li0: x y z a k\n");
    printf("li0: %d %d %d %d %d\n", x, y, z, a,k);
    geo3_dummy_li0( x, y, z, a,k);

    if (!(c < k)) break;

    c = c + 1;
    x = x*z + a;
    y = y*z;

  }

  assert(y == pow(z,(k-1)));
  assert(geo_pw(a,z,k) == x);

  printf("l_post: x y z a k\n");
  printf("l_post: %d %d %d %d %d\n", x, y, z, a,k) ;

  return x;
}//geo3


/*
  # // yielding x=y
  # //todo: too easy, not worth doing
  # def ps1 ( String []
  # y = 0
  # x = 0
  # while( args !=null){
  # y=y +1
  # x=x +1
*/


int ps_pw(const int k, const int z){
  // computes sum(i^z)[k=1..k]
  int i = 1; int s = 0;
  for(; i <= k; ++i) s = s + pow(i,z);
  return s;
}


void ps1_dummy_li0(int x, int y, int k){}
int ps1(const int k){

  printf("l_pre: k\n");
  printf("l_pre: %d\n",k);

  int y = 0; int x = 0;int c = 0;
  while(1){

    printf("li0: x y k\n");
    printf("li0: %d %d %d\n",x,y,k);
    ps1_dummy_li0(x,y,k);

    if (!(c < k)) break;

    c = c + 1;
    y = y + 1;
    x = x + 1;
  }

  assert(y == 1*k);
  assert(x == ps_pw(k,0));
  printf("l_post: x y k\n");
  printf("l_post: %d %d %d\n",x,y,k);

  return x;
}//ps1


void ps2_dummy_li0(int x, int y, int k){}
int ps2(int k){

  printf("l_pre: k\n");
  printf("l_pre: %d\n",k);

  int y = 0; int x = 0; int c = 0;

  while(1){
    printf("li0: x y k\n");
    printf("li0: %d %d %d\n",x,y,k);
    ps2_dummy_li0(x,y,k);

    if (!(c < k)) break;

    c = c + 1;
    y=y +1;
    x=x+y;

  }

  assert(y == 1*k);
  assert(x == ps_pw(k,1));
  printf("l_post: x y k\n");
  printf("l_post: %d %d %d\n",x,y,k);

  return x;
}//ps2

void ps3_dummy_li0(int x, int y, int k){}
int ps3(int k){
  printf("l_pre: k\n");
  printf("l_pre: %d\n",k);

  int y = 0;
  int x = 0;
  int c = 0;

  while(1){
    printf("li0: x y k\n");
    printf("li0: %d %d %d\n",x,y,k);
    ps3_dummy_li0(x,y,k);

    if (!(c < k)) break;

    c = c + 1;
    y=y +1;
    x=y*y+x;

  }

  assert(y == 1*k);
  assert(x == ps_pw(k,2));
  printf("l_post: x y k\n");
  printf("l_post: %d %d %d\n",x,y,k);

  return x;
}//ps3
  

void ps4_dummy_li0(int x,int y,int k){}
int ps4 (int k){

  printf("l_pre: k\n");
  printf("l_pre: %d\n",k);

  int y = 0;
  int x = 0;
  int c = 0;
  
  while(1){
    printf("li0: x y k\n");
    printf("li0: %d %d %d\n",x,y,k);
    ps4_dummy_li0(x,y,k);

    if (!(c < k)) break;

    c = c +1 ;
    y=y +1;
    x=y*y*y+x;

  }

  assert(y == 1*k);
  assert(x == ps_pw(k,3));
  printf("l_post: x y k\n");
  printf("l_post: %d %d %d\n",x,y,k);

  return x;
}//ps4



void ps5_dummy_li0(int x,int y,int k){}
int ps5 (int k){

  printf("l_pre: k\n");
  printf("l_pre: %d\n",k);

  int y = 0;
  int x = 0;
  int c = 0;
  
  while(1){
    printf("li0: x y k\n");
    printf("li0: %d %d %d\n",x,y,k);
    ps5_dummy_li0(x,y,k);

    if (!(c < k)) break;

    c = c +1 ;
    y=y +1;
    x=y*y*y*y+x;
  }

  assert(y == 1*k);
  assert(x == ps_pw(k,4));
  printf("l_post: x y k\n");
  printf("l_post: %d %d %d\n",x,y,k);

  return x;
}//ps5



void ps6_dummy_li0(int x,int y,int k){}
int ps6 (int k){

  printf("l_pre: k\n");
  printf("l_pre: %d\n",k);

  int y = 0;
  int x = 0;
  int c = 0;
  
  while(1){
    printf("li0: x y k\n");
    printf("li0: %d %d %d\n",x,y,k);
    ps6_dummy_li0(x,y,k);

    if (!(c < k)) break;

    c = c +1 ;
    y=y +1;
    x=y*y*y*y*y+x;
  }

  assert(y == 1*k);
  assert(x == ps_pw(k,5));
  printf("l_post: x y k\n");
  printf("l_post: %d %d %d\n",x,y,k);

  return x;
}//ps6


/* Drivers */

int driver_nla(char **argv){
  if (strcmp(argv[1],"cohendiv")==0){
    printf("#result = %d\n", 
	   cohendiv(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  /* else if (strcmp(argv[1],"divbin0")==0){ */
  /*   printf("#result = %d\n",  */
  /*          divbin0(atoi(argv[2]),atoi(argv[3]))); */
  /* } */

  else if (strcmp(argv[1],"divbin")==0){
    printf("#result = %d\n", 
	   divbin(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"mannadiv")==0){
    printf("#result = %d\n", 
	   mannadiv(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"hard")==0){
    printf("#result = %d\n", 
	   hard(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  /* else if (strcmp(argv[1],"hard0")==0){ */
  /*   printf("#result = %d\n",  */
  /*          hard0(atoi(argv[2]),atoi(argv[3]))); */
  /* } */
  else if (strcmp(argv[1],"sqrt1")==0){
    printf("#result = %d\n", sqrt1(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"dijkstra")==0){
    printf("#result = %d\n", dijkstra(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"freire1")==0){
    printf("#result = %d\n", freire1(atof(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"freire2")==0){
    printf("#result = %d\n", freire2(atof(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"cohencu")==0){
    printf("#result = %d\n", 
	   cohencu(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"euclidex1")==0){
    printf("#result = %d\n", 
	   euclidex1(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"euclidex2")==0){
    printf("#result = %d\n", 
	   euclidex2(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"euclidex3")==0){
    printf("#result = %d\n", 
	   euclidex3(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"lcm1")==0){
    printf("#result = %d\n", 
	   lcm1(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"lcm2")==0){
    printf("#result = %d\n", 
	   lcm2(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"prodbin")==0){
    printf("#result = %d\n", 
	   prodbin(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"prod4br")==0){
    printf("#result = %d\n", 
	   prod4br(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"fermat1")==0){
    printf("#result = %d\n", 
	   fermat1(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"fermat2")==0){
    printf("#result = %d\n", 
	   fermat2(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"knuth")==0){
    printf("#result = %d\n", 
	   knuth(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"geo1")==0){
    printf("#result = %d\n", 
	   geo1(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"geo2")==0){
    printf("#result = %d\n", 
	   geo2(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"geo3")==0){
    printf("#result = %d\n", 
	   geo3(atoi(argv[2]),atoi(argv[3]),atoi(argv[4])));
    return 1;
  }
  else if (strcmp(argv[1],"ps1")==0){
    printf("#result = %d\n", ps1(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"ps2")==0){
    printf("#result = %d\n", ps2(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"ps3")==0){
    printf("#result = %d\n", ps3(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"ps4")==0){
    printf("#result = %d\n", ps4(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"ps5")==0){
    printf("#result = %d\n", ps5(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"ps6")==0){
    printf("#result = %d\n", ps6(atoi(argv[2])));
    return 1;
  }
  return 0;
}


/* END of NLA programs */


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



/* void divbin0_dummy(int A, int B,int q,int b, int r){} */
/* int divbin0 (int A, int B){ */
/*   //binary division algorithm, by Kaldewaij */
/*   //returns A//B */
/*   //tvn: 2 whiles */

/*   assert(A > 0 && B > 0); */
/*   int q = 0; */
/*   int r = A; */
/*   int b = B; */

/*   printf("li0: A B q b r\n"); */
/*   printf("li0: %d %d %d %d %d\n",A,B,q,b,r); */
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
/*     if (r >= b){ */
/*       q = q + 1; */
/*       r = r - b; */
/*     } */
/*   } */
  
/*   assert(q==A/B); */
/*   assert(r==A%B); */

/*   printf("li1: A B q b r\n");   */
/*   printf("li1: %d %d %d %d %d\n",A,B,q,b,r); */
/*   return q; */
/* } */


/* void hard0_dummy(int a, int A, int D, int p, int r){} */
/* int hard0(int A, int D){ */
/*   //hardware integer division program, by Manna */
/*   //returns q==A//D */
/*   assert(A >= 0); */
/*   assert(D >= 1); */
/*   int r,a,p,q; */

/*   r=A; */
/*   a=D; */
/*   p=1; */
/*   q=0; */

/*   while(r >= a){ */
/*     assert( A >= 0 && D > 0 && q == 0 && r == A && a == D*p ); */
/*     //exists( int k; k>=0 && a==D*2^k) && exists( int l; l>=0 && p==2^l ) */
    
/*     a = 2 * a; */
/*     p  = 2 * p; */
/*   } */


/*   printf("li0: a A D q p r\n"); */
/*   printf("li0: %d %d %d %d %d %d\n", a, A,D, q, p, r); */

/*   while(p!=1){ */
/*     assert(A == q*D+r); */
/*     assert(a == D*p); */

    
/*     hard0_dummy(a, A,D, p, r); */

/*     a=a/2; */
/*     p=p/2; */
      
/*     if(r>=a){ */
/*       r=r-a; */
/*       q=q+p; */
/*     } */

/*   } */

/*   assert(r == A % D); */
/*   assert(q == A / D); */

/*   printf("li1: a A D q p r\n"); */
/*   printf("li1: %d %d %d %d %d %d\n", a, A,D, q, p, r); */
/*   return q; */
/* } */





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

  while(d > t){
    assert(y*z <= x);
    //assert(u == z*y);  //should be == instead of  u>= z*y
    assert(v == d/2.0*y);

    printf("li0: x y t z d u v\n");
    printf("li0:  %f %f %f %f %f %f %f\n",x, y, t, z, d, u, v);

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
  printf("li1: x y t z d u v\n");
  printf("li1: %f %f %f %f %f %f %f\n",x, y, t, z, d, u, v);
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


void z3sqrt_dummy(float a, float err, float r, float p, float q){}
float z3sqrt (float a, float err){
  //program for computing square roots, by Zuse

  //todo: due to rounding imprec
  assert(1.0 <= a && a <= 4.0 && 0.005 <= err );

  float r,q,p;

  r = a-1.0;
  q = 1.0;
  p = 1.0/2.0;
  


  while( 2.0*p*r >= err ){
    printf("li0: a err r p q\n");
    printf("li0: %f %f %f %f %f\n",a,err,r,p,q);
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
  printf("li1: a err r p q\n");
  printf("li1: %f %f %f %f %f\n",a,err,r,p,q);
  return q;
  
}//z3



double byz_sqrt(double x){
  //Byzantine's method to calc square root
  //Also known as Newton's method
  assert(x>=0);
  double eps = 0.00001;  //can change this
  double n = x / 2.0; 
  n = (n + x / n) / 2.0;
  while(abs(n * n - x) > eps){
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

  while(c*c <= a){
    c = 2*c;
  }

  while(c >= 2){
    
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


int driver_nla_others(char **argv){
  if (strcmp(argv[1],"wensley")==0){
      printf("#result = %g\n", 
             wensley(atof(argv[2]),atof(argv[3]),atof(argv[4])));
      return 1;
    }
    else if (strcmp(argv[1],"byz_sqrt")==0){
      printf("#result = %g\n", byz_sqrt(atof(argv[2])));
      return 1;
    }
    else if (strcmp(argv[1],"z3sqrt")==0){
      printf("#result = %g\n", 
             z3sqrt(atof(argv[2]), atof(argv[3])));
      return 1;
    }
    else if (strcmp(argv[1],"f1")==0){
      printf("#result = %d\n", 
             f1(atoi(argv[2])));
      return 1;
    }
    else if (strcmp(argv[1],"readers_writers")==0){
      printf("#result = %d\n", 
             readers_writers(atoi(argv[2]),
                             atoi(argv[3]),atoi(argv[4])));
      return 1;
    }  
  return 0;
}
