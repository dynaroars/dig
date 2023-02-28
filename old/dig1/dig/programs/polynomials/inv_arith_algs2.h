// Various Math functions in C++: http://jean-pierre.moreau.pagesperso-orange.fr/cplus.html

/********************************************
*    Factorization of an integer number     *
* ----------------------------------------- *
* Sample run:                               *
*                                           *
* ? 394616                                  *
*                                           *
* 2 2 2 107 461                             *
*                                           *
* ----------------------------------------- *
* Ref.: "Mathématiques par l'informatique   *
*        individuelle (1) par H. Lehning    *
*        et D. Jakubowicz, Masson, Paris,   *
*        1982" [BIBLI 06].                  *
*                                           *
*               C++ version by J-P Moreau.  *
********************************************/

int nr_factors(double n0){
  //I think this returns n, where n is a prime factor of n0
  double n,d,eps,m,i;
  n=n0;
  d=0.0;
  eps=1e-6;
  m=0.0;
  i=0.0;


  // Test if multiple of 2
 e50:d=n-2*(int)(n/2);
  if (fabs(d)<eps) {
    //printf("2 "); 
    n=n/2; goto e50;}
  // Test if multiple of 3
 e100:d=n-3*(int)(n/3);
  if (fabs(d)<eps) {
    //printf("3 "); 
    n=n/3; goto e100;
  }
  // Test of divisors 6i-1 and 6i+1 up to sqrt(n)
  // Prime numbers are of the form 6i-1 or 6i+1
  m=floor(sqrt(n))+1;
  i=6;

  printf("n0 n d eps m i\n");
  while (i<m+1) {
    printf("%g %g %g %g %g %g\n",n0,n,d,eps,m,i);

  e150:d=n-(i-1)*(int)(n/(i-1));
    if (fabs(d)<eps) {
      //printf("%4.0f ",i-1); 
      n=n/(i-1); 
      goto e150;
    }
  e200:d=n-(i+1)*(int)(n/(i+1));
    if (fabs(d)<eps) {
      //printf("%4.0f ",i+1); 
      n=n/(i+1); 
      goto e200;
    }
    i=i+6;
  }

  return n;
}


int nr_prime(double n){


  double d, eps, i,m;
  d=0.0;
  i=0.0;
  m=0.0;
  eps=1e-6;  //tvn : added


  d=n-2*(int)(n/2);
  if (fabs(d)<eps) return 0;
  //Test if multiple of 3
  d=n-3*(int)(n/3);
  if (fabs(d)<eps) return 0;
  //Test if multiple of 6i-1 and 6i+1 from i=6 to sqrt(N)+1
  i=6; m=floor(sqrt(n))+1;
  printf("n d eps i m\n");
  while (i<=m)  {
    printf("%g %g %g %g %g\n",
           n, d, eps, i, m);
    d=n-(i-1)*(int)(n/(i-1));
    if (fabs(d)<eps) return 0;
    d=n-(i+1)*(int)(n/(i+1));
    if (fabs(d)<eps) return 0;
    i=i+6;
  }
  return 1;
}

int nr_diophantian(float a, float b, float c) {
  float x0,yy0,p,q;
  x0=0.0;
  yy0=0.0;
  p=0.0;
  q=0.0;

  float pg,x1,x2,y1,y2;
  pg = 0.0;
  x1 = 0.0;
  x2 = 0.0;
  y1 = 0.0;
  y2 = 0.0;
  int found = 0;
  if (a==0) return FALSE;
  if (b==0) return FALSE;;
  pg=mygcd_n(a,b);


  a=a/pg; b=b/pg; c=c/pg;
  if (c!=(int)(c)) 
    return FALSE; // pg must be also a divisor of c
  x1=0; y2=0;
  found=FALSE;

  printf("a b c x0 yy0 p q pg x1 x2 y1 y2\n");
  do {

    printf("%g %g %g %g %g %g %g %g %g %g %g %g\n",
             a, b, c,x0,yy0,p, q,pg,x1,x2,y1,y2);

    y1=(c-a*x1)/b;
    if (y1==(int)(y1)) {
      x0=x1; yy0=y1;
      found=TRUE;
    }
    else {
      x1=-x1; if (x1>=0) x1=x1+1;
      x2=(c-b*y2)/a;
      if (x2==(int)(x2)) {
        x0=x2; yy0=y2; found=TRUE;
      }
      else {
        y2=-y2; if (y2>=0) y2=y2+1;
      }
    }
  } while (!found);
  p=a; 
  q=b;

  printf("#Sols: %g,%g,%g,%g\n",x0, fabs(q),yy0,fabs(p));
  return TRUE;
}

//////



void daikon_test_dummy(int a, int b, int c, int d, 
                       int e, int f, int g, int h, int t, int y){
  //printf("%d %d %d %d\n",a,b,c,d);
  assert(a >= 5*b);
  assert(c >= 7*d+5);
  assert(e >= f);   
  assert(g >= h+8);
  assert(-t + 2 <= y);

  //Daikon results
  /*
  a != e
  a != y
  b != y
  c != g
  c != h
  c != y
  d != t
  d != y
  e >= f
  e != y
  f != t
  f != y
  g > h
  g != y
  h != t
  h != y
  */

}
int daikon_test(int k){
  int i = 0;
  int a = 0;
  int b = 0;
  int c = 0;
  int d = 0;
  int e = 0;
  int f = 0;
  int g = 0;
  int h = 0;
  int t = 0;
  int y = 0;
  for(; i < k; ++i){
    b = randrange_i(0,10000,INCLUDE) - randrange_i(0,1000,INCLUDE);
    a = (5*b)+randrange_i(0,50,INCLUDE);
    d = randrange_i(0,10000,INCLUDE) - randrange_i(0,1000,INCLUDE);
    c = 7*d+5 + randrange_i(0,50,INCLUDE);
    f = randrange_i(0,10000,INCLUDE) - randrange_i(0,1000,INCLUDE);
    e = f + randrange_i(0,10,INCLUDE);
    h =  randrange_i(0,10000,INCLUDE) - randrange_i(0,1000,INCLUDE);
    g = h + 8 + randrange_i(0,5,INCLUDE);
    t =  randrange_i(0,100000,INCLUDE);
    y = 2 - t + randrange_i(0,5,INCLUDE);

    daikon_test_dummy(a,b,c,d,e,f,g,h,t,y);
  }
  return k;
}




