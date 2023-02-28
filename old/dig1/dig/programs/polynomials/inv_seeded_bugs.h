/*
programs from NLA testsuite with seeded bugs
*/


int euclidex2_bug (int x, int y){
  /* extended Euclid's algorithm */
  /* Used as motivation example in proposal */

  int a,b,p,q,r,s;
    
  a=x;
  b=y;
  p=1;
  q=0;
  r=0;
  s=1;
  
  printf("x y a b p q r s\n");
  
  while(a!=b) { 


    printf("%d %d %d %d %d %d %d %d\n",x,y,a,b,p,r,q,s);


    if (a>b) {
      a = a+b;   //bug, should be a-b
      p = p-q; 
      r = r-s;
    }
    else {
      b = b-a; 
      q = q-p; 
      s = s-r;}

  }

  return a;
}//euclidex2
