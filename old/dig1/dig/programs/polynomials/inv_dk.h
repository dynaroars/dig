/* int dk_product(int m, int n){ */
/*   //smilar to prodbin in inv_nla.h */
/* } */


int dk_sqr(int t){
  int m = 0;
  int n = 0;
  int s = 0;
  int x = t;

  while(1){
    printf("li0: m n s x t\n");
    printf("li0: %d %d %d %d %d\n",m,n,s,x,t); 
    /*
      DI results
      0: m - 2*t + 2*x == 0
      1: n - 2*t + 2*x == 0
      2: t^2 - 2*t*x + x^2 - s == 0
    */
 
    if(!(x!=0)) break; 

    x = x - 1;
    n = m + 2;
    m = m + 1;

    while(1){
      printf("li1: m n s x t\n");
      printf("li1: %d %d %d %d %d\n",m,n,s,x,t); 
      /*
	DIG: results 
	0: n - 2*t + 2*x == 0
	1: t^2 - 2*t*x + x^2 - m - s == 0
       */

      if(!(m!=0)) break;
      
      s = s + 1;
      m = m - 1;
    }
    m = n;
  }
  return s;
}



int dk_sqr1_helper(int t, int m){
  int t1 = t;
  int m1 = m;
  while(1){
    printf("li1: t1 m1 t m\n");
    printf("li1: %d %d %d %d\n",t1,m1,t,m); 
    /*
      DIG: results
      0: m - m1 + t - t1 == 0
      1: m1^2 - 2*m1*t + t^2 + 2*m1*t1 - 2*t*t1 + t1^2 - 2*m1 - 2*t - 2*t1 + 1 == 0
    */

    if(!(m1!=0)) break;
    t1 = t1 + 1;
    m1 = m1 - 1;
  }

  return t1;
}

int dk_sqr1(int t){
  int m = 0;
  int n = 0;
  int s = 0;
  int x = t;

  while(1){
    printf("li0: m n s x t\n");
    printf("li0: %d %d %d %d %d\n",m,n,s,x,t); 

    /*
      0: m - 2*t + 2*x == 0
      1: n - 2*t + 2*x == 0
      2: t^2 - 2*t*x + x^2 - s == 0

    */

    if(!(x!=0)) break; 

    x = x - 1;
    n = m + 2;

    s = dk_sqr1_helper(s,m+1);

    m = n;
  }
  return s;  
}


/* int dk91(int m){ */
/*   //similar as f91 in inv_allamigeon.h */
/* } */

int dk_exp (int a, int b){
  /* algorithm for computing the exp of two natural numbers */
  /* same strategy as prodbin  in inv_nla.h */

  assert(b>=0);

  int x,y,z;
  
  x = a;
  y = b;
  z = 1;

  while(1){ 
    printf("li0: a b x y z\n");
    printf("li0: %d %d %d %d %d\n", a,b,x,y,z);
    /*
      DIG: results
      No equalities up to deg 3
     */
    if (!(y != 0)) break;

    if (myodd(y)){
      z = z * x;
      y = y - 1;
    }
    x = x * x;
    y = y / 2;
  }
  assert(z == pow(a,b));
  printf("l_post: a b x y z\n");
  printf("l_post: %d %d %d %d %d\n", a,b,x,y,z);
  return z; 
}
  

int dk_exp1(int m, int n){
  int x = m;
  int y = n;
  int z = 0;
  int u = 1;

  while(1){
    printf("li0: m n x y z u\n");
    printf("li0: %d %d %d %d %d %d\n",m,n,x,y,z,u); 

    if(!(y != 0)) break;
    z = 0;
    while (1){
      printf("li1: m n x y z u\n");
      printf("li1: %d %d %d %d %d %d\n",m,n,x,y,z,u); 

      if(!(u != 0)) break;
      if(myodd(y)){
	z = x + z;
	u = u - 1;
      }
      x = x + x;
      u = u / 2;
    }
    
    x = m;
    y = y - 1;
    u = z;
  }
  return z;
}


int dk_exp2(int m, int n){
  int x = m;
  int y = n;
  int z = 0;
  int u = 1;
  int v = 1;

  while(1){
    printf("li0: m n x y z u v\n");
    printf("li0: %d %d %d %d %d %d %d\n",m,n,x,y,z,u,v); 

    if(!(y!=0)) break;

    if (myodd(y)){
      y = y - 1;
      u = x;
      v = z;
      z = 0;
      while (1) {
	printf("li1: m n x y z u v\n");
	printf("li1: %d %d %d %d %d %d %d\n",m,n,x,y,z,u,v); 

	if(!(u != 0)) break;

	if (myodd(u)){
	  z = z + v;
	  u = u - 1;
	}
	v = v + v ;
	u = u / 2 ;
      }
    }
    else{//y even
      y = y / 2;
      u = x;
      v = x;
      x = 0;

      while(1){
	printf("li2: m n x y z u v\n");
	printf("li2: %d %d %d %d %d %d\n",m,n,x,y,z,u,v); 

	if(!(u != 0)) break;

	if(myodd(u)){
	  x = x + v;
	  u = u - 1;
	}
	v = v + v;
	u = u / 2 ;
      }
    }
  }
  return z;
}

int driver_dk(char **argv){

  if (strcmp(argv[1],"dk_sqr") == 0){
    printf("#result = %d\n", 
	   dk_sqr(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"dk_sqr1") == 0){
    printf("#result = %d\n", 
	   dk_sqr1(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"dk_exp") == 0){
    printf("#result = %d\n", 
	   dk_exp(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"dk_exp1") == 0){
    printf("#result = %d\n", 
	   dk_exp1(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"dk_exp2") == 0){
    printf("#result = %d\n", 
	   dk_exp2(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }  
  return 0;
}
