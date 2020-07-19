/*
From Knuth's book - which vol ? 
 */


int knuth_gcd_n(int *arr, int n){
  //todo
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
  //todo
  //Knuth 4.5.2 Alg B
  //binary gcd

  int inp_u = u;
  int inp_v = v;
  
  int g = 1;

  printf("inp_u inp_v u v g\n");
  while(myeven(u) && myeven(v)){
    //printf("%d %d %d %d %d\n",inp_u, inp_v, u, v, g);
    g=2*g;
    u = u / 2;
    v = v / 2;
  }
  
  while(u > 0){
    printf("%d %d %d %d %d\n",inp_u, inp_v, u, v, g);
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

  assert(v*g==mygcd(inp_u,inp_v));
  return v*g;
}


int knuth_gcd_euclid(int u, int v){
  //todo
  // Knuth 4.5.2 Alg A
  // Euclid's gcd
  int inp_u = u;
  int inp_v = v;
  int r = 0; 

  printf("inp_u inp_v u v r\n");
  while(v != 0){
    printf("%d %d %d %d %d\n",inp_u, inp_v, u, v, r);
    r = u % v;
    u = v;
    v = r;
  }
  
  assert(u==mygcd(u,v));
  return u;
}


int knuth_factor_fermat(int N){
  //todo
  //Kuth 4.5.4 C
  //input an odd number N returns the largest factor of N <= sqrt(N)
  //using fermat method
  //very similar to the program 'fermat1'  in inv_arith_algs1


  //N has to be an odd number otherwise may loop forever
  //e.g., when N = 446
  //assert(N % 2 == 1); 
   
  int x = 2*floor(sqrt(N)) + 1;
  int y = 1;
  int r = pow(floor(sqrt(N)),2) - N;

  int ctr = 0 ;
  printf("N x y r\n");
  while(r != 0 && ctr < 250){

    //assert(4*(N+r) == pow(x,2) - pow(y,2) - 2*x + 2*y);

    printf("%d %d %d %d\n",N,x,y,r);

    ctr++;
    while(r<0){
      r = r + x ;
      x = x + 2 ;
    }
    
    while(r>0){
      r = r - y ;
      y = y + 2 ;
    }
    
    
  }
  
  int res = (x-y)/2;
  assert((float)res<=sqrt(N));
  return res;

  
}


int f_rand(int x,int n){
  return (int)(pow(x,2)+1) % n;
}

int knuth_factor_rho(int N){
  //todo
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

int driver_knuth(int argc, char **argv){
  if (strcmp(argv[1],"knuth_gcd_euclid")==0){
    printf("#result = %d\n", knuth_gcd_euclid(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"knuth_gcd_bin")==0){
    printf("#result = %d\n", knuth_gcd_bin(atoi(argv[2]),atoi(argv[3])));
    return 1;
  }
  else if(strcmp(argv[1],"knuth_gcd_n")==0){
    int size = argc-2;
    int *arr = (int *)malloc(sizeof(int[size]));
    int i = 0;
    for(i = 0; i < size; ++i){arr[i]=atoi(argv[2+i]);}
      
    printf("#result = %d\n", knuth_gcd_n(arr,size));
    free(arr);
    return 1;
  }
  else if (strcmp(argv[1],"knuth_factor_fermat")==0){
    printf("#result = %d\n", knuth_factor_fermat(atoi(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"knuth_factor_rho")==0){
    printf("#result = %d\n", knuth_factor_rho(atoi(argv[2])));
    return 1;
  }

  else if (strcmp(argv[1],"nr_diophantian")==0){
    printf("#result = %d\n", 
	   nr_diophantian(atof(argv[2]),atof(argv[3]),atof(argv[4])));
    return 1;
  }

  else if (strcmp(argv[1],"nr_prime")==0){
    printf("#result = %d\n", 
	   nr_prime(atof(argv[2])));
    return 1;
  }
  else if (strcmp(argv[1],"nr_factors")==0){
    printf("#result = %d\n", 
	   nr_factors(atof(argv[2])));
    return 1;
  }
  return 0;
}
