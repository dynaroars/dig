/*From Verification as Learning Geometric Concepts (lgc), Rahul Sharma */
int nondet(){
  // returns 0 or 1 randomly
  return randrange_i(0,1,INCLUDE);
}

int blast_nondet(){
  return nondet();
}

int blast(){
  return blast_nondet();
}


void lgc_test1(int y, int z){
  int lock,x;
  lock = 0;
  x = y;
  if (z>=0)
    {
      lock = 1;
      y++;
    }
  
  /* __loop_invariant( */
  /* 		   __requires((((1)*(0)) + ((x)*(1)) + ((y)*(-1)) + ((z)*(0)) + ((i)*(0)) + ((lock)*(1)))==0) */
  /*)*/
  while(TRUE)    {
    printf("li0: x y z\n");
    printf("li0: %d %d %d\n",x,y,z);

    if(!(x!=y))break;

      lock = 0;
      x = y;
      if (z>=	0)
	{
	  lock = 1;
	  y++;
	}
    }
  assert (lock == 0);
  //__hv_
}



void lgc_test2(int x, int y, int z, int i)
{
  //VU
  int lock = 1;
  int count = 0;
  {
    count++;
    lock = 0;
    x = y;
    if (z>=	1)
      {
	lock = 1;
	y++;
      }
  }
  /* __loop_invariant( */
  /* 		   __requires((((1)*(0)) + ((x)*(1)) + ((y)*(-1)) + ((z)*(0)) + ((i)*(0)) + ((lock)*(1)) + ((count)*(0)))==0) */
  /* 		   ) */
  while(TRUE)
    {
      printf("li0: x y z i c\n");
      printf("li0: %d %d %d %d %d\n",x,y,z,i,count);

      if(!(x!=y && count < 10)) break;

      count++;
      lock = 0;
      x = y;
      if (z>=	1)
	{
	  lock = 1;
	      y++;
	}
    }
  
  assert (!(lock != 0 &&  x == y));
  //__hv_assert (!(lock != 0 &&  x == y));
}



void glc_tacas06(int i, int j) {
  //VU: todo
  int x = i;
  int y = j;
  /* __loop_invariant( */
  /* 		   __requires((((1)*(0)) + ((x)*(1)) + ((y)*(-1)) + ((i)*(-1)) + ((j)*(1)))==0) */
  /* 		   ) */
  while(TRUE) {
    printf("li0: x y i j\n");
    printf("li0: %d %d %d %d\n",x,y,i,j);

    if(!(x!=0)) break;
    x--;
    y--;
  }
  if(i==j)
    assert(y == 0);
      //__hv_assert(y == 0);
}




/* int glc_ex23(unsigned int y){ */
/*   int x[4608];  */
/*    unsigned int counter=0U,z; */
/*    if ( 127 < y) return 0; */
/*    if ( y < 0) return 0; */
/*    z = y * 36U; */
/* /\* __loop_invariant( *\/ */
/* /\* __requires((((1)*(0)) + ((y)*(36)) + ((z)*(-1)) + ((counter)*(1)))==0) *\/ */
/* /\* ) *\/ */
/*    while (counter < 36U){ */
/*       x[z] =0; */
/*       //__hv_assert(z<4608); */
/*       assert(z<4608); */
/*       z++; */
/*       counter++; */
/*    } */

/*    return 1; */

/* } */

int glc_ex23(int y){

  int x[4608]; 
   int counter=0,z;
   if ( 127 < y) return 0;
   if ( y < 0) return 0;
   z = y * 36;
/* __loop_invariant( */
/* __requires((((1)*(0)) + ((y)*(36)) + ((z)*(-1)) + ((counter)*(1)))==0) */
/* ) */
   while (TRUE){
     //printf("li0: x y z c\n");
     //printf("li0: %d %d %d %d\n",x,y,z,counter);

     if(!(counter < 36)) break;
      x[z] =0;
      //__hv_assert(z<4608);
      assert(z<4608);
      z++;
      counter++;
   }

   return 1;

}


void glc_fig6()
{
  int y= 2;
  int x = 0;
  /* __loop_invariant( */
  /* 		   __requires((((1)*(0)) + ((x)*(1)) + ((y)*(0)))==0) */
  /* 		   ) */
    while (y >0)
      {
	y = y-1;
      }
    //__hv_assert(x==0);
    assert(x==0);
}


int glc_fig9()
{
  int x, y;
  x = 0;
  y = 0;
  /* __loop_invariant( */
  /* 		   __requires((((1)*(0)) + ((x)*(1)) + ((y)*(0)))==0) */
  /* 		   __requires((((1)*(0)) + ((x)*(0)) + ((y)*(1)))==0) */
  /* 		   ) */
  while ( y >= 0) {
    y = y + x;
  }
  //__hv_assert(0);
  assert(0);
}



void glc_prog2()
{
  //VU: TODo
  int x;
  int y;

  x = 0;
  y = 0;
/* __loop_invariant( */
/* __requires(x==y) */
/* ) */
  while (x <= 9)
  {
    x = x+1;
    y = y+1;
  }
  //__hv_assert(y>=0);
  assert(y>=0);
}





void glc_prog3()
{
  //VU: disjunctive invs

  int x;
  int y;
  int z;
  x = 0;
  y = 9;
/* __loop_invariant( */
/* __requires((((1)*(-9)) + ((x)*(0)) + ((y)*(1)))==0) */
/* ) */
  while (x <= 9)
  {
    x = x + 1;
  }
  //__hv_assert(y==9);
  assert(y==9);
}



void glc_prog4(int N, int b)
{
  int x;
  int y;

  x = 0;
  y = 0;

  /* disj */
  /* __loop_invariant( */
  /* __requires(( ( (((0)*(1)) + ((1)*(x)) + ((-1)*(y)) + ((0)*(b)))>=0 && (((0)*(1)) + ((-1)*(x)) + ((-1)*(y)) + ((0)*(b)))>=0 && !((((0)*(1)) + ((0)*(x)) + ((0)*(y)) + ((1)*(b)))>=0) ) || ( (((0)*(1)) + ((1)*(x)) + ((1)*(y)) + ((0)*(b)))>=0 && (((0)*(1)) + ((-1)*(x)) + ((1)*(y)) + ((0)*(b)))>=0 && (((0)*(1)) + ((0)*(x)) + ((0)*(y)) + ((1)*(b)))>=0 )  )) */
  /* ) */
  while (nondet())
    {
    if (0 <= b)
      y = y + 1;
    else
      y = y - 1;
    x = x + 1;
  }


  //__hv_assert ((y ==0) || (y  >= 0 && b >= 0) || (b <= -1 && y <= 0));
  assert ((y ==0) || (y  >= 0 && b >= 0) || (b <= -1 && y <= 0));
}

void glc_prog5()
{
  int x;
  int z;
  int y;
  y = 9;
  x = 0;
/* __loop_invariant( */
/* __requires((((1)*(-9)) + ((x)*(0)) + ((y)*(1)) + ((z)*(0)))==0) */
/* ) */
  for (;x<9;x++)
  {
    z = z + 1;
  }
  //__hv_assert(y==9);
  assert(y==9);
}


void glc_down() {
  int n;
  int k = 0;
  int i = 0;
  int j;
  if(i<n){
    /* __loop_invariant( */
    /* 		     __requires(i==k) */
    /* 		     __requires(n>=i) */
    /* 		     ) */
    while( i < n ) {
      i++;
      k++;
    }
  }
  j = n;
  if(j>0){
    /* __loop_invariant( */
    /* 		     __requires(i==n) */
    /* 		     __requires(j==k) */
    /* 		     ) */
      while( j > 0 ) {
	//__hv_assert(k > 0)
	assert(k>0);
	j--;
	k--;
      }
  }
}



void glc_gopan()
{
  int x,y;
  x=0;y=0;
  if(x<=50)y++;
  else {y--;}
  /* __loop_invariant( */
  /* 		   __requires(( ( (((-101)*(1)) + ((1)*(x)) + ((1)*(y)))>=0 && (((101)*(1)) + ((-1)*(x)) + ((-1)*(y)))>=0 && (((1)*(1)) + ((1)*(x)) + ((-1)*(y)))>=0 && (((1)*(1)) + ((0)*(x)) + ((1)*(y)))>=0 ) || ( (((-1)*(1)) + ((-1)*(x)) + ((1)*(y)))>=0 && !((((-101)*(1)) + ((1)*(x)) + ((1)*(y)))>=0) && (((1)*(1)) + ((1)*(x)) + ((-1)*(y)))>=0 && (((-1)*(1)) + ((0)*(x)) + ((1)*(y)))>=0  )  )) */
  /* 		   ) */
  while(TRUE){
    printf("li0: x y\n");
    printf("li0: %d %d\n",x,y);

    if(!(y>=0)) break;

    x++;
    if(x<=50)y++;
    else {y--;}
  }
  //__hv_assert(x==102);
  assert(x==102);
}


void glc_popl07()
{
  int x,y;
  x=0;y=50;
/* __loop_invariant( */
/* __requires(( ( (((-50)*(1)) + ((0)*(x)) + ((1)*(y)))>=0 && (((50)*(1)) + ((0)*(x)) + ((-1)*(y)))>=0 && (((0)*(1)) + ((-1)*(x)) + ((1)*(y)))>=0 && (((0)*(1)) + ((1)*(x)) + ((0)*(y)))>=0  ) || ( !((((50)*(1)) + ((0)*(x)) + ((-1)*(y)))>=0) && (((0)*(1)) + ((1)*(x)) + ((-1)*(y)))>=0 && (((0)*(1)) + ((-1)*(x)) + ((1)*(y)))>=0 && (((100)*(1)) + ((-1)*(x)) + ((0)*(y)))>=0 )  )) */
/* ) */
  while(x<100)
    {
      if(x<50)x++;
      else {x++;y++;}
      
    }
  //__hv_assert(y==100)
  assert(y==100);
    //return 0;
}



//This is nested2
void glc_nested(int n, int l) {
  int i,k;

  if(l>0);else goto END;
  k=1;

/* __loop_invariant( */
/* __requires((((-1)*(1)) + ((0)*(i)) + ((0)*(l)) + ((1)*(k)) + ((0)*(n)))>=0) */
/* ) */
  for (;k<n;k++){
    //__hv_assert(k<=n);
    //__hv_assert(1<=k)__hv_assert(1<=j);;
    /* __loop_invariant( */
    /* __requires((((-1)*(1)) + ((0)*(i)) + ((0)*(l)) + ((1)*(k)) + ((0)*(n)))>=0) */
    /* ) */
    
    for (i=l;i<n;i++) {
      //__hv_assert(1<=i);
      //__hv_assert(i<=n);
    }

    /* __loop_invariant( */
    /* __requires((((-1)*(1)) + ((0)*(i)) + ((0)*(l)) + ((1)*(k)) + ((0)*(n)))>=0) */
    /* ) */
    for (i=l;i<n;i++) {
      //__hv_assert(1<=k);
      assert(1<=k);
    }
   
  }
  
 END:;
}




void glc_seq_len(int n0, int n1, int n2) {
  int i = 0;
  int k = 0;
  /* __loop_invariant( */
  /* __requires(i==k) */
  /* ) */

  while( i < n0 ) {
    i++;
    k++;
  }
  //__hv_assert(k>=n0)
  assert(k>=n0);

  i=0;
  /* __loop_invariant( */
  /* __requires(k>=n0) */
  /* __requires(k>=n0+i) */
  /* ) */
  while( i < n1 ) {
    i++;
    k++;
  }  
  /* __hv_assert(k>=n0)   */
  /* __hv_assert(k>=n0+n1) */
  assert(k>=n0)   ;
  assert(k>=n0+n1);
  
  i=0;

  /* __loop_invariant( */
  /* __requires(k>=n0) */
  /* __requires(k>=n0+i) */
  /* __requires(k>=n0+n1) */
  /* __requires(k>=n0+n1+i) */
  /* ) */

  while( i < n2 ) {
    i++;
    k++;
  }
  /* __hv_assert(k>=n0) */
  /* __hv_assert(k>=n0+n2)   */
  /* __hv_assert(k>=n0+n1) */
  /* __hv_assert(k>=n0+n1+n2) */
  
    i=0;
  /* __loop_invariant( */
  /* __requires(k>=n0) */
  /* __requires(k+i>=n0+n2)   */
  /* __requires(k>=n0+n1) */
  /* __requires(k+i>=n0+n1+n2) */
  /* ) */

  while( i < n2 ) {
    i++;
    k--;
  }  
  /* __hv_assert(k>=n0) */
  /* __hv_assert(k>=n0+n1) */
  assert(k>=n0);
  assert(k>=n0+n1)  ;

  i=0;
  /* __loop_invariant( */
  /* __requires(k+i>=n0+n1) */
  /* __requires(k>=n0) */
  /* ) */

  while( i < n1 ) {
    i++;
    k--;
  }
  
  //__hv_assert(k>=n0)
  assert(k>=n0);
  i=0;
  /* __loop_invariant( */
  /* __requires(k+i>=n0) */
  /* ) */

  while( i < n0 ) {
    //__hv_assert(k > 0);
    assert(k > 0);

    i++;
    k--;
  }
  
}



int glc_seq_len_light(int n0, int n1, int n2) {
  int i = 0;
  int k = 0;
/* __hv_assume(n0>0) */
/* __hv_assume(n1>0) */
/* __hv_assume(n2>0) */
  assert(n0>0);
  assert(n1>0);
  assert(n2>0);

if(i<n0)
{
/* __loop_invariant( */
/* __requires((((1)*(0)) + ((i)*(-1)) + ((k)*(1)) + ((n0)*(0)) + ((n1)*(0)) + ((n2)*(0)))==0) */
/* __requires((((0)*(1)) + ((-1)*(i)) + ((0)*(k)) + ((1)*(n0)) + ((0)*(n1)) + ((0)*(n2)))>=0) */
/* ) */
  while( i < n0 ) {
    i++;
    k++;
  }
}  

  i = 0;
 if(i<n1){ 
/*  __loop_invariant( */
/* __requires((((1)*(0)) + ((i)*(-1)) + ((k)*(1)) + ((n0)*(-1)) + ((n1)*(0)) + ((n2)*(0)))==0) */
/* __requires((((0)*(1)) + ((-1)*(i)) + ((0)*(k)) + ((0)*(n0)) + ((1)*(n1)) + ((0)*(n2)))>=0) */
/* ) */
  while( i < n1 ) {
    i++;
    k++;
  }
}

  i = 0;
if(i<n2){  
/* __loop_invariant( */
/* __requires((((1)*(0)) + ((i)*(-1)) + ((k)*(1)) + ((n0)*(-1)) + ((n1)*(-1)) + ((n2)*(0)))==0) */
/* __requires((((0)*(1)) + ((-1)*(i)) + ((0)*(k)) + ((0)*(n0)) + ((0)*(n1)) + ((1)*(n2)))>=0) */
/* ) */
  while( i < n2 ) {
    i++;
    k++;
  }
}

  i = 0;
 if(i<n2)
{ 
/* __loop_invariant( */
/* __requires((((1)*(0)) + ((i)*(1)) + ((k)*(1)) + ((n0)*(-1)) + ((n1)*(-1)) + ((n2)*(-1)))==0) */
/* __requires((((0)*(1)) + ((-1)*(i)) + ((0)*(k)) + ((0)*(n0)) + ((0)*(n1)) + ((1)*(n2)))>=0) */
/* ) */
  while( i < n2 ) {
    i++;
    k--;
  }
}

  i = 0;
if(i<n1)
{  
/* __loop_invariant( */
/* __requires((((1)*(0)) + ((i)*(1)) + ((k)*(1)) + ((n0)*(-1)) + ((n1)*(-1)) + ((n2)*(0)))==0) */
/* __requires((((0)*(1)) + ((-1)*(i)) + ((0)*(k)) + ((0)*(n0)) + ((1)*(n1)) + ((0)*(n2)))>=0) */
/* ) */
  while( i < n1 ) {
    i++;
    k--;
  }
}  

  i = 0;
if(i<n0)
{  
/* __loop_invariant( */
/* __requires((((1)*(0)) + ((i)*(1)) + ((k)*(1)) + ((n0)*(-1)) + ((n1)*(0)) + ((n2)*(0)))==0) */
/* __requires((((0)*(1)) + ((-1)*(i)) + ((0)*(k)) + ((1)*(n0)) + ((0)*(n1)) + ((0)*(n2)))>=0) */
/* ) */

  while( i < n0 ) {
    //__hv_assert(k > 0);
    assert (k > 0);
    i++;
    k--;
  }
}  
}


void glc_svd(int n,int l)
{
  int i,j,k;
  
  if(l>0);else goto END;
  i=n;

  for (;i>=1;i--) { // Accumulation of right-hand transformations. 
    if (i < n) {
      if (nondet() ) {

/* __loop_invariant( */
/* __requires((((-1)*(1)) + ((-1)*(i)) + ((1)*(n)))>=0) */
/* ) */
	  for (j=l;j<=n;j++) { // Double division to avoid possible underflow.   
	  //__hv_assert(1<=j);//__hv_assert(j<=n);
	  // __hv_assert(1<=i);__hv_assert(i<=n);
	  // __hv_assert(1<=i);__hv_assert(i<=m); // TODO feasible counterexample found
	  //__hv_assert(1<=l);__hv_assert(l<=n);
	}

/* __loop_invariant( */
/* __requires((((-1)*(1)) + ((-1)*(i)) + ((1)*(n)))>=0) */
/* ) */
	for (j=l;j<=n;j++) {

/* __loop_invariant( */
/* __requires((((-1)*(1)) + ((-1)*(i)) + ((1)*(n)))>=0) */
/* ) */
	for (k=l;k<=n;k++) { 
	    //__hv_assert(1<=i);__hv_assert(i<=m); // TODO feasible counterexample found
	    //__hv_assert(1<=k);__hv_assert(k<=n);
	    //__hv_assert(1<=j);__hv_assert(j<=n);
	  }

/* __loop_invariant( */
/* __requires((((-1)*(1)) + ((-1)*(i)) + ((1)*(n)))>=0) */
/* ) */
	  for (k=l;k<=n;k++) { 
	    //__hv_assert(1<=k);__hv_assert(k<=n);
	    //__hv_assert(1<=j);__hv_assert(j<=n);
	    /*__hv_assert(1<=i);__hv_assert(i<=n);*/
	    assert(1<=i);
	    assert(i<=n);
	  }
	}
      }
      for (j=l;j<=n;j++) { 
        //__hv_assert(1<=j);
	//__hv_assert(j<=n);
	//__hv_assert(1<=i);
	//__hv_assert(i<=n);
      }
    }
    
    //__hv_assert(1<=i);
    //__hv_assert(i<=n);
    //__hv_assert(1<=i);
    //__hv_assert(i<=n);
    l=i;

	}
  END:;
}


/* good way to abstract semantics of program involving arrays or pointers */
void glc_heapsort(int n){
  int l,r,i,j;

  // tmpl("(le(n,l,r,i,j),le(n,l,r,i,j))");
  
  if(1 <= n);else goto END;
  l = (n/2) + 1;
  r = n;
  if(l>1) {
    l--;
  } else {
    r--;
  }
  if(r>1){
    /* __loop_invariant( */
    /* 		     __requires(l>=1 &&( ( (((0)*(1)) + ((1)*(n)) + ((0)*(l)) + ((-1)*(r)))>=0 && (((-1)*(1)) + ((1)*(n)) + ((-1)*(l)) + ((0)*(r)))>=0 )  )) */
    /* 		     ) */
  while(r > 1) {
    i = l;
    j = 2*l;
/* 	__loop_invariant( */
/* __requires((((1)*(0)) + ((n)*(0)) + ((l)*(0)) + ((r)*(0)) + ((i)*(-2)) + ((j)*(1)))==0) */
/* __requires(( ( (((0)*(1)) + ((1)*(n)) + ((0)*(l)) + ((-1)*(r)) + ((0)*(i)) + ((0)*(j)))>=0 && (((-1)*(1)) + ((0)*(n)) + ((0)*(l)) + ((0)*(r)) + ((1)*(i)) + ((0)*(j)))>=0 && (((-1)*(1)) + ((1)*(n)) + ((-1)*(l)) + ((0)*(r)) + ((0)*(i)) + ((0)*(j)))>=0 )  )) */
/* ) */
    while(j <= r) {
      if( j < r) {
	/*__hv_assert(1 <= j);__hv_assert(j <= n);
	  __hv_assert(1 <= j+1);__hv_assert(j+1 <= n);*/
	assert(1 <= j); assert(j <= n);
	assert(1 <= j+1); assert(j+1 <= n);

	if(blast_nondet())
	  j = j + 1;
      }
      /*__hv_assert(1 <= j);__hv_assert(j <= n);*/
      assert(1 <= j);
      assert(j <= n);
      if(blast_nondet) {
      	break;
      }
      /* __hv_assert(1 <= i); */
      /* __hv_assert(i <= n); */
      /* __hv_assert(1 <= j); */
      /* __hv_assert(j <= n); */
      assert(1 <= i);
      assert(i <= n);
      assert(1 <= j);
      assert(j <= n);
      i = j;
      j = 2*j;
    }
    if(l > 1) {
      //__hv_assert(1 <= l);__hv_assert(l <= n);
      assert(1 <= l);
      assert(l <= n);
      l--;
    } else {
      assert(1 <= r);
      assert(r <= n);
      r--;
    }
  }
  }
 END:;
}

void glc_mergesort(int n)
{ 
  int i,t,k;
  int l,r,u,j;

  int x,y,z;

  x=1;
/* __loop_invariant( */
/* __requires((((-1)*(1)) + ((0)*(n)) + ((1)*(x)) + ((0)*(z)))>=0) */
/* ) */
  while (x<n) {
    z=1;
/* 	__loop_invariant( */
/* __requires((((-1)*(1)) + ((0)*(n)) + ((1)*(x)) + ((0)*(z)))>=0) */
/* ) */
    while (z+x<=n) {
      y=z+x*2;
      if (y>n) y=n+1;
      //      merge(z,z+x,y);
      l = z; r = z+x; u = y;
      i=l; j=r; k=l;
/* __loop_invariant( */
/* __requires((((1)*(0)) + ((i)*(-1)) + ((j)*(-1)) + ((k)*(1)) + ((l)*(0)) + ((r)*(1)) + ((u)*(0)) + ((n)*(0)) + ((x)*(0)) + ((y)*(0)) + ((z)*(0)))==0) */
/* __requires((((1)*(0)) + ((i)*(-1)) + ((j)*(-1)) + ((k)*(1)) + ((l)*(1)) + ((r)*(0)) + ((u)*(0)) + ((n)*(0)) + ((x)*(1)) + ((y)*(0)) + ((z)*(0)))==0) */
/* __requires((((1)*(0)) + ((i)*(0)) + ((j)*(0)) + ((k)*(0)) + ((l)*(0)) + ((r)*(0)) + ((u)*(-1)) + ((n)*(0)) + ((x)*(0)) + ((y)*(1)) + ((z)*(0)))==0) */
/* __requires((((1)*(0)) + ((i)*(0)) + ((j)*(0)) + ((k)*(0)) + ((l)*(-1)) + ((r)*(0)) + ((u)*(0)) + ((n)*(0)) + ((x)*(0)) + ((y)*(0)) + ((z)*(1)))==0) */
/* __requires((((0)*(1)) + ((0)*(i)) + ((0)*(j)) + ((-1)*(k)) + ((0)*(l)) + ((0)*(r)) + ((0)*(u)) + ((1)*(n)) + ((0)*(x)) + ((0)*(y)) + ((0)*(z)))>=0) */
/* ) */
      while (i<r && j<u) { 
	//	__hv_assert(0<=i);__hv_assert(i<=n);
	//__hv_assert(0<=j);__hv_assert(j<=n);
	if(i<r-1) {
	//if (a[i]<=a[j]) {
	  //__hv_assert(0<=i);__hv_assert(i<=n);
	  //__hv_assert(0<=k);__hv_assert(k<=n);
	  //b[k]=a[i]; 
	  i++;
	} 
	else {
	  //__hv_assert(0<=j);__hv_assert(j<=n);
	  //__hv_assert(0<=k);__hv_assert(k<=n);	  
	  //b[k]=a[j]; 
	  j++;
	}
	k++;
      }
      //__hv_assert(0<=r);__hv_assert(r<=n);
      
      /*__hv_assert(k<=n);*/
      assert(k<=n);
      
      while (i<r) {
	//__hv_assert(0<=i);__hv_assert(i<=n);
	//__hv_assert(0<=k);__hv_assert(k<=n);
	//b[k]=a[i]; 
	i++; 
	k++;
      }
      while (j<u) { 
	//__hv_assert(0<=j);__hv_assert(j<=n);
	//__hv_assert(0<=k);__hv_assert(k<=n);
	//b[k]=a[j]; 
	j++; k++;
      }
      for (k=l; k<u; k++) { 
	//__hv_assert(0<=k);__hv_assert(k<=n);
	//a[k]=b[k]; 
      }
      
      z=z+x*2;
    }
    x=x*2;
  }
}

/*
main()
{ printf("input size \n");
  scanf("%d",&n); 
  for (i=1;i<=n;i++) a[i]=random()%1000;
  t=clock();
  sort1();
  for (i=1;i<=10;i++) printf("%d ",a[i]);
  printf("\n");
  printf("time= %d millisec\n",(clock()-t)/1000);
}
*/


int glc_sendmail_qp(void)
{
  int outfilelen;
  //  char outfile[BASE_SZ]; // originally MAXLINE
    // originally a function argument **ooutfile; this function modified
    // caller's pointer into outbut buffer

  //int c1, c2;

  // number of chars copied from infile into outfile; reset when
  // continuation sequence "=\n" is read
  int nchar = 0;

  int out = 0; // index into outfile

  //tmpl("(le(nchar,out,outfilelen),le(nchar,out,outfilelen),le(nchar,out,outfilelen))");

  if(outfilelen > 0); else goto RETURN;

  //  while ((c1 = nondet_char ()) != EOS) 
/*   __loop_invariant( */
/* __requires(( ( (((-1)*(1)) + ((0)*(nchar)) + ((-1)*(out)) + ((1)*(outfilelen)))>=0 && (((0)*(1)) + ((0)*(nchar)) + ((1)*(out)) + ((0)*(outfilelen)))>=0 && (((0)*(1)) + ((1)*(nchar)) + ((-1)*(out)) + ((0)*(outfilelen)))>=0 )  )) */
/* ) */

  while(blast_nondet())
  {
    //    if (c1 == '=')
    if(blast_nondet())
    {
      // malformed: early EOS
      //      if ((c1 = nondet_char ()) == EOS)
      if(blast_nondet())
	// in Zitser, these breaks actually return to the caller where the
	// pointer into outfile is reset before this is called again
	goto AFTERLOOP; 

      // =\n: continuation; signal to caller it's ok to pass in more infile
      // OK: reset out before taking more input
      //if (c1 == '\n')
      if(blast_nondet())
      {
	out = 0;
	nchar = 0;
	goto LOOPEND;
      }
      else
      {
	// convert, e.g., "=5c" to int

	// malformed: early EOF
	//if ((c2 = nondet_char ()) == EOS)
	if(blast_nondet())  goto AFTERLOOP;

	nchar++;
	if (nchar >= outfilelen)
	  goto AFTERLOOP;

	/* OK */
	/* __hv_assert(0<=out);//1 */
	/* __hv_assert(out<outfilelen);//2 */
	assert(0<=out);
	assert(out<outfilelen);
	// outfile[out] = c1;
	out++;
      }
    }
    else
    {
      // regular character, copy verbatim

      nchar++;
      if (nchar >= outfilelen)
	goto AFTERLOOP;

      /* OK */
      /* __hv_assert(0<=out);//3 */
      /* __hv_assert(out<outfilelen);//4 */
      assert(0<=out);//3
      assert(out<outfilelen);//4

      //  outfile[out] = c1;
      out++;

      //if (c1 == '\n')
      if(blast_nondet()) goto AFTERLOOP;
    }
  LOOPEND:;
  }
 AFTERLOOP:;

  /* OK */
  /* __hv_assert(0<=out);//5 */
  /* __hv_assert(out<outfilelen); */
  assert(0<=out);//5
  assert(out<outfilelen); 

  //  outfile[out] = EOS;
  out++;
 RETURN:  return 0;
}



void glc_spam_assassin(int len, int bufsize)
{
  int i,j;
  int limit = bufsize - 4;
/* __loop_invariant( */
/* __requires((((1)*(4)) + ((i)*(0)) + ((j)*(0)) + ((len)*(0)) + ((bufsize)*(-1)) + ((limit)*(1)))==0) */
/* __requires((((0)*(1)) + ((1)*(i)) + ((0)*(j)) + ((0)*(len)) + ((0)*(bufsize)) + ((0)*(limit)))>=0) */
/* ) */
  for (i = 0; i < len; ) {
/* __loop_invariant( */
/* __requires((((1)*(4)) + ((i)*(0)) + ((j)*(0)) + ((len)*(0)) + ((bufsize)*(-1)) + ((limit)*(1)))==0) */
/* __requires((((0)*(1)) + ((1)*(i)) + ((0)*(j)) + ((0)*(len)) + ((0)*(bufsize)) + ((0)*(limit)))>=0) */
/* ) */
    for (j = 0; i < len && j < limit; ){     
	if (i + 1 < len){ 
	//__hv_assert(i+1<len);//1
	//__hv_assert(0<=i);//2//Interesting __hv_assert
	if( nondet() ) goto ELSE;
        //__hv_assert(i<len);//3
	//__hv_assert(0<=i); //4
        //__hv_assert(j<bufsize);//5 //Interesting Assert
	//__hv_assert(0<=j);	
	//        buffer[j] = msg[i];
        j++;
        i++;
        //__hv_assert(i<len);//6
	//__hv_assert(0<=i);//7
        // __hv_assert(j<bufsize);//8 //Very intersting
	//__hv_assert(0<=j);	//9

	//        buffer[j] = msg[i];
        j++;
        i++;
        //__hv_assert(j<bufsize);//10
	//__hv_assert(0<=j);	//11
        /* OK */
	//        buffer[j] = '.';
        j++;
      } else {
ELSE:
        //__hv_assert(i<len);//12
	  //__hv_assert(0<=i);//Really really interesting
	  assert(0<=i);
        //__hv_assert(j<bufsize);//13
	//__hv_assert(0<=j);	//14
	
	//	buffer[j] = msg[i];
        j++;
        i++;
      }
    }
  }
}


//0<=cp<=urilen & 0<=c<=tokenlen

void glc_ap_esc_abs ()
{
  int scheme;
  int urilen,tokenlen;
  int cp,c;
  //  char *token[TOKEN_SZ];

  //tmpl("(le(scheme,urilen,tokenlen,cp,c),le(scheme,urilen,tokenlen,cp,c))");
  if(urilen>0); else goto END;
  if(tokenlen>0); else goto END;
  if(scheme >= 0 );else goto END;
  if (scheme == 0
      || (urilen-1 < scheme)) {
    goto END;
  }

  cp = scheme;
  
  /* __hv_assert(cp-1 < urilen); */
  /* __hv_assert(0 <= cp-1); */
  assert(cp-1 < urilen);
  assert(0 <= cp-1);

  if (blast()) {
/*     __hv_assert(cp < urilen); */
/*     __hv_assert(0 <= cp); */
    assert(cp < urilen);
    assert(0 <= cp);
/* 	__loop_invariant( */
/* __requires(( ( (((-1)*(1)) + ((-1)*(cp)) + ((0)*(scheme)) + ((1)*(urilen)) + ((0)*(tokenlen)))>=0 && (((-1)*(1)) + ((1)*(cp)) + ((0)*(scheme)) + ((0)*(urilen)) + ((0)*(tokenlen)))>=0 )  )) */
/* ) */
    while ( cp != urilen-1) {
      if(blast()) break;
      /* __hv_assert(cp < urilen); */
      /* __hv_assert(0 <= cp); */
      assert(cp < urilen);
      assert(0 <= cp);

      ++cp;
    }
    /* __hv_assert(cp < urilen); */
    /* __hv_assert( 0 <= cp ); */
    assert(cp < urilen);
    assert( 0 <= cp );

    if (cp == urilen-1) goto END;
    /* __hv_assert(cp+1 < urilen); */
    /* __hv_assert( 0 <= cp+1 ); */
    assert(cp+1 < urilen);
    assert( 0 <= cp+1 );

    if (cp+1 == urilen-1) goto END;
    ++cp;

    scheme = cp;

    if (blast()) {
      c = 0;
      //token[0] = uri;
      /* __hv_assert(cp < urilen); */
      /* __hv_assert(0<=cp); */
      assert(cp < urilen);
      assert(0<=cp);

/* 	  __loop_invariant( */
/* __requires(( ( (((-1)*(1)) + ((-1)*(cp)) + ((0)*(scheme)) + ((1)*(urilen)) + ((0)*(tokenlen)) + ((0)*(c)))>=0 && (((-1)*(1)) + ((1)*(cp)) + ((0)*(scheme)) + ((0)*(urilen)) + ((0)*(tokenlen)) + ((0)*(c)))>=0 && (((0)*(1)) + ((0)*(cp)) + ((0)*(scheme)) + ((0)*(urilen)) + ((0)*(tokenlen)) + ((1)*(c)))>=0 )  )) */
/* ) */

      while ( cp != urilen-1
             && c < tokenlen - 1) {
	/* __hv_assert(cp < urilen); */
	/* __hv_assert(0<=cp); */

	assert(cp < urilen);
	assert(0<=cp);
	
        if (blast()) {
          ++c;
          /* OK */
	  /* __hv_assert(c < tokenlen); */
	  /* __hv_assert(0<=c); */
	  assert(c < tokenlen);
	  assert(0<=c);

          //token[c] = uri + cp + 1;
	  /* __hv_assert(cp < urilen); //Interesting __hv_assert */
	  /* __hv_assert(0<=cp); */
	  assert(cp < urilen); //Interesting __hv_assert
	  assert(0<=cp);

          //uri[cp] = EOS;
        }
        ++cp;
      }
      goto END;
    }
  }

 END:;
}

void glc_ap_get_tag()
{
  int tagbuf_len;
  int t;

  //tmpl("(le(tagbuf_len, t), le(tagbuf_len, t))");
  //  tmpl("le(tagbuf_len, t)");
  
  if(tagbuf_len >= 1); else goto END;

  t = 0;

  --tagbuf_len;
  /*
  do {
    GET_CHAR(c, NULL);
  } while (ap_isspace(c));
  */

  /*
  if (c == '-') {
    GET_CHAR(c, NULL);
    if (c == '-') {
      do {
        GET_CHAR(c, NULL);
      } while (ap_isspace(c));
      if (c == '>') {
        ap_cpystrn(tag, "done", tagbuf_len);
        return tag;
      }
    }
    return NULL;
  }
  */
/* __loop_invariant( */
/* __requires(( ( (((0)*(1)) + ((-1)*(t)) + ((1)*(tagbuf_len)))>=0 && (((0)*(1)) + ((1)*(t)) + ((0)*(tagbuf_len)))>=0 )  )) */
/* ) */

  while (1) {
    if (t == tagbuf_len) {
      /* __hv_assert(0 <= t); */
      /* __hv_assert(t <= tagbuf_len); */

      assert(0 <= t);
      assert(t <= tagbuf_len);

      //      tag[t] = EOS;
      goto END;
    }
    if (blast_nondet()) {
      break;
    }
    /* __hv_assert(0 <= t); */
    /* __hv_assert(t <= tagbuf_len); */

    assert(0 <= t);
    assert(t <= tagbuf_len); 

    //    tag[t] = ap_tolower(c);
    t++;
    //    GET_CHAR(c, NULL);
  }

   /* __hv_assert(0 <= t); */
   /* __hv_assert(t <= tagbuf_len); */
  
  assert(0 <= t);
  assert(0 <= t);

  //  tag[t] = EOS;
  t++;
  //  tag_val = tag + t;
  /*
  while (ap_isspace(c)) {
    GET_CHAR(c, NULL);
  }
  if (c != '=') {
    return NULL;
  }

  do {
    GET_CHAR(c, NULL);
  } while (ap_isspace(c));

  if (c != '"' && c != '\'') {
    return NULL;
  }
  term = c;
  */
/*   __loop_invariant( */
/* __requires(( ( (((0)*(1)) + ((-1)*(t)) + ((1)*(tagbuf_len)))>=0 && (((0)*(1)) + ((1)*(t)) + ((0)*(tagbuf_len)))>=0 )  )) */
/* ) */

  while (1) {
    //    GET_CHAR(c, NULL);
    if (t == tagbuf_len) { /* Suppose t == tagbuf_len - 1 */
      /* __hv_assert(0 <= t); */
      /* __hv_assert(t <= tagbuf_len); */
      assert(0 <= t);
      assert(t <= tagbuf_len);
      //      tag[t] = EOS;
      goto END;
    }

    if (blast_nondet()) {
      //      GET_CHAR(c, NULL);
      if ( blast_nondet()) {
        /* OK */
	/* __hv_assert(0 <= t); */
	/* __hv_assert(t <= tagbuf_len); // interesting __hv_assert, t2. */

	assert(0 <= t);
	assert(t <= tagbuf_len); // interesting __hv_assert, t2.

	//        tag[t] = '\\';
        t++;
        if (t == tagbuf_len) {
          /* OK */
	  /* __hv_assert(0 <= t); */
	  /* __hv_assert(t <= tagbuf_len); */


	  assert(0 <= t);
	  assert(t <= tagbuf_len);

	  //          tag[t] = EOS;
          goto END;
        }
      }
    }
    else if ( blast_nondet()) {
      break;
    }

    /* OK */
    /* __hv_assert(0 <= t); */
    /* __hv_assert(t <= tagbuf_len); */
    assert(0 <= t);
    assert(t <= tagbuf_len);

    //    tag[t] = c;    
    t++;                /* Now t == tagbuf_len + 1 
                         * So the bounds check (t == tagbuf_len) will fail */
  }
  /* OK */ 
  /* __hv_assert(0 <= t); */
  /* __hv_assert(t <= tagbuf_len); */
  assert(0 <= t);
  assert(t <= tagbuf_len);

  //  tag[t] = EOS;

  END:;
}


int driver_lgc(char **argv){
  if (strcmp(argv[1],"lgc_test1")==0){
    lgc_test1(atoi(argv[2]),atoi(argv[3]));
    return 1;
  }
  
  else if (strcmp(argv[1],"glc_tacas06")==0){
    glc_tacas06(atoi(argv[2]),atoi(argv[3]));
    return 1;
  }
  else if (strcmp(argv[1],"glc_gopan")==0){
    glc_gopan();
    return 1;
  }

  return 0;
}
