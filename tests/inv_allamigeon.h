
void swap(int *x , int *y){int t = *x; *x = *y; *y = t;}

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


int vumemcopy_abstract(const int n, const int siz){
  assert(n<=siz && 0 <= n && n <= siz-1);
  int l_src_null = randrange_i(0,siz-1,INCLUDE);
  int l_dst_null = randrange_i(0,siz-1,INCLUDE);


  int i = 0;
  while(TRUE){
    printf("li0: i s d\n");
    printf("li0: %d %d %d\n", i, l_src_null, l_dst_null);

    assert((i > l_src_null & l_dst_null == l_src_null)||
	   (i<=l_src_null && l_dst_null >= i));
    

    if(!(i<=n))break;

    i=i+1;

    if (i >= l_src_null){
      l_dst_null = l_src_null;
    }
    else{ //i<ls
      //ds >=i
      if (l_dst_null>=i){
	;
      }
      else{
	l_dst_null = i;
      }
    }
    
  }
  
  i = i - 1;
  if (n <= l_src_null){
    if (n < l_dst_null){printf("#0. n <= s , n <= ld\n");}
    else if (n == l_dst_null){printf("#1. n <= s, n == ld\n");}
    else{//n > len_dst_null:
      assert(FALSE);
    }
  }
  else{
    if(l_src_null == l_dst_null){printf("#2. n > ls, ls == ld\n");}
    else{assert(FALSE);}
  }
  
}

int vumemcopy(const int n, const int siz){
  /*
    strcpy
    The version using malloc and strlen doesn't work very well
    so just stick with this version
  */
  
  //const int siz = 31;
  assert (1 <= siz && 0 <= n && n <= siz-1);
  int src[siz]; int dst[siz];
  mk_rand_list(src, siz);
  mk_rand_list(dst, siz);
  
  int i = 0;
  for(; i < n ; ++i){
    dst[i] = src[i];
  }

  int ls = mylen(n,src,siz);
  int ld = mylen(n,dst,siz);

  printf("l_post: n s d\n");
  printf("l_post: %d %d %d\n", n, ls, ld);

  //inv
  assert(!(n <= ls) || ld >= n);
  assert(!(n > ls) || ld == ls);

  /* 
     DIG
     13: lambda d,n,s: d >= min(n,s) ***
     14: lambda d,n,s: s >= min(d,n) ***
  */

  if (n <= ls){
    if (n < ld){printf("#0. n <= s , n <= ld\n");}
    else if (n == ld){printf("#1. n <= s, n == ld\n");}
    else{//n > ld:
      assert(FALSE);
    }
  }
  else{
    if(ls == ld){printf("#2. n > ls, ls == ld\n");}
    else{assert(FALSE);}
  }
  
}


int strncopy(const int n, const int siz){
  //const int siz = 31
  assert (1 <= siz && 0 <= n && n <= siz-1);
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

  if (n <= ls){
    if (n < ld){printf("#0. n <= s , n <= ld\n");}
    else if (n == ld){printf("#1. n <= s, n == ld\n");}
    else{//n > ld:
      assert(FALSE);
    }
  }
  else{
    if(ls == ld){printf("#2. n > ls, ls == ld\n");}
    else{assert(FALSE);}
  }
  
}

/*Partial decr*/
void partial_decr0(int n){
  int i = 0;
  while(TRUE){
    printf("li0: i n \n");
    printf("li0: %d %d\n",i,n);

    if(!(i > n)) break;

    i = i - 1;
  }
  
  assert(i <= n); //inv
  printf("l_post: i n \n");
  printf("l_post: %d %d\n",i,n);

  /*
    DIG:
    0: lambda i: 0 >= i
    1: lambda i,n: n >= i
    2: lambda i,n: i >= min(n,0) *** If(n<=0,n<=i,0<=i), redundant, implied by 0,1


    sage: f1;f2; prove(f1==f2)
    And(i <= n, i<= 0)
    And(n >= i, 0 >= i, If(n <= 0, n <= i, 0 <= i))
    proved

   */
}


void partial_decr1(const int p, const int q){
  /*
    Proving this
    1) use ktp to prove p>=i & i>=min(p,q) is loop inv
    2) p>i & i>=min(p,q) & i<=q  =>  the DIG results ... 
   */

  int i = p;
  while(TRUE){
    printf("li0: i p q\n");
    printf("li0: %d %d %d\n",i,p,q);
    /*
      If(p<=q,p<=p,q<=p)
     */
    assert(i >= min(p,q));
    assert(i <= max(p,q));

    /*
      DIG:
      p>=i
      i >= min(p,q)
    */

    if (!(i>q)){break;}
    printf("l1a: i p q\n");
    printf("l1a: %d %d %d\n",i,p,q);
    assert(i >= min(p,q));
    assert(i <= max(p,q));
    /*
      DIG
      Nothing Useful
    */

    
    i = i - 1;
  }
  
  assert(i==min(p,q)); //inv
  printf("l_post: i p q\n");
  printf("l_post: %d %d %d\n",i,p,q);
  
  /*
    DIG
    1: lambda i,p: p >= i
    2: lambda i,q: q >= i
    4: lambda i,p,q: i >= min(p,q) ***

    sage: f1;f2; prove(f1 == f2)
    If(p <= q, i == p, i == q)
    And(If(p <= q, p <= i, q <= i), p >= i, q >= i)
    proved


  */
  
}

void partial_decr2(const int p, const int q, const int r){

  int i = p;
  while(TRUE){
    assert(i >= min(p,q));
    assert(i <= max(p,q));
    printf("li0: i p q r\n");
    printf("li0: %d %d %d %d\n",i,p,q,r);

    if (!(i > q)){break;}

    i = i - 1;
  }
  assert(i==min(p,q));
  printf("l2: i p q r\n");
  printf("l2: %d %d %d %d\n",i,p,q,r);


  while(TRUE){
    
    assert(i >= min(min(p,q),r));
    assert(i <= max(max(p,q),r));
    printf("li1: i p q r\n");
    printf("li1: %d %d %d %d\n",i,p,q,r);

    if (!(i > r)){break;}

    i = i - 1;
  }

  //inv
  assert(i==min(min(p,q),r));
  printf("l_post: i p q r\n");
  printf("l_post: %d %d %d %d\n",i,p,q,r);

  /*
    DIG
    0: lambda i,q: q >= i
    1: lambda i,p: p >= i
    2: lambda i,r: r >= i
    12: lambda i,p,q,r: i >= min(p,q,r) ***
    
  */
  
}

void partial_decr3(const int p, const int q, const int r, const int s){

  int i = p;
  while(TRUE){
    assert(i >= min(p,q));
    assert(i <= max(p,q));
    printf("li0: i p q r s\n");
    printf("li0: %d %d %d %d %d\n",i,p,q,r,s);

    if (!(i > q)){break;}
    i = i - 1;
  }
  assert(i==min(p,q));
  printf("l2: i p q r s\n");
  printf("l2: %d %d %d %d %d\n",i,p,q,r,s);


  while(TRUE){
    assert(i >= min(min(p,q),r));
    assert(i <= max(max(p,q),r));
    printf("li1: i p q r s\n");
    printf("li1: %d %d %d %d %d\n",i,p,q,r,s);

    if (!(i > r)){break;}
    i = i - 1;
  }

  assert(i==min(min(p,q),r));
  printf("l4: i p q r s\n");
  printf("l4: %d %d %d %d %d\n",i,p,q,r,s);


  while(TRUE){
    assert(i >= min(min(min(p,q),r),s));
    assert(i <= max(max(max(p,q),r),s));
    printf("li2: i p q r s\n");
    printf("li2: %d %d %d %d %d\n",i,p,q,r,s);

    if (!(i > s)){break;}
    i = i - 1;
  }

  //inv
  assert(i==min(min(min(p,q),r),s));
  printf("l_post: i p q r s\n");
  printf("l_post: %d %d %d %d %d\n",i,p,q,r,s);
  /*
    0: lambda i,s: s >= i
    1: lambda i,p: p >= i
    2: lambda i,q: q >= i
    32: lambda i,p,q,r,s: i >= min(p,q,r,s) ***
   */
}

void partial_decr4(const int p, const int q, const int r, const int s, int t){

  int i = p;
  while(TRUE){
    assert(i >= min(p,q));
    assert(i <= max(p,q));
    printf("li0: i p q r s t\n");
    printf("li0: %d %d %d %d %d %d\n",i,p,q,r,s,t);

    if (!(i > q)){break;}
    i = i - 1;
  }

  assert(i==min(p,q));
  printf("l2: i p q r s t\n");
  printf("l2: %d %d %d %d %d %d\n",i,p,q,r,s,t);

  while(TRUE){
    assert(i >= min(min(p,q),r));
    assert(i <= max(max(p,q),r));
    printf("li1: i p q r s t\n");
    printf("li1: %d %d %d %d %d %d\n",i,p,q,r,s,t);

    if (!(i > r)){break;}
    i = i - 1;
  }

  assert(i==min(min(p,q),r));
  printf("l4: i p q r s t\n");
  printf("l4: %d %d %d %d %d %d\n",i,p,q,r,s,t);

  while(TRUE){
    assert(i >= min(min(min(p,q),r),s));
    assert(i <= max(max(max(p,q),r),s));
    printf("li2: i p q r s t\n");
    printf("li2: %d %d %d %d %d %d\n",i,p,q,r,s,t);

    if (!(i > s)){break;}
    i = i - 1;
  }

  assert(i == min(min(min(p,q),r),s));
  printf("l6: i p q r s t\n");
  printf("l6: %d %d %d %d %d %d\n",i,p,q,r,s,t);

  while(TRUE){
    assert(i >= min(min(min(min(p,q),r),s),t));
    assert(i <= max(max(max(max(p,q),r),s),t));

    printf("li3: i p q r s t\n");
    printf("li3: %d %d %d %d %d %d\n",i,p,q,r,s,t);

    if (!(i > t)){break;}
    i = i - 1;
  }

  //inv
  assert(i==min(min(min(min(p,q),r),s),t));
  printf("l_post: i p q r s t\n");
  printf("l_post: %d %d %d %d %d %d\n",i,p,q,r,s,t);
  
}

void partial_decr5(const int p, const int q, const int r, const int s, const int t, const int u){

  int i = p;
  while(TRUE){
    assert(i >= min(p,q));
    assert(i <= max(p,q));
    printf("li0: i p q r s t u\n");
    printf("li0: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

    if (!(i > q)){break;}
    i = i - 1;
  }
  assert(i == min(p,q));
  printf("l2: i p q r s t u\n");
  printf("l2: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);
  
  while(TRUE){
    assert(i >= min(min(p,q),r));
    assert(i <= max(max(p,q),r));
    printf("li1: i p q r s t u\n");
    printf("li1: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

    if (!(i > r)){break;}
    i = i - 1;
  }

  assert(i==min(min(p,q),r));
  printf("l4: i p q r s t u\n");
  printf("l4: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

  while(TRUE){
    assert(i >= min(min(min(p,q),r),s));
    assert(i <= max(max(max(p,q),r),s));
    printf("li2: i p q r s t u\n");
    printf("li2: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

    if (!(i > s)){break;}
    i = i - 1;
  }
  assert(i == min(min(min(p,q),r),s));
  printf("l6: i p q r s t u\n");
  printf("l6: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

  while(TRUE){
    assert(i >= min(min(min(min(p,q),r),s),t));
    assert(i <= max(max(max(max(p,q),r),s),t));
    printf("li3: i p q r s t u\n");
    printf("li3: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

    if (!(i > t)){break;}
    i = i - 1;
  }
  assert(i == min(min(min(min(p,q),r),s),t));
  printf("l8: i p q r s t u\n");
  printf("l8: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);


  while(TRUE){
    assert(i >= min(min(min(min(min(p,q),r),s),t),u));
    assert(i <= max(max(max(max(max(p,q),r),s),t),u));
    printf("li4: i p q r s t u\n");
    printf("li4: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

    if (!(i > u)){break;}
    i = i - 1;
  }

  //inv
  assert(i==min(min(min(min(min(p,q),r),s),t),u));
  printf("l_post: i p q r s t u\n");
  printf("l_post: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);
  
}

/* Partial Incr*/
void partial_incr0(int n){
  int i = 0;
  while(TRUE){
    printf("li0: i n \n");
    printf("li0: %d %d\n",i,n);
    if(!(i < n)) break; 
    i = i + 1;
  }

  assert(i >= n); //inv
  assert(i >= 0); //inv

  printf("l_post: i n \n");
  printf("l_post: %d %d\n",i,n);

  /* 
     DIG (stronger than inv: i >= n)
     0: lambda i: i >= 0
     1: lambda i,n: i >= n
     2: lambda i,n: max(n,0) >= i *** If(n>=0,n>=i,0>=i) , redudant, implied by 0,1
     
     
     sage: f1;f2; prove(f1==f2)
     And(i >= n, i>=0)
     And(i >= n, i >= 0, If(n <= 0, n <= i, 0 <= i))
     proved

     
  */

}



void partial_incr1(const int p, const int q){

  int i = p;
  while(TRUE){
    assert(i >= min(p,q));
    assert(i <= max(p,q));
    printf("li0: i p q\n");
    printf("li0: %d %d %d\n",i,p,q);

    if (!(i < q)){break;}

    i = i + 1;
  }
  //inv
  assert(i==max(p,q));
  printf("l_post: i p q\n");
  printf("l_post: %d %d %d\n",i,p,q);
  /* 
     DIG
     0: lambda i,p: i >= p
     1: lambda i,q: i >= q
     12: lambda i,p,q: max(p,q) >= i ***
  */

  
}





void partial_incr2(const int p, const int q, const int r){

  int i = p;
  while(TRUE){
    assert(i >= min(p,q));
    assert(i <= max(p,q));
    printf("li0: i p q r\n");
    printf("li0: %d %d %d %d\n",i,p,q,r);

    if (!(i < q)){break;}
    i = i + 1;
  }
  assert(i==max(p,q));
  printf("l2: i p q r\n");
  printf("l2: %d %d %d %d\n",i,p,q,r);


  while(TRUE){
    assert(i >= min(min(p,q),r));
    assert(i <= max(max(p,q),r));
    printf("li1: i p q r\n");
    printf("li1: %d %d %d %d\n",i,p,q,r);

    if (!(i < r)){break;}
    i = i + 1;
  }
  //inv
  assert(i==max(max(p,q),r));
  printf("l_post: i p q r\n");
  printf("l_post: %d %d %d %d\n",i,p,q,r);
  /*
    DIG
    0: lambda i,p: i >= p
    1: lambda i,q: i >= q
    5: lambda i,r: i >= r
    14: lambda i,p,q,r: max(p,q,r) >= i ***
  */

  
}




void partial_incr3(const int p, const int q, const int r, const int s){

  int i = p;
  while(TRUE){
    assert(i >= min(p,q));
    assert(i <= max(p,q));
    printf("li0: i p q r s\n");
    printf("li0: %d %d %d %d %d\n",i,p,q,r,s);
    if (!(i < q)){break;}

    i = i + 1;
  }

  assert(i==max(p,q));
  printf("l2: i p q r s\n");
  printf("l2: %d %d %d %d %d\n",i,p,q,r,s);

  while(TRUE){
    assert(i >= min(min(p,q),r));
    assert(i <= max(max(p,q),r));
    printf("li1: i p q r s\n");
    printf("li1: %d %d %d %d %d\n",i,p,q,r,s);

    if (!(i < r)){break;}
    i = i + 1;

  }
  assert(i==max(max(p,q),r));
  printf("l4: i p q r s\n");
  printf("l4: %d %d %d %d %d\n",i,p,q,r,s);

  while(TRUE){
    assert(i >= min(min(min(p,q),r),s));
    assert(i <= max(max(max(p,q),r),s));
    printf("li2: i p q r s\n");
    printf("li2: %d %d %d %d %d\n",i,p,q,r,s);

    if (!(i < s)){break;}
    i = i + 1;
  }

  //inv
  assert(i==max(max(max(p,q),r),s));
  printf("l_post: i p q r s\n");
  printf("l_post: %d %d %d %d %d\n",i,p,q,r,s);
  
}




void partial_incr4(const int p, const int q, const int r, const int s, int t){

  int i = p;
  while(TRUE){

    assert(i >= min(p,q));
    assert(i <= max(p,q));
    printf("li0: i p q r s t\n");
    printf("li0: %d %d %d %d %d %d\n",i,p,q,r,s,t);

    if (!(i < q)){break;}
    i = i + 1;
  }

  assert(i==max(p,q));
  printf("l2: i p q r s t\n");
  printf("l2: %d %d %d %d %d %d\n",i,p,q,r,s,t);


  while(TRUE){
    assert(i >= min(min(p,q),r));
    assert(i <= max(max(p,q),r));
    printf("li1: i p q r s t\n");
    printf("li1: %d %d %d %d %d %d\n",i,p,q,r,s,t);
    
    if (!(i < r)){break;}
    i = i + 1;
  }

  assert(i==max(max(p,q),r));
  printf("l4: i p q r s t\n");
  printf("l4: %d %d %d %d %d %d\n",i,p,q,r,s,t);

  while(TRUE){
    assert(i >= min(min(min(p,q),r),s));
    assert(i <= max(max(max(p,q),r),s));
    printf("li2: i p q r s t\n");
    printf("li2: %d %d %d %d %d %d\n",i,p,q,r,s,t);

    if (!(i < s)){break;}
    i = i + 1;
  }

  assert(i == max(max(max(p,q),r),s));
  printf("l6: i p q r s t\n");
  printf("l6: %d %d %d %d %d %d\n",i,p,q,r,s,t);

  while(TRUE){
    assert(i >= min(min(min(min(p,q),r),s),t));
    assert(i <= max(max(max(max(p,q),r),s),t));

    printf("li3: i p q r s t\n");
    printf("li3: %d %d %d %d %d %d\n",i,p,q,r,s,t);

    if (!(i < t)){break;}
    i = i + 1;
  }

  //inv
  assert(i==max(max(max(max(p,q),r),s),t));
  printf("l_post: i p q r s t\n");
  printf("l_post: %d %d %d %d %d %d\n",i,p,q,r,s,t);
  
}


void partial_incr5(const int p, const int q, const int r, const int s, const int t, const int u){

  int i = p;
  while(TRUE){
    assert(i >= min(p,q));
    assert(i <= max(p,q));
    printf("li0: i p q r s t u\n");
    printf("li0: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

    if (!(i < q)){break;}
    i = i + 1;
  }

  assert(i == max(p,q));
  printf("l2: i p q r s t u\n");
  printf("l2: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);


  while(TRUE){
    assert(i >= min(min(p,q),r));
    assert(i <= max(max(p,q),r));
    printf("li1: i p q r s t u\n");
    printf("li1: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

    if (!(i < r)){break;}
    i = i + 1;
  }
  assert(i==max(max(p,q),r));
  printf("l4: i p q r s t u\n");
  printf("l4: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

  while(TRUE){
    assert(i >= min(min(min(p,q),r),s));
    assert(i <= max(max(max(p,q),r),s));
    printf("li2: i p q r s t u\n");
    printf("li2: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

    if (!(i < s)){break;}
    i = i + 1;
  }

  assert(i == max(max(max(p,q),r),s));
  printf("l6: i p q r s t u\n");
  printf("l6: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

  while(TRUE){
    assert(i >= min(min(min(min(p,q),r),s),t));
    assert(i <= max(max(max(max(p,q),r),s),t));
    printf("li3: i p q r s t u\n");
    printf("li3: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

    if (!(i < t)){break;}
    i = i + 1;
  }

  assert(i == max(max(max(max(p,q),r),s),t));
  printf("l8: i p q r s t u\n");
  printf("l8: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

  while(TRUE){

    assert(i >= min(min(min(min(min(p,q),r),s),t),u));
    assert(i <= max(max(max(max(max(p,q),r),s),t),u));
    printf("li4: i p q r s t u\n");
    printf("li4: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

    if (!(i < u)){break;}
    i = i + 1;
  }

  //inv
  assert(i==max(max(max(max(max(p,q),r),s),t),u));
  printf("l_post: i p q r s t u\n");
  printf("l_post: %d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);
  
}

void vusearch3(int t0, int t1, int t2, int x){
  int r = 0;
  if(t0 == x) r = 1;
  if(t1 == x) r = 1;
  if(t2 == x) r = 1;
  printf("l_post: t0 t1 t2 x r\n");
  printf("l_post: %d %d %d %d %d\n",t0,t1,t2,x,r);
}

void oddeven2(const int t0, const int t1){
  /*Not in paper but much simpler than oddeven3+ , good place to start*/
  int x0 = t0;
  int x1 = t1;
  if (x0 > x1){swap(&x0,&x1);}
  int arr[2] = {x0,x1}; assert(myissorted(arr,0,2));
  printf("l_post: x0 x1 t0 t1\n");
  printf("l_post: %d %d %d %d\n",x0,x1,t0,t1);
}


void oddeven3(int t0, int t1, int t2){
  int x0 = t0;
  int x1 = t1;
  int x2 = t2; 

  if (x0 > x1){swap(&x0,&x1);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x0 > x1){swap(&x0,&x1);}
  if (x1 > x2){swap(&x1,&x2);}
  
  int arr[3] = {x0,x1,x2}; assert(myissorted(arr,0,3));

  printf("l_post: x0 x1 x2 t0 t1 t2\n");
  printf("l_post: %d %d %d %d %d %d\n",x0,x1,x2,t0,t1,t2);
	 
  
}


void oddeven4(int t0, int t1, int t2, int t3){
  int x0 = t0;
  int x1 = t1;
  int x2 = t2;
  int x3 = t3;

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x1 > x2){swap(&x1,&x2);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x1 > x2){swap(&x1,&x2);}
  
  int arr[4] = {x0,x1,x2,x3}; assert(myissorted(arr,0,4));

  printf("l_post: x0 x1 x2 x3 t0 t1 t2 t3\n");
  printf("l_post: %d %d %d %d %d %d %d %d\n",x0,x1,x2,x3,t0,t1,t2,t3);
	 
  
}

void oddeven5(int t0, int t1, int t2, int t3, int t4){
  int x0 = t0;
  int x1 = t1;
  int x2 = t2;
  int x3 = t3;
  int x4 = t4;
  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}

  int arr[5] = {x0,x1,x2,x3,x4}; assert(myissorted(arr,0,5));
  printf("l_post: x0 x1 x2 x3 x4 t0 t1 t2 t3 t4\n");
  printf("l_post: %d %d %d %d %d %d %d %d %d %d\n",
	 x0,x1,x2,x3,x4,t0,t1,t2,t3,t4);
}

void oddeven6(int t0, int t1, int t2, int t3, int t4, int t5){

  int x0 = t0;
  int x1 = t1;
  int x2 = t2;
  int x3 = t3;
  int x4 = t4;
  int x5 = t5;

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}

  int arr[6] = {x0,x1,x2,x3,x4,x5}; assert(myissorted(arr,0,6));
  printf("l_post: x0 x1 x2 x3 x4 x5 t0 t1 t2 t3 t4 t5\n");
  printf("l_post: %d %d %d %d %d %d %d %d %d %d %d %d\n",
	 x0,x1,x2,x3,x4,x5,t0,t1,t2,t3,t4,t5);
	 
  
}


void oddeven7(int t0, int t1, int t2, int t3, int t4, int t5, int t6){

  int x0 = t0;
  int x1 = t1;
  int x2 = t2;
  int x3 = t3;
  int x4 = t4;
  int x5 = t5;
  int x6 = t6;

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}
  if (x5 > x6){swap(&x5,&x6);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}
  if (x5 > x6){swap(&x5,&x6);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}
  if (x5 > x6){swap(&x5,&x6);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}
  if (x5 > x6){swap(&x5,&x6);}

  int arr[7] = {x0,x1,x2,x3,x4,x5,x6}; assert(myissorted(arr,0,7));
  printf("l_post: x0 x1 x2 x3 x4 x5 x6 t0 t1 t2 t3 t4 t5 t6\n");
  printf("l_post: %d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
	 x0,x1,x2,x3,x4,x5,x6,t0,t1,t2,t3,t4,t5,t6);
}


void oddeven8(int t0, int t1, int t2, int t3, int t4, 
	      int t5, int t6, int t7){

  int x0 = t0;
  int x1 = t1;
  int x2 = t2;
  int x3 = t3;
  int x4 = t4;
  int x5 = t5;
  int x6 = t6;
  int x7 = t7;

  x0 = t0;
  x1 = t1;
  x2 = t2;
  x3 = t3;
  x4 = t4;
  x5 = t5;
  x6 = t6;
  x7 = t7;

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x6 > x7){swap(&x6,&x7);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}
  if (x5 > x6){swap(&x5,&x6);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x6 > x7){swap(&x6,&x7);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}
  if (x5 > x6){swap(&x5,&x6);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x6 > x7){swap(&x6,&x7);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}
  if (x5 > x6){swap(&x5,&x6);}

  if (x0 > x1){swap(&x0,&x1);}
  if (x2 > x3){swap(&x2,&x3);}
  if (x4 > x5){swap(&x4,&x5);}
  if (x6 > x7){swap(&x6,&x7);}
  if (x1 > x2){swap(&x1,&x2);}
  if (x3 > x4){swap(&x3,&x4);}
  if (x5 > x6){swap(&x5,&x6);}

  int arr[8] = {x0,x1,x2,x3,x4,x5,x6,x7}; assert(myissorted(arr,0,8));
  printf("l_post: x0 x1 x2 x3 x4 x5 x6 x7 t0 t1 t2 t3 t4 t5 t6 t7\n");
  printf("l_post: %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
	 x0,x1,x2,x3,x4,x5,x6,x7,t0,t1,t2,t3,t4,t5,t6,t7);
};


/* void oddeven9(int t0, int t1, int t2, int t3, int t4, int t5, int t6, int t7, int t8){ */

/*   int x0 = t0; */
/*   int x1 = t1; */
/*   int x2 = t2; */
/*   int x3 = t3; */
/*   int x4 = t4; */
/*   int x5 = t5; */
/*   int x6 = t6; */
/*   int x7 = t7; */
/*   int x8 = t8; */

/*   x0 = t0; */
/*   x1 = t1; */
/*   x2 = t2; */
/*   x3 = t3; */
/*   x4 = t4; */
/*   x5 = t5; */
/*   x6 = t6; */
/*   x7 = t7; */
/*   x8 = t8; */

/*   if (x0 > x1){swap(&x0,&x1);} */
/*   if (x2 > x3){swap(&x2,&x3);} */
/*   if (x4 > x5){swap(&x4,&x5);} */
/*   if (x6 > x7){swap(&x6,&x7);} */
/*   if (x1 > x2){swap(&x1,&x2);} */
/*   if (x3 > x4){swap(&x3,&x4);} */
/*   if (x5 > x6){swap(&x5,&x6);} */
/*   if (x0 > x1){swap(&x0,&x1);} */
/*   if (x2 > x3){swap(&x2,&x3);} */
/*   if (x4 > x5){swap(&x4,&x5);} */
/*   if (x6 > x7){swap(&x6,&x7);} */
/*   if (x1 > x2){swap(&x1,&x2);} */
/*   if (x3 > x4){swap(&x3,&x4);} */
/*   if (x5 > x6){swap(&x5,&x6);} */
/*   if (x0 > x1){swap(&x0,&x1);} */
/*   if (x2 > x3){swap(&x2,&x3);} */
/*   if (x4 > x5){swap(&x4,&x5);} */
/*   if (x6 > x7){swap(&x6,&x7);} */
/*   if (x1 > x2){swap(&x1,&x2);} */
/*   if (x3 > x4){swap(&x3,&x4);} */
/*   if (x5 > x6){swap(&x5,&x6);} */
/*   if (x0 > x1){swap(&x0,&x1);} */
/*   if (x2 > x3){swap(&x2,&x3);} */
/*   if (x4 > x5){swap(&x4,&x5);} */
/*   if (x6 > x7){swap(&x6,&x7);} */
/*   if (x1 > x2){swap(&x1,&x2);} */
/*   if (x3 > x4){swap(&x3,&x4);} */
/*   if (x5 > x6){swap(&x5,&x6);} */

/*   int arr[8] = {x0,x1,x2,x3,x4}; assert(myissorted(arr,0,8)); */
/*   printf("l_post: x0 x1 x2 x3 x4 x5 x6 x7\n"); */
/*   printf("l_post: %d %d %d %d %d %d %d %d\n",x0,x1,x2,x3,x4,x5,x6,x7); */
/* }; */


//End Allaminioni




/*Other programs*/ 


void max_ex1(int x){
  int y = 0;
  if (x>=10){
    y = x;
  }
  else{
    y = 10;
  }
  printf("x y\n");
  printf("l_post: %d %d\n",x,y);
  /*
    2,5,6 together imply the strongest inv
    If(x>=10,x=y,10=y) .. nice

    0. x >= y - 10: False
    1. x >= 0: False
    2. y - 10 >= 0: True
    3. y - 19 <= 0: False
    4. x - 19 <= 0: False
    5. y >= x: True
    6. If(x - 10 >= 0, x - 10 >= y - 10, y - 10 <= 0): True
  */

}


void min_ex1(int x){
  int y = 0;
  if (x<=10){
    y = x;
  }
  else{
    y = 10;
  }
  printf("x y\n");
  printf("l_post: %d %d\n",x,y);
  /*
  */

}


void max_ex1a(int x){
  int y = 0;
  if (x>=10){
    y = randrange_i(x-3,x,INCLUDE);  // y <= x
  }
  else{
    y = randrange_i(10-3,10,INCLUDE); // y <= 10
  }
  printf("x y\n");
  printf("l_post: %d %d\n",x,y);
  /*
    0. x >= -100: False
    1. y - 5 >= 0: False
    2. y - 95 <= 0: False
    3. y >= x - 5: False
    4. x - 100 <= 0: False
    5. x >= y - 105: False
    6. If(x - 10 >= 0, x - 10 >= y - 5, y - 5 <= 0): False #spurious,
    this implies the desired invariant If(x>=10,x>=y,10>=y)
  */

}

void t1(int x){
  /*ex1 in ICSE14*/
  int y, b;
  if (x >= 0){
    y=x+1;
  }
  else{
    y=x-1;
  }

  if (y >= 11){
    b = 1;
  }
  else{
    b = 0;
  }

  printf("l_post: x y b\n");
  printf("l_post: %d %d %d\n",x,y,b);

  /*
    If(y >= 0, y-x >= 1, -1 >= x)
  */

  /*
    Interproc

    proc ex1(x:int) returns (b:int) 
    var y:int;
    begin
    if (x>=0) then
    y = x + 1;
    else
    y = x - 1;
    endif;

    if (y>10) then
    b = 1;
    else
    y = 0;
    endif;
    end

var
x:int, b:int;
begin
  b = ex1(x);
end
   */
}


  
/*  13 Programs from Xavier Allemigeon that has documented max-plus invariants 

    Todo:

    partial_dec inside loop

    try obtain the inv
    while(cond){
    inv
    i > min() //strictly
    }

    instead of 

    while(TRUE){
    inv i >= min()
    if(!cond) break

    }
*/








/* From the thesis "Disjunctive Invariants for Modular Static Analysis "by 
   Corneliu Popee

   See page 7 more the complete example -- quite interesting if I can get all these invs

   Lots more example from this guy's thesis -- very interesting ones too
*/

int f91(int x) {
  int t = 0 ;
  if (x<=100){
    t= f91(f91(x+11));
  }
  else{
    t= x-10;
  }
  printf("l_post: x t\n");
  printf("l_post: %d %d\n",x,t);
  assert((x >= 101 && t==x-10) || (x<=100 && t == 91) );

  /*
    DIG 
    0: lambda t: t >= 91
    2: lambda t,x: t + 10 >= x
    4: lambda t,x: max(x - 101,0) >= t - 91 ***

    x >= 101 -> x == t + 10
    x < 101 -> 91 == t

   */
  return t;
}


int f91_nr(const int x) {
  /*non recursive version http://proval.lri.fr/gallery/mccarthy.en.html*/
  int c = 1;
  int t = x;

  while(TRUE){
    printf("li0: c x t\n");
    printf("li0: %d %d %d\n",c, x,t);

    if(!(c>0)) break;

    if(t > 100){
      t = t - 10;
      c = c - 1;
      }
    else{
      t = t + 11;
      c = c + 1;
    }
  }
  printf("l_post: c x t\n");
  printf("l_post: %d %d %d\n",c, x,t);
  assert((x >= 101 && t==x-10) || (x<=100 && t == 91) );
  return t;
 }


void fig1_1(int x){
  int y; int b;
  if (x > 0) {
    y = x;
  }
  else { 
    y = -x;
  }
  
  if (y>10){
    b = 1;
  }
  else{
    b = 0;
  }


  printf("l_post: x y b\n");
  printf("l_post: %d %d %d\n",x,y,b);

  //inv
  
  int c1 = (b == 1 && y > 10 && y == x) ;
  int c2 = (b == 1 && y > 10 && y == -x) ;
  int c3 = (b == 0 && y <= 10 && x > 0 && y == x) ;
  int c4 = (b == 0 && y <= 10 && x <= 0 && y == -x) ;
  assert(c1 || c2 || c3 || c4);

 

  assert ((x > 0 && y == x) || (x <= 0 && y == -x));

  //b => (x < -10 or 10 < x)
  assert (b==0 || (x < 10 || 10 < x));

  //I think this is also an inv
  //b = 0 =>  !(x < -10 || 10 < x)
  assert(b == 1 || (x >= -10 && 10 >= x));

  //in other words,  b *iff* (x <-10 || 10 < x)

  /*
    0. x + 100 >= 0: False
    1. x + 200 >= y: False
    2. x + 101 >= b: False
    3. y >= 0: True
    4. y >= b: True
    5. b >= 0: True
    6. y >= x: True
    7. b <= 1: True
    8. b + 99 >= y: False
    9. y <= 100: False
    10. x <= 100: False
    11. b + 99 >= x: False
    12. If(y <= 11, b + 10 >= y, b + 10 >= 11): True
    13. If(x <= 11, b + 10 >= x, b + 10 >= 11): True
   */
}




/*Not fully tested / used*/


int fig2_6_mn(int x){
  if (x > 0){
    x = fig2_6_mn(x-1);
  }
  
  return x;
}

void fig2_6_mn_caller(int x){
  int t = fig2_6_mn(x);
  //inv 

  printf("l_post: x t\n");
  printf("l_post: %d %d\n",x,t);
  assert ((x <= 0 && t==x) || (x > 0  && t==0));  
}

// quicksort

void swap_arr(float a[], int i, int j) {
  float temp = a[i]; 
  a[i] = a[j]; 
  a[j] = temp;
}


int changeN(float a[], int n, int i, int h, float v) { 
  if (i <= h){
    if (a[i] < v){ 
      swap_arr(a,n+1,i); 
      return changeN(a,n+1,i+1,h,v);
    } 
    else { 
      return changeN(a,n,i+1,h,v);
    } 
  } 
  else { 
    return n ;
  } 
}

int mypartition(float a[], int l, int h){
  int v = a[l]; 
  int n = changeN(a,l,l+1,h,v); 
  swap_arr(a,l,n);
  return n ;
}


/* MY EXAMPLES */

void maxfun(int a, int b, int c){
  int t = a ;
  if (b > t){
    t = b;
  }
  if (c > t){
    t = c;
  }
  printf("a b c t\n");
  printf("l_post: %d %d %d %d\n",a,b,c,t);
}


void myminmax(const int a, const int b){
  //suppose to give max(x,y) >= max(a,b)
  //similar to the mymemcpy but easier for me to debug

  int x = a;
  int y = b;
  
  int i = 0 ;
  printf("a b x y\n");
  while(i < 10){
    printf("l_post: %d %d %d %d\n",a,b,x,y);
    assert(max(x,y) >= max(a,b));

    if (x == max(x,y)){
      x = x + randrange_i(0,100,1);
      y = y + randrange_i(-100,100,1);
    }
    else{
      y = y + randrange_i(0,100,1);
      x = x + randrange_i(-100,100,1);
    }
    i++;
  }


}




/*old stuff from inv_tropical.h

  void mymemcpy(int n, const int s1, const int s2){
  char *src = malloc(s1);
  char *dst = malloc(s2);

  assert((n <= s2) && (n <= s1));
  
  assert((1 <= s2) && (1 <= s1));

  int i = 0;
  while(i < n){
  dst[i] = src[i];
  i = i + 1;
  }
  printf("n s d\n");
  printf("l_post: %d %d %d\n",n,(unsigned)strlen(src),(unsigned)strlen(dst));
  }




  void partial_decr0(int n){

  int i = 0;
  while(i > n){
  i = i - 1;
  }
  //inv

  printf("i n\n");
  printf("l_post: %d %d\n",i,n);

  }


  void partial_incr0(int n){

  int i = 0;
  while(i <= n){
  i = i + 1;
  }
  //inv

  printf("i n\n");
  printf("l_post: %d %d\n",i,n);

  }


  void partial_decr1(const int p, const int q){

  int i = p;
  while(i > q){
  i = i - 1;
  }
  //inv
  assert(i==min(p,q));
  printf("i p q\n");
  printf("l_post: %d %d %d\n",i,p,q);

  }


  void partial_incr1(const int p, const int q){

  int i = p;
  while(i < q){
  i = i + 1;
  }
  //inv
  assert(i==max(p,q));
  printf("i p q\n");
  printf("l_post: %d %d %d\n",i,p,q);

  }



  void partial_decr2(const int p, const int q, const int r){

  int i = p;
  while(i > q){
  i = i - 1;
  }

  while(i > r){
  i = i - 1;
  }

  //inv
  assert(i==min(min(p,q),r));
  printf("i p q r\n");
  printf("l_post: %d %d %d %d\n",i,p,q,r);

  }


  void partial_incr2(const int p, const int q, const int r){

  int i = p;
  while(i < q){
  i = i + 1;
  }

  while(i < r){
  i = i + 1;
  }
  //inv
  assert(i==max(max(p,q),r));
  printf("i p q r\n");
  printf("%d %d %d %d\n",i,p,q,r);

  }




  void partial_decr3(const int p, const int q, const int r, const int s){

  int i = p;
  while(i > q){
  i = i - 1;
  }

  while(i > r){
  i = i - 1;
  }

  while(i > s){
  i = i - 1;
  }

  //inv
  assert(i==min(min(min(p,q),r),s));
  printf("i p q s\n");
  printf("%d %d %d %d %d\n",i,p,q,r,s);

  }


  void partial_incr3(const int p, const int q, const int r, const int s){

  int i = p;
  while(i < q){
  i = i + 1;
  }

  while(i < r){
  i = i + 1;
  }

  while(i < s){
  i = i + 1;
  }

  //inv
  assert(i==max(max(max(p,q),r),s));
  printf("i p q s\n");
  printf("%d %d %d %d %d\n",i,p,q,r,s);

  }


  void partial_decr4(const int p, const int q, const int r, const int s, int t){

  int i = p;
  while(i > q){
  i = i - 1;
  }

  while(i > r){
  i = i - 1;
  }

  while(i > s){
  i = i - 1;
  }

  while(i > t){
  i = i - 1;
  }


  //inv
  assert(i==min(min(min(min(p,q),r),s),t));
  printf("i p q r s t\n");
  printf("%d %d %d %d %d %d\n",i,p,q,r,s,t);

  }


  void partial_incr4(const int p, const int q, const int r, const int s, int t){

  int i = p;
  while(i < q){
  i = i + 1;
  }

  while(i < r){
  i = i + 1;
  }

  while(i < s){
  i = i + 1;
  }

  while(i < t){
  i = i + 1;
  }

  //inv
  assert(i==max(max(max(max(p,q),r),s),t));
  printf("i p q r s t\n");
  printf("%d %d %d %d %d %d\n",i,p,q,r,s,t);

  }

  void partial_decr5(const int p, const int q, const int r, const int s, const int t, const int u){

  int i = p;
  while(i > q){
  i = i - 1;
  }

  while(i > r){
  i = i - 1;
  }

  while(i > s){
  i = i - 1;
  }

  while(i > t){
  i = i - 1;
  }

  while(i > t){
  i = i - 1;
  }

  while(i > u){
  i = i - 1;
  }


  //inv
  assert(i==min(min(min(min(min(p,q),r),s),t),u));
  printf("i p q r s t u\n");
  printf("%d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

  }


  void partial_incr5(const int p, const int q, const int r, const int s, const int t, const int u){

  int i = p;
  while(i < q){
  i = i + 1;
  }

  while(i < r){
  i = i + 1;
  }

  while(i < s){
  i = i + 1;
  }

  while(i < t){
  i = i + 1;
  }

  while(i < u){
  i = i + 1;
  }

  //inv
  assert(i==max(max(max(max(max(p,q),r),s),t),u));
  printf("i p q r s t u\n");
  printf("%d %d %d %d %d %d %d\n",i,p,q,r,s,t,u);

  }



  void oddeven4(int t0, int t1, int t2, int t3){

  int x0 = t0;
  int x1 = t1;
  int x2 = t2;
  int x3 = t3;

  int u;
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }

  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }

  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }

  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }

  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }

  assert (x0 <= x1 && x1 <= x2 && x2 <= x3);
  printf("x0 x1 x2 x3 t0 t1 t2 t3\n");
  printf("%d %d %d %d %d %d %d %d\n",x0,x1,x2,x3,t0,t1,t2,t3);
  }


  void oddeven5(int t0, int t1, int t2, int t3, int t4){
 
  int x0 = t0;
  int x1 = t1;
  int x2 = t2;
  int x3 = t3;
  int x4 = t4;

  int u;
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }

  assert (x0 <= x1 && x1 <= x2 && x2 <= x3 && x3 <= x4);

  printf("x0 x1 x2 x3 x4\n");
  printf("%d %d %d %d %d\n",x0,x1,x2,x3,x4);

  }

  void oddeven6(int t0, int t1, int t2, int t3, int t4, int t5){

  int x0 = t0;
  int x1 = t1;
  int x2 = t2;
  int x3 = t3;
  int x4 = t4;
  int x5 = t5;
  int u;
 
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }

  assert (x0 <= x1 && x1 <= x2 && x2 <= x3 && x3 <= x4 && x4 <= x5);

  printf("x0 x1 x2 x3 x4 x5 t0 t1 t2 t3 t4 t5\n");
  printf("%d %d %d %d %d %d %d %d %d %d %d %d\n",x0,x1,x2,x3,x4,x5,t0,t1,t2,t3,t4,t5);
  }

  void oddeven7(int t0, int t1, int t2, int t3, int t4, int t5, int t6){
  
  int x0 = t0;
  int x1 = t1;
  int x2 = t2;
  int x3 = t3;
  int x4 = t4;
  int x5 = t5;
  int x6 = t6;
  int u;
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x5 > x6){
  u = x5;
  x5 = x6;
  x6 = u;
  }
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x5 > x6){
  u = x5;
  x5 = x6;
  x6 = u;
  }
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x5 > x6){
  u = x5;
  x5 = x6;
  x6 = u;
  }
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x5 > x6){
  u = x5;
  x5 = x6;
  x6 = u;
  }

  assert (x0 <= x1 && x1 <= x2 && x2 <= x3 && x3 <= x4 && x4 <= x5 && x5 <= x6);

  printf("x0 x1 x2 x3 x4 x5 x6\n");
  printf("%d %d %d %d %d %d %d\n",x0,x1,x2,x3,x4,x5,x6);
  }

  void oddeven8(int t0, int t1, int t2, int t3, int t4, int t5, int t6, int t7){
  
  int x0 = t0;
  int x1 = t1;
  int x2 = t2;
  int x3 = t3;
  int x4 = t4;
  int x5 = t5;
  int x6 = t6;
  int x7 = t7;
  int u;
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x6 > x7){
  u = x6;
  x6 = x7;
  x7 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x5 > x6){
  u = x5;
  x5 = x6;
  x6 = u;
  }
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x6 > x7){
  u = x6;
  x6 = x7;
  x7 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x5 > x6){
  u = x5;
  x5 = x6;
  x6 = u;
  }
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x6 > x7){
  u = x6;
  x6 = x7;
  x7 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x5 > x6){
  u = x5;
  x5 = x6;
  x6 = u;
  }
  if (x0 > x1){
  u = x0;
  x0 = x1;
  x1 = u;
  }
  if (x2 > x3){
  u = x2;
  x2 = x3;
  x3 = u;
  }
  if (x4 > x5){
  u = x4;
  x4 = x5;
  x5 = u;
  }
  if (x6 > x7){
  u = x6;
  x6 = x7;
  x7 = u;
  }
  if (x1 > x2){
  u = x1;
  x1 = x2;
  x2 = u;
  }
  if (x3 > x4){
  u = x3;
  x3 = x4;
  x4 = u;
  }
  if (x5 > x6){
  u = x5;
  x5 = x6;
  x6 = u;
  }

  assert (x0 <= x1 && x1 <= x2 && x2 <= x3 && 
  x3 <= x4 && x4 <= x5 && x5 <= x6 && x6 <= x7);

  printf("x0 x1 x2 x3 x4 x5 x6 x7\n");
  printf("%d %d %d %d %d %d %d\n",x0,x1,x2,x3,x4,x5,x6,x7);
  }






  /*
  Examples from the paper InvGen: An Effcient Invariant Generator by Ashutosh Gupta and Andrey Rybalchenko
  
*/

void fig2a(int n){
  int x = 0;

  while(1){
    printf("l_post: x n\n");
    printf("l_post: %d %d\n",x,n);
    if(!(x<n)){
      break;
    }
    x++;
  }
}



/*
  Examples from the paper Extending Dynamic Constraint Detection with Disjunctive
  Constraints by Nadya Kuzmina, John Paul, Ruben Gamboa, and James Caldwell


  void calculator_numberpressed(int number){
  int displayValue = 100;
  if (number){
  displayValue = number ;
  }
  else{
  displayValue = displayValue * 10  + number ;
  }
  }


  void calculator_equals(int choice){
  const int result = 0;
  if (choice == 1){
  result = result + 10;
  }
  else{
  result = 10 - result;
  }
  }


  /* From the thesis Disjunctive Invariants for Modular Static Analysis by 
  Corneliu Popee

  See page 7 more the complete example -- quite interesting if I can get all these invs

  Lots more example from this guy's thesis -- very interesting ones too


  void fig1_1(int x){
  int y; int b;
  if (x > 0) {
  y = x;
  }
  else { 
  y = -x;
  }
  
  if (y>10){
  b = 1;
  }
  else{
  b = 0;
  }


  printf("x y b\n");
  printf("%d %d %d\n",x,y,b);

  //inv
  
  int c1 = (b == 1 && y > 10 && y == x) ;
  int c2 = (b == 1 && y > 10 && y == -x) ;
  int c3 = (b == 0 && y <= 10 && x > 0 && y == x) ;
  int c4 = (b == 0 && y <= 10 && x <= 0 && y == -x) ;
  assert(c1 || c2 || c3 || c4);

 

  assert ((x > 0 && y == x) || (x <= 0 && y == -x));

  //b => (x < -10 or 10 < x)
  assert (b==0 || (x < 10 || 10 < x));

  //I think this is also an inv
  //b = 0 =>  !(x < -10 || 10 < x)
  assert(b == 1 || (x >= -10 && 10 >= x));

  //in other words,  b *iff* (x <-10 || 10 < x)
  }


  int fig2_6_mn(int x){
  if (x > 0){
  x = fig2_6_mn(x-1);
  }
  
  return x;
  }

  void fig2_6_mn_caller(int x){
  int t = fig2_6_mn(x);
  //inv 

  printf("x t\n");
  printf("%d %d\n",x,t);
  assert ((x <= 0 && t==x) || (x > 0  && t==0));  
  }



  int f91(int x) {
  if (x<=100){
  return f91(f91(x+11));
  }
  else{
  return x-10;
  }
  }

  int f91_caller(int x){
  int t = f91(x);
  printf("x t\n");
  printf("%d %d\n",x,t);
  assert((x >= 101 && t==x-10) || (x<=100 && t == 91) );
  }

  // quicksort

  void swap(float a[], int i, int j) {
  float temp = a[i]; 
  a[i] = a[j]; 
  a[j] = temp;
  }


  int changeN(float a[], int n, int i, int h, float v) { 
  if (i <= h){
  if (a[i] < v){ 
  swap(a,n+1,i); 
  return changeN(a,n+1,i+1,h,v);
  } 
  else { 
  return changeN(a,n,i+1,h,v);
  } 
  } 
  else { 
  return n ;
  } 
  }

  int mypartition(float a[], int l, int h){
  int v = a[l]; 
  int n = changeN(a,l,l+1,h,v); 
  swap(a,l,n);
  return n ;
  }


  /* MY EXAMPLES 

  void maxfun(int a, int b, int c){
  int t = a ;
  if (b > t){
  t = b;
  }
  if (c > t){
  t = c;
  }
  printf("a b c t\n");
  printf("%d %d %d %d\n",a,b,c,t);
  }


  void myminmax(const int a, const int b){
  //suppose to give max(x,y) >= max(a,b)
  //similar to the mymemcpy but easier for me to debug

  int x = a;
  int y = b;
  
  int i = 0 ;
  printf("a b x y\n");
  while(i < 10){
  printf("%d %d %d %d\n",a,b,x,y);
  assert(max(x,y) >= max(a,b));

  if (x == max(x,y)){
  x = x + randrange_i(0,100,1);
  y = y + randrange_i(-100,100,1);
  }
  else{
  y = y + randrange_i(0,100,1);
  x = x + randrange_i(-100,100,1);
  }
  i++;
  }


  }







*/


/*Program from http://www.model.in.tum.de/~popeea/research/disjunctive.asian06.pdf */


/* int find_elem(A,siz,e){ */
/*   int found = -1; */
/*   for(int i = 0 ; i < siz; ++i){ */
/*     if (A[i] == e){ */
/*       found = 1; */
/*     } */
/*   } */
/*   /\*0<=idx<=i => *\/ */
/* } */




/* From Synergy paper: SYNERGY: A New Algorithm for Property Checking */

void syn_fig6(int y){
  while (y > 0) {
    printf("L_POST: y\n");
    printf("L_POST: %d\n",y);
    y = y - 1;
  }
  printf("L1: y\n");
  printf("L1: %d\n",y);

  //assume(false);
}


void syn_fig9( ){
  int x, y;
  x = 0;
  y = 0;
  while (y >= 0) {
  y = y + x;
  }
  //assert(false);
}


/* From http://www7.in.tum.de/~popeea/research/disjunctive.asian06.pdf */


/* http://pages.cs.wisc.edu/~bgogul/Research/Papers/vmcai12.pdf */


/* http://www.di.ens.fr/~mine/publi/article-chen-al-sas09.pdf */


/*From http://theory.stanford.edu/~aiken/publications/papers/cav11.pdf 

The program ex1 used for motivating example in Icse2013
*/




int driver_disj(char **argv){
  if (strcmp(argv[1],"max_ex1")==0){
    max_ex1(atoi(argv[2]));
    return 1;
  }

  else if (strcmp(argv[1],"min_ex1")==0){
    min_ex1(atoi(argv[2]));
    return 1;
  }

  else if (strcmp(argv[1],"max_ex1a")==0){
    max_ex1a(atoi(argv[2]));
    return 1;
  }

  else if (strcmp(argv[1],"t1")==0){
    t1(atoi(argv[2]));
    return 1;
  }

  else if (strcmp(argv[1],"vumemcopy")==0){
    int stime = (unsigned int)time(0) + atoi(argv[2])*10 + atoi(argv[3])*100;
    srand(stime);
    vumemcopy(atoi(argv[2]),atoi(argv[3]));
    return 1;
  }

  else if (strcmp(argv[1],"vumemcopy_abstract")==0){
    int stime = (unsigned int)time(0) + atoi(argv[2])*10 + atoi(argv[3])*100;
    srand(stime);
    vumemcopy_abstract(atoi(argv[2]),atoi(argv[3]));
    return 1;
  }

    

  else if (strcmp(argv[1],"strncopy")==0){
    int stime = (unsigned int)time(0) + atoi(argv[2])*10 + atoi(argv[3])*100;
    srand(stime);
    strncopy(atoi(argv[2]),atoi(argv[3]));
    return 1;
  }    

  //Other MPP invs
  else if (strcmp(argv[1],"partial_decr0")==0){
    partial_decr0(atoi(argv[2]));
    return 1;
  }

  else if (strcmp(argv[1],"partial_incr0")==0){
    partial_incr0(atoi(argv[2]));
    return 1;
  }

  else if (strcmp(argv[1],"partial_decr1")==0){
    partial_decr1(atoi(argv[2]),atoi(argv[3]));
    return 1;
  }

  else if (strcmp(argv[1],"partial_incr1")==0){
    partial_incr1(atoi(argv[2]),atoi(argv[3]));
    return 1;
  }

  else if (strcmp(argv[1],"partial_decr2")==0){
    partial_decr2(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]));
    return 1;
  }

  else if (strcmp(argv[1],"partial_incr2")==0){
    partial_incr2(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]));
    return 1;
  }

  else if (strcmp(argv[1],"partial_decr3")==0){
    partial_decr3(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),
		  atoi(argv[5]));
    return 1;
  }

  else if (strcmp(argv[1],"partial_incr3")==0){
    partial_incr3(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),
		  atoi(argv[5]));
    return 1;
  }

  else if (strcmp(argv[1],"partial_decr4")==0){
    partial_decr4(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),
		  atoi(argv[5]),atoi(argv[6]));
    return 1;
  }

  else if (strcmp(argv[1],"partial_incr4")==0){
    partial_incr4(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),
		  atoi(argv[5]),atoi(argv[6]));
    return 1;
  }
  else if (strcmp(argv[1],"partial_decr5")==0){
    partial_decr5(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),
		  atoi(argv[5]),atoi(argv[6]),atoi(argv[7]));
    return 1;
  }

  else if (strcmp(argv[1],"partial_incr5")==0){
    partial_incr5(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),
		  atoi(argv[5]),atoi(argv[6]),atoi(argv[7]));
    return 1;
  }
  //Search
  else if (strcmp(argv[1],"vusearch3")==0){
    vusearch3(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),atoi(argv[5]));
    return 1;
  }

  //Odd-Even sort
  else if (strcmp(argv[1],"oddeven2")==0){
    oddeven2(atoi(argv[2]),atoi(argv[3]));
    return 1;
  }

  else if (strcmp(argv[1],"oddeven3")==0){
    oddeven3(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]));
    return 1;
  }

  else if (strcmp(argv[1],"oddeven4")==0){
    oddeven4(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),atoi(argv[5]));
    return 1;
  }

  else if (strcmp(argv[1],"oddeven5")==0){
    oddeven5(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),
	     atoi(argv[5]),atoi(argv[6]));
    return 1;
  }
  else if (strcmp(argv[1],"oddeven6")==0){
    oddeven6(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),
	     atoi(argv[5]),atoi(argv[6]),atoi(argv[7]));
    return 1;
  }
  else if (strcmp(argv[1],"oddeven7")==0){
    oddeven7(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),
	     atoi(argv[5]),atoi(argv[6]),atoi(argv[7]),atoi(argv[8]));
    return 1;
  }
  else if (strcmp(argv[1],"oddeven8")==0){
    oddeven8(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),
	     atoi(argv[5]),atoi(argv[6]),atoi(argv[7]),
	     atoi(argv[8]),atoi(argv[9]));
    return 1;
  }
  /* else if (strcmp(argv[1],"oddeven9")==0){ */
  /*   oddeven9(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]), */
  /* 	       atoi(argv[5])); */
  /* } */


  else if (strcmp(argv[1],"f91")==0){
    printf("#result = %d\n", f91(atoi(argv[2])));
    return 1;
  }    

  else if (strcmp(argv[1],"f91_nr")==0){
    printf("#result = %d\n", f91_nr(atoi(argv[2])));
    return 1;
  }    

  else if (strcmp(argv[1],"fig1_1")==0){
    fig1_1(atoi(argv[2]));
    return 1;
  }
    
  else if (strcmp(argv[1],"fig2a")==0){
    fig2a(atoi(argv[2]));
    return 1;
  }
    
  else if (strcmp(argv[1],"fig2_6_mn_caller")==0){
    fig2_6_mn_caller(atoi(argv[2]));
    return 1;
  }

  else if (strcmp(argv[1],"myminmax")==0){
    myminmax(atoi(argv[2]),atoi(argv[3]));
    return 1;
  }
    
  else if (strcmp(argv[1],"maxfun")==0){
    maxfun(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]));
    return 1;
  }
  return 0;
}
