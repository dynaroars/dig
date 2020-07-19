/*
LIA (Loop invariant involving arrays)
Testsuite containing various functions that have loop invariants involving arrays
 */


/*Sorting algorithms*/


/*Search algorithms*/


/*
Array operations
"Aligators for Arrays (tool paper) 
*/

void copy(int A[],int B[], const int N){
  
  int i = 0; 
  while (i < N){
    B[i] = A[i]; 
    i = i + 1 ;
  }
  //\forall k. 0≤k<i \implies (B[k]=A[k] \wedge k<N)
}

void copy_prop(int A[], int B[], const int N){
  int i = 0; 
  while (i < N){
    A[i] = 0; 
    i = i + 1;
  };
  i = 0; 
  while (i < N){
    B[i] = A[i]; 
    i = i + 1; 
  }
  //(\forall k. 0≤k<i \implies (A[k]=0 \wedge k<N))  \wedge  (\forall k. 0 ≤ k<N  \implies  (B[k] = A[k] \wedge k < N))
}


void init(int A[], const int N){
  int i = 0; 
  while (i < N){
    A[i] = 0; 
    i = i + 1; 
  }
  //\forall k. 0≤k<i \implies (A[k]=0 \wedge k<N)
}


/*Array parititioning 
  (also found in Finding Loop Invariants for Programs over ARrays Using a Theorem Prover)*/
void partition(int A[], int B[], int C[], const int N){

 int i = 0; int j = 0; int k = 0; 
 while(i <= N){
   /*(\forall k. 0 ≤ k<j1 \implies (k < N \wedge C[k]≥0))  
     \wedge  (\forall k. 0≤k<j2 \implies (k<N \wedge B[k]<0))*/
   if (A[i] >= 0){
     B[j] = A[i];
     j = j + 1;
   }
   else{
     C[k] = A[i];
     k = k + 1;
   }
   i = i + 1;
 }
}



void part_init1(int A[], int B[], const int N){
  int i = 0; 
  int j = 0; 
  while (i < N){
    if (A[i]>=0){
      B[j] = i; 
      j = j + 1;
    }
    i = i + 1;
  }
  //\forall k. 0 ≤ k<j  \implies  (B[k] < N \wedge A[B[k]]≥0)
}

void part_init2(int A[], int B[], int C[], const int N){
  int i = 0; 
  int j = 0; 
  while (i < N){
    if (A[i] == B[i]){
      C[j] = i;
      j = j + 1;
    }; 
    i = i + 1;
  }
  //\forall k. 0 ≤ k<j  \implies  (C[k] < N \wedge A[C[k]]=B[C[k]])
}


void permutation(int A[], int B[], const int N){
  int i = 0; 
  while (i < N){
    // B[σ(i)] = A[i]; /*todo: need \sigma */
    i = i + 1; 
  }
  //\forall k. 0 ≤ k<i  \implies  (B[σ(k)] = A[k] \wedge k < N)
}

void vararg(int A[]){
  int i = 0; 
  while (A[i] != 0){
    i = i + 1; 
  }

  //\forall k. 0≤k<i \implies (A[k]0∨A[k]>0)
}



