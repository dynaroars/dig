#include <stdio.h>
#include <math.h>
#include <stdlib.h>  //required for afloat to work
#include <assert.h>
#include <time.h>
#include <string.h>
#include <ctype.h>
#include "strmap.h"


//Helpers
#define TRUE 1
#define FALSE 0
#define INCLUDE 1
#define EXCLUDE 0
#define MAX_LOOP  2000
#define MAX_OUTPUT 1000



void print_array(const int a[], const int siz, const int verbose, 
		 const int print_endline){


  int i = 0;
  if(verbose){
    for (; i < siz ; ++i){
      printf("[%i] -> %d, ", i,a[i]);
    }
  }
  else{
    for(; i < siz ; ++i){
      printf("%d, ",a[i]);
    }
  }
  if (print_endline){
    printf("\n");
  }
}



char buf[128];

struct tracker{
  int loop_ctr;
  int* tracker_p;//number of times entering an if branch
  int size;  //size of tracker_p

  StrMap* smap; //hash table: only display data that we haven't seen
};
struct tracker TKR;

void init_tracker(){
  TKR.loop_ctr = -1;

  TKR.size = -1;
  TKR.tracker_p  = NULL;

  TKR.smap = strmap_new(MAX_OUTPUT);
  if (TKR.smap==NULL){
    printf("cannot allocate space (%d) for smap\n",MAX_OUTPUT);
    exit(1);
  }
}

void clean_tracker(){
  TKR.loop_ctr  = -1;
  TKR.size = -1;

  if (TKR.tracker_p != NULL){
    free(TKR.tracker_p);
    TKR.tracker_p  = NULL;
  }
  
  

  if (TKR.smap != NULL){
      strmap_delete(TKR.smap);
      TKR.smap = NULL;
    }
  
  
}


void set_tracker(const int size){
  int* p;
  int i;

  TKR.loop_ctr = 0;
  TKR.size = size+1;
  if (TKR.tracker_p != NULL){
    printf("##free tracker_p\n");
    free(TKR.tracker_p);
  }
  TKR.tracker_p = malloc(TKR.size * sizeof(p));
  for (i = 0 ; i < TKR.size ; ++i){
    TKR.tracker_p[i] = 0;
  }
}

void print_tracker(const int VERBOSE){
  print_array(TKR.tracker_p,TKR.size,VERBOSE,TRUE);
}

void incr_tracker_pos(const int pos){
  TKR.tracker_p[pos]++;
}

int get_n_incr_loop_ctr_tracker(){
  int ret_val = TKR.loop_ctr;
  TKR.loop_ctr++;
  return ret_val;
}

void hash_print(char *buf){
  char buf_t[128];
  if (strmap_get(TKR.smap, buf, buf_t,sizeof(buf_t)) == 0){
    strmap_put(TKR.smap,buf,"");
    printf("%s",buf);
  }
}




/* MISCS */

int myissorted(const int *arr, const int start, const int end){
  /*To check if an array of size S is sorted, then use
   myisorted(arr, 0, S) 
  */

  int i = 0;

  for (i=start; i<end-1; ++i){
    if(arr[i]>arr[i+1]){
      return FALSE;
    }
  }

  return TRUE;
}

int myisprime(int number) {
  if (number == 1)return FALSE;
  if (number == 2)return TRUE;
  if (number % 2 == 0)return FALSE;

  int d = 3;
  for (; d <= (int)sqrt((float)number); d++){
    if (number % d == 0)
      return FALSE;
  }
  return TRUE;
}

double randrange_f(const double min, const double max, 
                   const int including){
  //returns a rand # btw min and max
  //if including=1 then it will include max, otherwise excluding
  //printf("min %g, max %g\n",min,max);

  if (max-min < 0.0){
    printf("cannot do randrange_f(%g,%g)\n", min, max);
    assert(0);
  }

  return min + ((max - min) * rand()) / (RAND_MAX + (double)including) ;
}

float randrange_p(const float min, const float max,
                   const int including,const int prec){
  //returns a rand # btw min and max with precision <= prec
  //if including=1 then it will include max, otherwise excluding
  //printf("min %g, max %g\n",min,max);

  

  if (max-min < 0.0){
    printf("cannot do randrange_p(%g,%g)\n", min, max);
    assert(0);
  }

  int n = pow(10,prec);
  int range = (int)((max-min)*(float)n)+including;
  float rnum = (float)(rand()%range)/(float)n;
  //printf("n=%d,range=%d, rnum=%g\n",n,range,rnum);
  float result = min + rnum;
  assert(min<=result);
  if(including){
    assert(result<=max);
  }
  else{
    assert(result<max);
  }
  return result;
}


int randrange_i(const int min, const int max, const int including){
  //returns a rand # btw min and max
  if (max-min < 0){
    printf("cannot do randrange_i(%d,%d)\n",min,max);
    assert(0);
  }
  return min + rand()%(max-min+including);
}

int myeven(const int u){return u % 2 == 0;}
int myodd(const int u){return !myeven(u);}

int min(const int a, const int b){return (a<=b)? a:b;}
int max(const int a, const int b){return (a<b)? b:a;}






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
