/* Generated by CIL v. 1.7.3 */
/* print_CIL_Input is false */

#include "stdio.h"
#include "stdlib.h"
#include "assert.h"
#include "math.h"
int __VERIFIER_nondet_int(){}

void __VERIFIER_assume(int r ) 
{ 


  {
  return;
}
}
void vassume(int r ) 
{ 


  {
  return;
}
}
int x  ;
int y  ;

void vtrace20(int a, int b, int c){}
void vtrace21(int a, int b, int c){}
void vtrace22(int a, int b, int c){}
void vtrace24(int a, int b, int c){}
void vtrace25(int a, int b, int c){}
void vtrace27(int a, int b, int c){}
void vtrace28(int a, int b, int c){}
void vtrace30(int a, int b, int c){}

/* int main(int a , int b )  */
int mainQ(int a , int b ) 
{ 
  int c ;
  int d;
  x = a;
  y = b;

  {
  c = 0;
  d = 0;
  //vtrace20(x, y, c);
  //x = __VERIFIER_nondet_int();
  //vtrace21(x, y, c);
  //y = __VERIFIER_nondet_int();
  //vtrace22(x, y, c);
  while (c <= 2) {
    c ++;
    //vtrace24(x, y, c);
    //y = 1;
    //vtrace25(x, y, c);
    while (x > 0 && d <= 3) {
        d++;
      c --;
      x--;
      //printf("%d %d %d\n",x,y,c);
      vtrace27(x, y, c);
      x = x & (c - 1);
      //vtrace28(x, y, c);
      /* if (x <= 1) { */
      /*   y = 0; */
      /*   //vtrace30(x, y, c); */
      /* } */
    }
  }
  return (0);
}
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
