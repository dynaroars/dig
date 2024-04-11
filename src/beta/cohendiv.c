#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int w, int x, int y){}
//void vtrace1(int x, int c, int c2, int r, int c1){}
//void vtrace2(int x, int c, int c2, int r, int c1){}

int mainQ(int rho, int x, int y){
    int w = 0;                   
    if (rho){
        w = x;
    }else{
        w = 10;
    }

    if (w == x){
        x = y;
    }
    vtrace1(w,x,y);
}

//int mainQ(int x, int y){
/* int mainQ(int c, int n) { */
/*     vassume(c >= 0); */
/*     //if(c < 0) return 0; */
    
/*     int c2=c; */
/*     int x, r=0; */

/*     int j1 = 0; */
    
/*     while(j1 <= 100) { */
/*         j1++; */
/*         int c1=c; */
/*         while(c1>0) { r = r+c1; c1--; } */
/*         x = (2*r) - (c*c) + 1; */
/*         vtrace1(x, c,c2,r,c1); */
/*         // DIG Infer:  { x == 1 } */
/*         while(n>0) n--; */
/*         r=0; */
/*         while(c2>0) { r = r+c2; c2--; } */
/*         x =  (2*r) - (c2*c2);       // DIG Infer: { x = 0; } */
/*         vtrace2(x, c, c2, r, c1); */
/*     } */
/* } */

    
    /* vassume(x >= 1 && y >= 1); */
    
    /* int q=0; */
    /* int r=x; */
    /* int a=0; */
    /* int b=0; */
    /* while(1) { */
    /* 	vtrace1(q, r, a, b, x, y); */
    /* 	if(!(r>=y)) */
    /* 	    break; */
    /* 	a=1; */
    /* 	b=y; */
	  
    /* 	while (1){ */
    /* 	    vtrace2(q, r, a, b, x, y); */
    /* 	    if(!(r >= 2*b)) */
    /* 		break; */
	       
    /* 	    a = 2*a; */
    /* 	    b = 2*b; */
    /* 	} */
    /* 	r=r-b; */
    /* 	q=q+a; */
    /* } */
    
    /* return q; */
//}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]),atoi(argv[2]),atoi(argv[3]));
}


