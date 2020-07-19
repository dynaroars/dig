/*
From Mccune paper
 */

int vu_ex1(){
  /*simple example showing dynamic analysis is not as 
   powerful as static anlays.
  The inv for x is x>=0  (i.e. no upperbound on x)
  */

  int x;
  int icounter=0;
  printf("x\n");
  while(get_n_incr_loop_ctr_tracker()<MAX_LOOP){
    printf("%d\n",x);
    x++;
  }
}

int mccune_ex4(){
  int x,y;
  x = 2;
  y = 3;
  printf("x y\n");
  while(TRUE){
    assert(-5<=x+y && x+y<=7); //inv
    printf("%d %d\n",x,y);
    if (!(x+y>=0)){
      break;
    }

    if(y>=2){
      y = -y + 4;
      x = -x + 3;
    } 
    else{
      x = -x - 3;
      y = -y + 5;
    }
  }
  return 0;
}


int mccune_ex5(){
  int x = 10; 
  int y =  0; 

  printf("x y\n");
  while(TRUE){

    assert(2 <= x - y && x - y <= 10);
    assert(x+y <= 10);
    assert(4 <= x && x <= 10);
    assert(0 <= y && y <= 2);
    
    printf("%d %d\n",x,y);
    if (!(x - y >= 3)){
      break;
    }
    if (x >= 5){
      x = x - 1;
    } 
    else{
      y = y + 1;
    }
  }
  return 0;
}



int mccune_ex6(){
  int x = 4; 
  int y = 6;
  printf("x y\n");
  while(TRUE){

    assert(-9 <= x - y && x - y <= 9);
    assert(-11 <= x + y && x + y <= 10);
    assert(-6 <= x && x <= 6);
    assert(-5 <= y && y <= 6);

    printf("%d %d\n",x,y);
    if (!(x+y>=0)){
      break;
    }
    if (y >= 6){
      x = -x;
      y = y-1;
    } 
    else{
      x = x-1;
      y = -y;
    }
  }
  return 0;
  
}


int mccune_ex7(){
  int x = 4; 
  int y = 6;
  printf("x y\n");
  while(TRUE){

    assert(-9 <= x - y && x - y <= 9);
    assert(-10 <= x + y && x + y <= 10);
    assert(-4 <= x && x <= 4);
    assert(-5 <= y && y <= 6);

    printf("%d %d\n",x,y);
    if (!(x+y>=0)){
      break;
    }
    if (y >= 6){
      x = -x;
      y = y-1;
    } 
    else{
      x = -x;
      y = -y;
    }
  }
  return 0;
  
}


int mccune_ex8(){
  int x = 0; 
  printf("x\n");
  while(TRUE){
    
    assert(-9 <= x &&  x <= 10);  //gqe result
    assert(0 <= x && x <= 1); //dig result

    printf("%d\n",x);
    if (!(x <= 10)){
      break;
    }
    x = 1 - x;
  }
  return 0;
  
}


int mccune_ex9_20(int loop_i){
  //Examples 9 and 20
  printf("#loop %d\n", loop_i);

  int x = 0; 
  int y = 5;

  printf("x y\n");
  while(TRUE){

    assert(-5 <= x - y && x - y <= 10);
    assert(-5 <= x + y && x + y <= 15);
    assert(0 <= x && x <= 10);
    assert(0 <= y && y <= 5);
    if (loop_i == 0){
      printf("%d %d\n",x,y);
    }
    if (x < 10 && y == 5){
      x = x + 1;
    }else if (x == 10 && y > 0){
      y = y - 1;
    }
    else{
      while(TRUE){
	assert(-5 <= x - y && x - y <= 10);
	assert(-5 <= x + y && x + y <= 15);
	assert(0 <= x && x <= 10);
	assert(0 <= y && y <= 5);

	if (loop_i==1){
	  printf("%d %d\n",x,y);
	}
	if (!(y < 5)){
	  break;
	}
	x = x - 1;
	y = y + 1;
      }
    }

  }
  return 0;
  
}


int mccune_ex14(){
  int x = 0; 
  int y = 5;
  printf("x y\n");
  while(TRUE){

    assert((0 <= x && x <= 5 && y == 5) || (5 <= x <= 10 && x==y));

    printf("%d %d\n",x,y);
    if (!(x < 10)){
      break;
    }

    if (x < 5){
      x = x + 1;
    } 
    else{
      x = x + 1;
      y = y + 1;
    }
  }
  return 0;
}

int mccune_ex14a(int x){
  int y = 5;
  printf("x y\n");
  while(TRUE){


    if (!(x < 10)){
      break;
    }
    printf("%d %d\n",x,y);
    assert((x <= 5 && y == 5) || (5 <= x <= 10 && x==y));


    if (x < 5){
      x = x + 1;
    } 
    else{
      x = x + 1;
      y = y + 1;
    }
  }
  return 0;
}

int mccune_ex19(){
  int x = 0; 
  int y = 0;
  printf("x y\n");
  while(TRUE){

    printf("%d %d\n",x,y);
    if (y == 0 && x < 10){
      x = x + 1;
    } 
    else if (x >= 10 && y < 5){
      y = y + 1;
    }
    else{
	x = x - 1;
	y = y - 1;
      }

  }
  return 0;
}


int driver_mccune(char **argv){
    if (strcmp(argv[1],"mccune_ex4")==0){
      printf("#result = %d\n", mccune_ex4());
      return 1;
    }

    else if (strcmp(argv[1],"mccune_ex5")==0){
      printf("#result = %d\n", mccune_ex5());
      return 1;
    }

    else if (strcmp(argv[1],"mccune_ex6")==0){
      printf("#result = %d\n", mccune_ex6());
      return 1;
    }

    else if (strcmp(argv[1],"mccune_ex7")==0){
      printf("#result = %d\n", mccune_ex7());
      return 1;
    }

    else if (strcmp(argv[1],"mccune_ex8")==0){
      printf("#result = %d\n", mccune_ex8());
      return 1;
    }

    else if (strcmp(argv[1],"mccune_ex9_20_0")==0){
      printf("#result = %d\n", mccune_ex9_20(0));
      return 1;
    }

    else if (strcmp(argv[1],"mccune_ex9_20_1")==0){
      printf("#result = %d\n", mccune_ex9_20(1));
      return 1;
    }


    else if (strcmp(argv[1],"mccune_ex14")==0){
      printf("#result = %d\n", mccune_ex14());
      return 1;
    }

    else if (strcmp(argv[1],"mccune_ex14a")==0){
      printf("#result = %d\n", mccune_ex14a(atoi(argv[2])));
      return 1;
    }

    else if (strcmp(argv[1],"mccune_ex19")==0){
      printf("#result = %d\n", mccune_ex19());
      return 1;
    }

    return 0;
}
