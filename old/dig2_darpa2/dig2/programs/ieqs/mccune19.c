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

