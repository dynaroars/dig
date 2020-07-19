int inf1(int a, int b, int c){
  /*BUG: a < c fails when inputs is 0 0 0*/

  int flag1,flag2;
	
  if (a > b) {
    flag1 = 1;
  } else {
    flag1 =0;
  }
  
  if (b > c){
    flag2 =1;
  } else {
    flag2 = 0;
  }
  printf("a b c flag1 flag2\n");
  printf("%d %d %d %d %d\n",a,b,c,flag1,flag2);
  
  /* if (flag1 == 1){ */
  /*   if (flag2 == 1){ */
  /*     assert( a >= c); */
  /*   } */
  /* } */
  
  /* if ( flag2 -flag1 <= 0 ) { */
  /*   if (flag1 + flag2 < 1){ */
  /*     assert(a < c); */
  /*   } */
  /* } */
  return 1;
}


int driver_nec(char **argv){

  if (strcmp(argv[1],"inf1")==0){
    inf1(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]));
    return 1;
  }

  return 0;
}
