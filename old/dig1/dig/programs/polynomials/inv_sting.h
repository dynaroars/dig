/*
  From Stanford Inv Generator website (STING) 
  http://www.cs.colorado.edu/~srirams/Software/sting.html
*/



void seesaw_dummy(x,y){}
int seesaw(int seed){
  /*A simple 2D example.
    Safety analysis can be "cooked" by modifying this system. 
    CH79 widens out to true

    tvn: I can't find this example from CH78 (CH79 doesn't exist).
  */
  
  srand(seed);

  //Location l0
  int x=0;
  int y=0;
  set_tracker(4);

  printf("x y\n");
  while(get_n_incr_loop_ctr_tracker() < MAX_LOOP){
    
    assert(2*y - x >= 0);  
    assert(3*x - y >= 0);
    sprintf(buf,"%d %d\n",x,y);
    hash_print(buf);

    seesaw_dummy(x,y);


    int rd = randrange_i(1,4,INCLUDE);

    //Transition t1: l0,
    if (rd == 1 && x >= 5  && x <= 7){
      incr_tracker_pos(rd);

      x = x + 2;
      y = y + 1;
    }

    //Transition t2: l0,
    if (rd == 2 && x <= 4){
      incr_tracker_pos(rd);

      x = x + 1;
      y = y + 2;
    }

    //Transition t3: l0,
    if(rd == 3 && x >= 7 && x <=9){
      incr_tracker_pos(rd);

      x = x + 1;
      y = y + 3;
    }

    //Transition t4: l0,
    if (rd == 4 && x >= 9){
      incr_tracker_pos(rd);

      x = x+2;
      y = y+1;
    }
  }

  print_tracker(FALSE);
  return -1;
}


int robot(int seed){
  //Example taken originally from Henzinger Ho 1993?
  //See CAV 2003 paper for details
  //todo: to check

  srand(seed);

  double x = 0.0;
  double y = 0.0;
  double t = 0.0;

  set_tracker(2);

  while(get_n_incr_loop_ctr_tracker() < MAX_LOOP){

    assert(t <= x && x <= 2*t);
    assert(y<=2*t);
    //2 more invariants cannot get
    //see cav03

    int rd = randrange_i(1,2,TRUE);
    
    if(rd==1){
      incr_tracker_pos(rd);

      /*[1,2] =  t' - t */
      double td = randrange_f(1.0,2.0,TRUE);
      t = t + td;
      
      /*[td,2td] = x' -x */
      double xd = randrange_f(td,2.0*td,TRUE);
      x = x + xd;

      /*[td,2td] = y' -y */
      double yd = randrange_f(td,2.0*td,TRUE);
      y = y + yd;

      assert(td <= xd && xd <= 2.0 * td);
      assert(td <= yd && yd <= 2.0 * td);
      assert(1.0 <= td && td <= 2.0);
      
    }
    else{
      incr_tracker_pos(rd);
      
      /*[1,2] =  t' - t */
      double td = randrange_f(1.0,2.0,TRUE);
      t = t + td;
      
      /*[td,2td] = x' -x */
      double xd = randrange_f(td,2.0*td,TRUE);
      x = x + xd;

      /*[-2td,-td] = x' -x */
      double offset = 0.0 - (-2.0 * td);
      double yd = randrange_f(0, -td + offset,TRUE)  - offset;
      y = y + yd;

      assert(td <= xd && xd <= 2.0 * td);
      assert(-td >= yd && yd >= -2*td);
      assert(1.0 <= td && td <= 2.0);

    }


  }

  print_tracker(FALSE);
  return -1;
}//robot


/*train-hpr97*/
/* # int trainbeacon(b1,s,d){ */
/* #   #folklore example */
/* #   #From the description in Halbwachs97 journal paper */

/* #   #propsteps(2) */

/* #   #Location ontime */
/* #   b1=0 */
/* #   s=0 */
/* #   d=0 */

/* #   #Location late1 */
/* #   b1 -s +10 =0 */
/* #   d=0 */
/* #   b1 >=0 */
/* #   s>=0 */

/* #   #Location onbrake */
/* #   b1-s-10=0 */
/* #   d=0 */
/* #   b1 >=0 */
/* #   s>=0 */




/* #   #at location ontime beacon is not going to advance  */

/* #   #second advances */

/* #   #Transition second_advance:ontime,ontime, */

/* #   #'b1-b1=0 */
/* #   s=s+1 */
/* #   #'d-d=0 */

/* #   #beacon advances */
/* #   #Transition beacon_advance:ontime, */
/* #   b1 = b1+1 */
/* #   #'s-s=0 */
/* #   #'d-d=0 */

/* #   #Train 1 is 10 beacons behind */
/* #   #Transition run_late1: ontime,late1, */
/* #   if(b1-s+10<=0){ */
/* #     #'b1-b1=0 */
/* #     #'s-s=0 */
/* #     #'d-d=0 */


/* #   #Train 1 beacon advance when late */

/* #   #Transition tr1_beacon_advance:late1, */
/* # #   'b1-b1-1=0 */
/* # #   preserve[s,d] */


/* # #   #Train 1 comes back on time */

/* # # Transition back_on_time1: late1,ontime, */
/* # # b1 -s >=0 */
/* # # preserve[b1,s,d] */


/* # # #Train 1 becomes early */

/* # # Transition run_early1: ontime,onbrake, */
/* # # b1 -s -10 >=0 */
/* # # 'd=0 */
/* # # preserve[b1,s] */


/* # # #delay and second advance when on brake */

/* # # Transition on_brake_second_tick: onbrake, */
/* # # 's-s-1=0 */
/* # # 'd-d-1=0 */
/* # # 'b1-b1=0 */


/* # # #beacon advance */

/* # # Transition onbrake_beacon_advance:onbrake, */
/* # # 'b1-b1-1=0 */
/* # # preserve[s,d] */

/* # # #onbrake to ontime */

/* # # Transition back_on_time_ob: onbrake,ontime, */
/* # # b1 - s <=0 */
/* # # 'd=0 */
/* # # preserve[s,b1]  */

/* # # Transition complete_stop_os: onbrake,stopped, */
/* # # d -10 >=0 */
/* # # preserve[b1,d,s] */


/* # # Transition time_advance_on_stop_1: stopped,stopped, */
/* # # 's-s-1=0 */
/* # # preserve[b1,d] */


/* # # Transition back_on_time_so: stopped,ontime, */
/* # # b1 -s <=0 */
/* # # 'd=0 */
/* # # preserve[b1,s] */



void berkeley_dummy(int invalid, int unowned, 
                    int nonexclusive, int exclusive){}
int berkeley(int invalid, int exclusive, int nonexclusive, int unowned){
  
 
  printf("#inv: invalid + unowned + nonexclusive + exclusive -1 >= 0\n");
  printf("invalid unowned nonexclusive exclusive\n");

  set_tracker(3);


  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){


    assert(exclusive >= 0);
    assert(unowned >= 0);
    assert(invalid + unowned + nonexclusive + exclusive -1 >= 0); //ineq
   
    printf("%d %d %d %d\n",invalid, unowned, nonexclusive, exclusive);
    berkeley_dummy(invalid, unowned, nonexclusive, exclusive);
    
    int rd = randrange_i(1,3,INCLUDE);
    
    if (invalid >= 1 && rd == 1){ //transition t1: l0,
      incr_tracker_pos(rd);

      nonexclusive = nonexclusive + exclusive;
      exclusive = 0;
      invalid = invalid - 1;
      unowned = unowned + 1;
    }

    if (nonexclusive + unowned >= 1 && rd == 2){//transition t2: l0
      incr_tracker_pos(rd);

      invalid = invalid + unowned + nonexclusive - 1;
      exclusive = exclusive + 1;
      unowned = 0;
      nonexclusive = 0;
    }

    if (invalid >= 1 && rd == 3){//transition t3: l0
      incr_tracker_pos(rd);

      unowned = 0;
      nonexclusive = 0;
      exclusive = 1;
      invalid = invalid + unowned + exclusive + nonexclusive +  - 1;
    }
  }
  
  print_tracker(TRUE);
  return -1;
}

void berkeley_nat_dummy(int invalid, int unowned, 
                        int nonexclusive, int exclusive){}
int berkeley_nat(int invalid, int exclusive, int nonexclusive, int unowned){

  //int invalid=1;
  //int exclusive=0;
  //int nonexclusive=0;
  //int unowned=0;


  set_tracker(3);

  //printf("#inv: invalid + unowned + exclusive -1 >= 0\n");
  printf("invalid unowned nonexclusive exclusive\n");

  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){


    assert(exclusive  >= 0);
    assert(nonexclusive  >= 0);
    assert(unowned  >= 0);
    assert(invalid  >= 0);
    assert(invalid + unowned + exclusive -1 >= 0);
    printf("%d %d %d %d\n",
           invalid, unowned, nonexclusive, exclusive);
    berkeley_nat_dummy(invalid, unowned, nonexclusive, exclusive);

    int rd = randrange_i(1,3,INCLUDE);

    if (invalid >= 1 && rd == 1){//diff than berkeley
      incr_tracker_pos(rd);

      nonexclusive=nonexclusive+exclusive;
      exclusive=0;
      invalid=invalid-1;
      unowned=unowned+1;
    }

    if (invalid >= 1 && rd == 2){//diff than berkeley
      incr_tracker_pos(rd);

      unowned=0;
      nonexclusive=0;
      exclusive=1;
      invalid=invalid+unowned+exclusive+nonexclusive-1;  
    }

    if (nonexclusive + unowned >=1 && rd == 3){
      incr_tracker_pos(rd);

      invalid=invalid + unowned + nonexclusive-1;
      exclusive=exclusive+1;
      nonexclusive=0;
      unowned=0;
    }

  }      
  print_tracker(TRUE);
  return -1;
}


void heap_dummy(int n, int l, int r, int i, int j){}
int heap(int n, int l){ //todo: ask Deepak, will it ever get to t4 ?
  //Adaptation of the heap sort example from the CAV 2003 paper

  //location l0
  assert(n >= 2);
  int r = n;
  int i = l;
  int j = 2 *l;

  assert(n <= 2 * l);
  assert(2 * l <= n + 1);

  printf ("#inv: lots ..\n");
  printf ("n l r i j\n");

  set_tracker(4);

  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){

    assert(2*i - j   == 0);
    assert(-2*l +r  + 1 >= 0);   //ineq
    assert(r -2 >= 0);
    assert(l -1 >= 0);
    assert(n -r  >= 0);
    printf("%d %d %d %d %d\n",n, l, r, i, j);
    heap_dummy(n, l, r, i, j);


    int rd= randrange_i(1,4,INCLUDE);

    //transition t1: l0,
    if (r   >= j + 1 && rd == 1){
      incr_tracker_pos(rd);
      i = j +1;
      j = 2 + 2*j;
    }

    //transition t2: l0,
    if (r  >= j && rd == 2){
      incr_tracker_pos(rd);
      i  = j;
      j = 2*j;
    }

    //transition t3: l0,
    if (l >=2 &&  r >=2 && rd == 3){
      incr_tracker_pos(rd);
      i = l - 1;
      j= 2*l -2;
    }

    //transition t4: l0,
    if (l <= 1 && r >= 3 && rd == 4){
      incr_tracker_pos(rd);
      r = r - 1;
      i = l;
      j = 2*l;
    }



  }

  print_tracker(TRUE);
  return -1;
}

void myheapsort_helper(int *T, int n, int l,int r){

  assert(2 <= n && n<=2*l && 2*l <= n+1);
  assert(r==n);


  int k = -1;
  int i = -1;
  int j = -1;

  //l0
  if (l>=2){
    l = l-1;
    k = T[l];
  }
  else{
    k = T[r];
    T[r] = T[1];
    r = r - 1;
  }
  

  //l1
  while(r >= 2){

    //{8}
    assert(r>=2);
    assert(2*l<=n+1);
    //assert(r+3<=n);
    assert(2*l+2*r*1<=3*n);
    assert(l>=1);
    assert(r<=n);

    i = l;
    j = 2*i;

    while(j<=r){
      //{10}
      assert(r>=2);
      assert(2*l<=n+1);
      assert(r+3<=2*n);
      assert(1<=l);
      assert(r<=n);
      assert(2*i==j);
      assert(l<=i);
      assert(2*i+6*l+r+18<=12*n);
      assert(j<=r);
      assert(2*l+2*r+1<=3*n);
      assert(4*i+2*l+1<=2*r+3*n);

      if (j <= r-1 && T[j] < T[j+1]){
        j = j+1;
      }
      if (k >= T[j]){
        break;
      }
      T[i] =T[j];
      i=j;
      j=2*j;

    }//while

    //{15}
    assert(j+2<=2*i+r);
    assert(2*j+2*l<=4*i+n+1);
    assert(r+3<=2*n);
    assert(1<=l);
    assert(r<=n);
    assert(7*j+6*l+r+18<=12*i+12*n);
    assert(2*i<=j && j <= 2*i+1);
    assert(l<=i);
    assert(2*l+2*r+1<=3*n);
    assert(8*j+2*l+1<=12*i+2*r+3*n);

    T[i]=k;

    if(l>=2){
      l = l-1;
      k = T[l];
    }
    else{
      k = T[r];
      T[r] = T[1];
      r = r - 1;
    }
    //{21}
    assert(r>=1);
    assert(2*l<=n+1);
    assert(r+4<=2*n);
    assert(2*l+2*r+3<=3*n);
    assert(l>=1);
    assert(r<=n);


    T[1] = k;
  }//while
  

}

int myheapsort(int n){
  //create the array
  int *T = (int *)malloc(sizeof(int[n+1]));
  T[0]=-1000;
  int idx = 1; //start idx at 1
  int max_range=max(999999,n);
  for(; idx <= n; ++idx){
    T[idx] =  randrange_i(0,max_range,INCLUDE);
  }

  //print_array(T,n+1,FALSE);
  
  int l_temp = (int)n/2;
  int l = 0;
  if ((int)l_temp * 2.0 == n){
    l = l_temp;
  }
  else{
    l = l_temp + 1;
  }
  int r = n;
  myheapsort_helper(T,n,l,r);

  //print_array(T,n+1,FALSE);
  assert(myissorted(T,1,n+1));
  free(T);
  return -1;
}


int train_rm03(int d, int afu, int amax, int v, int a){
  /*Copied from Rusinowich and Musset TR 2003*/

  //variable [v d a afu amax]
  //Location l0
  //int v=0;
  //int a=0;
  
  assert (afu>=0);
  assert(amax>=0);
	 

  //invs at this loc
	assert(v>=0);
	assert(afu >=0);
  assert(afu - a >=0);
  assert(afu >=0);
  assert(amax>=0);
	assert(afu -v >=0);

  int tval = 5;




  set_tracker(6);

  printf("v d a afu amax\n");
  while(get_n_incr_loop_ctr_tracker() < 2000){

    assert(-1*v -1*a +1*afu +1*amax  >= 0);  //tvn: todo  I need this invariant !
    assert(-1*v +1*afu  >= 0);
    assert(-1*a +1*afu  >= 0);
    assert(1*amax  >= 0);
    //assert(1*d +2*amax  >= 0);
    assert(1*d +2*afu  >= 0);
    assert(1*v  >= 0);

    printf("%d %d %d %d %d\n",v, d, a, afu, amax);

    int rd = randrange_i(1,6,INCLUDE);
    //Transition t1: l0,
    if(rd==1)  {
      incr_tracker_pos(rd);

      if(d - v + amax < 0 && v - afu  >= 0){
        a = afu;
        v = v - afu;
        int vp = randrange_i(0,tval,INCLUDE);
        d = d + vp - v + afu;
      }
    }


    //Transition t2: l0,
    if(rd==2){
      incr_tracker_pos(rd);

      if(d - v + amax < 0 && v - afu < 0){
        a = afu;        
        v = 0;
        int vp = randrange_i(0,tval,INCLUDE);
        d = d + vp;
      }
    }
    
    //Transition t3: l0,
    if(rd==3){
      incr_tracker_pos(rd);

      if(v + amax - afu >= 0 && v - afu >= 0){
        a = afu;
        v = v - afu;
        int vp = randrange_i(0,tval,INCLUDE);
        d = d + vp - v + afu;
      }
    }

    //Transition t4: l0,
    if(rd==4){
      incr_tracker_pos(rd);

      if(v + amax - afu >= 0 && v - afu < 0){
        a  = afu  ;
        v  = 0 ;
        int vp = randrange_i(0,tval,INCLUDE);
        d = d + vp;
      }
    }

    //Transition t5: l0,
    if(rd==5){
      incr_tracker_pos(rd);

      int am = randrange_i(0, amax, INCLUDE);
      if (d - v + amax > 0 && v + amax - afu < 0 && v + am >= 0){
        a = am;
        v = v + am;
        int vp = randrange_i(0,tval,INCLUDE);
        d = d + vp - v - am;
      }
    }

    //Transition t6: l0,
    if(rd==6){
      incr_tracker_pos(rd);

      int am = randrange_i(0, amax,EXCLUDE);
      if (d - v + amax > 0 && v + amax - afu < 0 && v + am < 0){
        a = am;
        v = 0;
        int vp = randrange_i(0,tval,INCLUDE);
        d = d + vp;
      }
    }
  
  }//while */

  print_tracker(TRUE);
  return -1;
}

void efm_dummy(int X1, int X2, int X3, int X4, int X5, int X6){}
int efm(int X1,int X2,int X3, int X4, int X5, int X6){
  
  assert (X1>=1);
  //X2=0
  //X3=0
  //int X4=1;
  //int X5=0;
  //int X6=0;

  assert(X1>=0);
  assert(X2>=0);
  assert(X3>=0);
  assert(X4>=0);
  assert(X5>=0);
  assert(X6>=0);



  set_tracker(5);
  printf("X1 X2 X3 X4 X5 X6\n");

  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){

    assert (X5  >= 0);
    assert (X4  >= 0);
    assert (X3  >= 0);
    assert (X2  >= 0);
    assert (X4 +X5 +X6 -1  == 0); //inv
    assert (-X4 -X5  + 1 >= 0); //inv
    assert (X1 +X5 -1 >= 0);  //inv
    assert (X1 +X2 -X4 -X5  >= 0);  //inv
    assert (X1 +X2 +X3 -1 >= 0);   //inv
    printf("%d %d %d %d %d %d\n",X1, X2, X3, X4, X5, X6);
    efm_dummy(X1, X2, X3, X4, X5, X6);

    int rd = randrange_i(1,5,INCLUDE);
    //transition t1:l0,
    if (X1 >= 1 && X4 >= 1 && rd==1){
      incr_tracker_pos(rd);

      X1=X1-1;
      X4=X4-1;
      X2=X2+1;
      X5=X5+1;
    }

    //transition t2:l0,
    if (X2 >=1 && X6 >= 1 && rd==2){
      incr_tracker_pos(rd);

      X2=X2 -1;
      X3=X3 +1;
    }

    //transition t3:l0,
    if (X4 >= 1 && X3 >= 1 && rd==3){
      incr_tracker_pos(rd);

      X3=X3-1;
      X2=X2+1;
    }

    //transition t4:l0,
    if (X3>=1 && rd == 4){
      incr_tracker_pos(rd);

      X3=X3-1;
      X1=X1+1;
      X6=X6+X5;
      X5=0;
    }

    //transition t5:l0,
    if (X2 >= 1 && rd == 5){
      incr_tracker_pos(rd);

      X2 = X2 -1;
      X1 = X1 +1;
      X4 = X4 + X6;
      X6 = 0;
    }
  }

  print_tracker(TRUE);
  return -1;
}


void efm1_dummy(int X1, int X2, int X3, int X4, int X5, int X6){}
int efm1(int X1, int X2, int X3, int X4, int X5, int X6){
  assert (X1>=1);
  //int X2=0;
  //int X3=0;
  //int X4=1;
  //int X5=0;
  //int X6=0;

  printf("X1 X2 X3 X4 X5 X6\n");


  set_tracker(5);
  
  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){

    assert (X4 +X5 +X6 -1  == 0);
    assert (-X2 -X3 +X5  >= 0);
    assert (-X4 -X5  + 1 >= 0);
    assert (X1 +X2 -1 >= 0);
    assert (2*X1 +2*X2 +X3 +X4 +X5 -3 >= 0);
    assert (X4  >= 0);
    assert (X3  >= 0);
    assert (X2  >= 0);
    printf("%d %d %d %d %d %d\n",X1, X2, X3, X4, X5, X6);
    efm1_dummy(X1, X2, X3, X4, X5, X6);

    int rd = randrange_i(1,5,INCLUDE);

    //transition t1:l0,
    if (X1 >= 1 && X4 >= 1 && rd == 1){
      incr_tracker_pos(rd);

      X1=X1-1;
      X4=X4-1;
      X2=X2+1;
      X5=X5+1;
    }

    //transition t2:l0,
    if (X2 >=1 && X6 >= 1 && rd == 2){
      incr_tracker_pos(rd);

      X2=X2 -1;
      X3=X3 +1;
    }

    //transition t3:l0,
    if (X4 >= 1 && X3 >= 1 && rd == 3){
      incr_tracker_pos(rd);

      X3=X3-1;
      X2=X2+1;
    }

    //transition t4:l0,
    if (X3>=1 && rd == 4){
      incr_tracker_pos(rd);

      X3=X3-1;
      X1=X1+1;
      X6=X6+X5;
      X5=0;
    }

    //transition t5:l0,
    if (X2 >= 1 && rd == 5){
      incr_tracker_pos(rd);

      X2 = X2 -1;
      X1 = X1 +1;
      X4 = X4 + X6;
      X6=0;
    }
  }

  print_tracker(TRUE);
  return -1;
}

void lifo_dummy(int I, int Sa, int Ea, int Ma, int Sb, int Eb, int Mb){}
int lifo(int I){
  //last in first served taken from FAST web page

  assert (I>=1);
  int Sa=0;
  int Ea=0;
  int Ma=0;
  int Sb=0;
  int Eb=0;
  int Mb=0;
  

  

  set_tracker(10);

  printf("I Sa Ea Ma Sb Eb Mb\n");
  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){

    assert (-Ea -Ma  + 1 >= 0);  //inv
    assert (-Eb -Mb  + 1 >= 0);  //inv
    assert (Mb  >= 0);
    assert (Eb  >= 0);
    assert (Ma  >= 0);
    assert (Ea  >= 0);

    printf("%d %d %d %d %d %d %d\n", I, Sa, Ea, Ma, Sb, Eb, Mb);
    lifo_dummy(I, Sa, Ea, Ma, Sb, Eb, Mb);

    int rd = randrange_i(1,10,INCLUDE);
    
    //transition t2:l0,
    if (Sb >= 1 && rd == 2){
      incr_tracker_pos(rd);

      Sb = Sb-1;
      Sa = Ea+Ma+1;
      Ea = 0;
      Ma = 0;
    }

    //transition t1: l0,
    if (I >= 1 && rd == 1){
      incr_tracker_pos(rd);

      I = I -1;
      Sa = Sa + Ea + Ma + 1;
      Ea = 0;
      Ma = 0;
    }

    //transition t3: l0,
    if (I>=1 && rd == 3){
      incr_tracker_pos(rd);

      I=I-1;
      Sb=Sb+Eb+Mb+1;
      Eb=0;
      Mb=0;
    }

    //transition t4: l0,
    if (Sa>=1 && rd == 4){
      incr_tracker_pos(rd);

      Sa=Sa-1;
      Sb=Sb+Eb+Mb+1;
      Eb=0;
      Mb=0;
    }

    //transition t5: l0,
    if (Sa>=1 && rd == 5){
      incr_tracker_pos(rd);

      I=I+Sa+Ea+Ma;
      Sa=0;
      Ea=1;
      Ma=0;
    }

    //transition t6: l0,
    if (Sb>=1 && rd == 6){
      incr_tracker_pos(rd);

      Sb=Sb-1;
      I=I+Sa+Ea+Ma;
      Sa=0;
      Ea=1;
      Ma=0;
    }

    //transition t7: l0,
    if (Sb>=1 && rd == 7){
      incr_tracker_pos(rd);

      I=I+Sb+Eb+Mb;
      Sb=0;
      Eb=1;
      Mb=0;
    }

    //transition t8: l0,
    if  (Sa>=1 && rd == 8){
      incr_tracker_pos(rd);

      Sa=Sa-1;
      I=I+Sb+Eb+Mb;
      Sb=0;
      Eb=1;
      Mb=0;
    }

    //transition t9: l0,
    if (Ea >=1 && rd == 9){
      incr_tracker_pos(rd);

      Ea = Ea -1;
      Ma = Ma +1;
    }

    //transition t10: l0,
    if (Eb >=1 && rd == 10){
      incr_tracker_pos(rd);

      Eb = Eb -1;
      Mb = Mb +1;
    }
  }

  print_tracker(TRUE);
  return -1;
}


void lifo_nat_dummy(int I, int Sa, int Ea, int Ma, int Sb, int Eb, int Mb){}
int lifo_nat(int I){

  //last in first served taken from FAST web page

  assert (I>=1);
  int Sa=0;
  int Ea=0;
  int Ma=0;
  int Sb=0;
  int Eb=0;
  int Mb=0;

  printf("I Sa Ea Ma Sb Eb Mb\n");


  set_tracker(10);
  
  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){

    assert (-Ea -Ma  + 1 >= 0);    //inv
    assert (-Eb -Mb  + 1 >= 0);    //inv
    assert (Mb  >= 0);
    assert (Eb  >= 0);
    assert (Sb  >= 0);
    assert (Ma  >= 0);
    assert (Ea  >= 0);
    assert (Sa  >= 0);
    assert (I  >= 0);
    assert (I +Sa +Ea +Ma +Sb +Eb +Mb -1 >= 0);   //inv
    printf ("%d %d %d %d %d %d %d\n",
            I, Sa, Ea, Ma, Sb, Eb, Mb);
    lifo_nat_dummy(I, Sa, Ea, Ma, Sb, Eb, Mb);


    int rd = randrange_i(1,10,INCLUDE);

    //transition t2:l0,
    if (Sb >= 1 && rd == 2){
      Sb  = Sb - 1;
      Sa = Ea + Ma +1;
      Ea = 0;
      Ma = 0;
    }

    //transition t1: l0,
    if (I >= 1 && rd == 1){
      I = I -1;
      Sa = Sa + Ea + Ma + 1;
      Ea = 0;
      Ma = 0;
    }

    //transition t3: l0,
    if (I>=1 && rd == 3){
      I=I-1;
      Sb=Sb+Eb+Mb+1;
      Eb=0;
      Mb=0;
    }

    //transition t4: l0,
    if (Sa>=1 && rd == 4){
      Sa=Sa-1;
      Sb=Sb+Eb+Mb+1;
      Eb=0;
      Mb=0;
    }

    //transition t5: l0,
    if (Sa>=1 && rd == 5){
      I=I+Sa+Ea+Ma;
      Sa=0;
      Ea=1;
      Ma=0;
    }

    //transition t6: l0,
    if (Sb>=1 && rd == 6){
      Sb=Sb-1;
      I=I+Sa+Ea+Ma;
      Sa=0;
      Ea=1;
      Ma=0;
    }

    //transition t7: l0,
    if (Sb>=1 && rd == 7){
      I=I+Sb+Eb+Mb;
      Sb=0;
      Eb=1;
      Mb=0;
    }

    //transition t8: l0,
    if (Sa>=1 && rd == 8){
      Sa=Sa-1;
      I=I+Sb+Eb+Mb;
      Sb=0;
      Eb=1;
      Mb=0;
    }

    //transition t9: l0,
    if (Ea >=1 && rd == 9){
      Ea = Ea -1;
      Ma = Ma +1;
    }

    //transition t10: l0,
    if (Eb >=1 && rd == 10){
      Eb = Eb -1;
      Mb = Mb +1;
    }


  }
  return -1;
}


void cars_midpt_dummy(int x1, int v1, int x2, int v2, int x3, int v3, int t){}
int cars_midpt(int v1, int v2, int v3){
  //"ex: inv.go('cars',5,5,5)"
  int x1 = 100;
  int x2 = 75;
  int x3 = -50;
  assert(v3 >= 0);
  assert(v1 <= 5);
  assert(v1 >= v3);
  assert(2* v2 - v1 - v3 == 0);
  int tt = 0;
  
  assert (v2 +5 >=0);
  assert (v2 <= 5);

  printf("x1 v1 x2 v2 x3 v3 tt\n");

  set_tracker(2);
  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){

    assert(-v1  + 5 >= 0);
    assert(-v1 +2*v2 -v3 +2*tt  >= 0);  //2*v2+2*tt >= v1 + v3
    //assert -x2 +5*tt  + 75 >= 0
    assert(v3  >= 0);
    //assert -v2  + 6 >= 0
    //assert v2  + 6 >= 0
    assert(x2 +5*tt -75 >= 0);
    assert(v1 -2*v2 +v3 +2*tt  >= 0); //v1+v3+2*tt>= 2*v2
    assert(v1 -v3  >= 0);

    printf("%d %d %d %d %d %d %d\n",x1, v1, x2, v2, x3, v3, tt);
    cars_midpt_dummy(x1, v1, x2, v2, x3, v3, tt);
    
    int r = randrange_i(1,2,INCLUDE);

    //Transition t0:l0,
    if(2* x2 - x1 - x3>=0 && r == 1){
      x1 = x1 + v1;
      x3 = x3 + v3;
      x2 = x2 +v2;
      v2 = v2 - 1;
      tt = tt + 1;
    }

    //Transition t1: l0,
    if (2*x2 -x1-x3 <=0 && r == 2){
      x1 = x1 + v1;
      x3 = x3 + v3;
      x2 = x2 + v2;
      v2 = v2 +1;
      tt = tt + 1;
    }
  }

  return -1;
}

      
void barber_dummy(int barber, int chair, int open1, 
                  int p1, int p2, int p3, int p4, int p5){}
int barber(int barber, int chair){

  //barber=0  
  //chair=0  
  //todo: skipping because easy invs


  int open1=0;
  int p1=0;
  int p2=0;
  int p3=0;
  int p4=0;
  int p5=0;


  set_tracker(12);

  printf("barber chair open1 p1 p2 p3 p4 p5\n");
  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){

    assert (-open1 +p5  >= 0);
    assert (-p1  + 1 >= 0);
    assert (-p2  + 1 >= 0);
    assert (-p3  + 1 >= 0);
    assert (-p4  + 1 >= 0);
    assert (-p5  + 3 >= 0);
    assert (p4  >= 0);
    assert (p3  >= 0);
    assert (p2  >= 0);
    assert (p1  >= 0);
    assert (open1  >= 0);
    assert (chair  >= 0);
    assert (barber  >= 0);

    printf("%d %d %d %d %d %d %d %d\n",
           barber, chair, open1, p1, p2, p3, p4, p5);
    barber_dummy(barber,  chair, open1, p1, p2, p3, p4, p5);


    int rd = randrange_i(1,12,INCLUDE);
    
    //transition t1: l0,
    if (p1 == 0 && barber >= 1 && rd == 1){
      barber = barber-1;
      chair = chair+1;
      p1 = 1;
    }

    //transition t3: l0,
    if (p2 == 0 && barber >= 1 && rd == 3){
      barber = barber-1;
      chair = chair+1;
      p2 = 1;
    }

    //transition t4: l0,
    if (p2 == 1  && open1 >=1 && rd == 4){
      open1 = open1 -1;
      p2 =0;
    }

    //transition t5: l0,
    if (p3 == 0 && barber >=1  && rd == 5){
      barber = barber- 1;
      chair = chair +1;
      p3 =1;
    }

    //transition t6: l0,
    if (p3 == 1 && open1 >=1 && rd==6){
      open1  = open1 - 1;
      p3 =0;
    }

    //transition t7: l0,
    if (p4 == 0 && barber >=1 && rd==7){
      barber= barber-1;
      chair = chair +1;
      p4 = p4+1;
    }

    //transition t8: l0,
    if (p4 == 1 && open1 >=1 && rd==8){
      open1 = open1 - 1;
      p4=p4 -1;
    }

    //transition t9:l0,
    if (p5 == 0 && rd==9){
      barber=barber+1;
      p5 = 1;
    }

    //transition t10:l0,
    if (p5 == 1 && chair >=1  && rd==10){
      chair = chair  -1;
      p5=2;
    }

    //transition t11:l0,
    if (p5 == 2 && rd==11){
      open1=open1 +1;
      p5=3;
    }

    //transition t12:l0,
    if (p5 == 3 && open1 == 0  && rd==12){
      p5=0;
    }

    //transition t2: l0,
    if (p1 == 1 && open1 >= 1 && rd==2){
      open1 = open1-1;
      p1 = 0;
    }

  }
  return -1;
}//barber


void swim_pool_dummy(int x1, int x2, int x3, int x4, 
                     int x5, int x6, int x7, int p, int q){}
int swim_pool(int p, int q){
  /*Taken from a Petri net paper. See [Fribourg+Olsen] or the 
    Sankaranarayanan+Sipma+Manna 2003 Petri net paper 
    tvn: see petri03.pdf in my Google Docs
  */

  //tvn: seems ok 

  int x1=0;
  int x2=0;
  int x3=0;
  int x4=0;
  int x5=0;
  int x6 = p;
  int x7 = q;
  assert (p >= 1);
  assert (q >= 1);

  printf("x1 x2 x3 x4 x5 x6 x7 p q\n");

  set_tracker(6);
  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){

    
    assert (x2 +x3 +x4 +x7 -q   == 0 );
    assert (x1 +x2 +x4 +x5 +x6 -p   == 0 );
    assert (x7  >= 0);
    assert (x6  >= 0);
    assert (x5  >= 0);
    assert (x4  >= 0);
    assert (x3  >= 0);
    assert (x2  >= 0);
    assert (x2 +x3 +x4 +x7 -1 >= 0);
    assert (x1  >= 0);
    assert (x1 +x2 +x4 +x5 +x6 -1 >= 0);

    printf("%d %d %d %d %d %d %d %d %d\n",
           x1, x2, x3, x4, x5, x6, x7, p, q);
    swim_pool_dummy(x1, x2, x3, x4, x5, x6, x7, p, q);


    int rd = randrange_i(1,6,INCLUDE);

    //Transition t1: l0,
    if (x6 >=1 && rd==1){
      incr_tracker_pos(rd);

      x1 = x1 +1;
      x6 = x6 -1;
    }

    //Transition t2: l0,
    if (x1 >=1 && x7 >=1 && rd == 2){
      incr_tracker_pos(rd);

      x1 = x1 - 1;
      x2 = x2 + 1;
      x7 = x7 - 1;
    }

    //Transition t3: l0,
    if (x2 >=1 && rd == 3){
      incr_tracker_pos(rd);

      x2 = x2 - 1;
      x3 = x3 + 1;
      x6 = x6 + 1;
    }

    //Transition t4: l0,
    if (x3>=1 && x6>=1 && rd==4){
      incr_tracker_pos(rd);

      x3 = x3 - 1;
      x4 = x4 + 1;
      x6 = x6 - 1;
    }

    //Transition t5: l0,
    if (x4>=1 && rd==5){
      incr_tracker_pos(rd);

      x4 = x4 - 1;
      x5 = x5 + 1;
      x7 = x7 + 1;
    }

    //Transition t6: l0,
    if (x5>=1 && rd==6){
      incr_tracker_pos(rd);

      x5 = x5 - 1;
      x6 = x6 + 1;
    }

  }
 
  print_tracker(TRUE);
  return -1;
}

void swim_pool1_dummy(int x1, int x2, int x3, int x4, 
                      int x5, int x6, int x7, int p, int q){}
int swim_pool1(int p, int q){
  //Inductive invariants from swim-pool.in added back to the transition system

  //tvn: seems ok

  int x1=0;
  int x2=0;
  int x3=0;
  int x4=0;
  int x5=0;
  int x6 = p;
  int x7 = q;
  assert(p >=1);
  assert(q >=1);

  printf("x1 x2 x3 x4 x5 x6 x7 p q\n");
  
  set_tracker(6);
  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){


    assert (x2 +x3 +x4 +x7 -q   == 0);
    assert (x1 +x2 +x4 +x5 +x6 -p   == 0);
    assert (x7  >= 0);
    assert (x6  >= 0);
    assert (x5  >= 0);
    assert (x4  >= 0);
    assert (x3  >= 0);
    assert (x2  >= 0);
    assert (x2 +x3 +x4 +x7 -1 >= 0);
    assert (x1  >= 0);
    assert (x1 +x2 +x4 +x6 +x7 -1 >= 0);
    assert (x1 +x2 +x4 +x5 +x6 -1 >= 0);

    printf("%d %d %d %d %d %d %d %d %d\n",
           x1, x2, x3, x4, x5, x6, x7, p, q);
    swim_pool1_dummy(x1, x2, x3, x4, x5, x6, x7, p, q);


    int rd = randrange_i(1,6,INCLUDE);

    //Transition t1: l0,
    if (x6 >=1 && rd == 1){
      incr_tracker_pos(rd);

      x1 = x1 + 1;
      x6 = x6 - 1;
    }


    //Transition t2: l0,
    if (x1 >=1 && x7 >=1 && rd == 2){
      incr_tracker_pos(rd);

      x1=x1-1;
      x2=x2+1;
      x7=x7-1;
    }

    //Transition t3: l0,
    if (x2 >=1 && rd == 3){
      incr_tracker_pos(rd);

      x2 = x2 - 1;
      x3 = x3 + 1;
      x6 = x6 + 1;
    }



    //Transition t4: l0,
    if (x3>=1 && x6>=1 && rd == 4){
      incr_tracker_pos(rd);

      x3 = x3 - 1;
      x4 = x4 + 1;
      x6 = x6 - 1;
    }


    //Transition t5: l0,
    if (x4>=1 && rd == 5){
      incr_tracker_pos(rd);

      x4 = x4 - 1;
      x5 = x5 + 1;
      x7 = x7 + 1;
    }

    //Transition t6: l0,
    if (x5>=1 && rd == 6){
      incr_tracker_pos(rd);

      x5 = x5 - 1;
      x6 = x6 + 1;
    }


  }

  print_tracker(TRUE);
  return -1;
}


//STING High Dimension (Scheduler)
int schedule2p(int seed){
  srand(seed);

  int c1,c2,k1,k2,x1,x2,t;

  int tval = 10;
  int loc = randrange_i(1,2,INCLUDE);
  
  //location l1
  if (loc == 1){
    c1=0;
    c2 = randrange_i(10,10+tval,INCLUDE);
    k1=1;
    k2=0;
    x1=0;
    x2=0;
    t=c2;
  }
  else{
    //location l2
    c1=randrange_i(20,20+tval,INCLUDE);
    c2=0;
    k1=0;
    k2=1;
    x1=0;
    x2=0;
    t=c1;
  }

  set_tracker(12);

  printf("c1 c2 k1 k2 x1 x2 t\n");
  while(get_n_incr_loop_ctr_tracker() < 1000){

    //invs we want to discover
    if (loc==1){
      assert(1*k2   == 0 );
      assert(1*x2   == 0 );
      assert(-1*c1 -1*c2 +1*x1 -10*k1 +1*t  + 10 >= 0);
      assert(-1*c1 -10*k1 +1*t  >= 0);
      assert(-1*c2 +1*t  >= 0);
      assert(-1*x1  + 4 >= 0);
      assert(-1*x1 +1*t -10 >= 0);
      assert(1*k1 -1 >= 0);
      assert(1*x1  >= 0);
      assert(1*c2  >= 0);
      assert(1*c1  >= 0);
      sprintf(buf,"loc1: %d %d %d %d %d %d %d\n",c1,c2,k1,k2,x1,x2,t);
      hash_print(buf);
    }
    else{
      assert(1*k2 -1  == 0);
      assert(1*c2 -1*x2  == 0);
      assert(-3*c1 -5*c2 -5*x1 +20*k1 +8*t -100 >= 0);
      assert(-1*c1 -10*k1 +1*t  >= 0);
      assert(-1*c2  + 8 >= 0);
      assert(-1*c2 +1*t -20 >= 0);
      assert(-1*x1  + 4 >= 0);
      assert(1*k1  >= 0);
      assert(1*x1  >= 0);
      assert(1*c2  >= 0);
      assert(1*c1  >= 0);
      sprintf(buf,"loc2: %d %d %d %d %d %d %d\n",c1,c2,k1,k2,x1,x2,t);
      hash_print(buf);
    }
    
    int rd = randrange_i(1,12,INCLUDE);

    //transition t2: l1,
    if(loc==1 && rd == 2 && x1 - 4 <= 0){
      incr_tracker_pos(rd);
      
      int old_x1 = x1;
      x1 = randrange_i(old_x1,4,INCLUDE);
      int x1diff = x1 - old_x1;

      int old_t = t;
      //x1diff = t-old_t  =>  t = x1diff + old_t
      t = x1diff + old_t;
      //t = randrange_i(t,t+tval,INCLUDE);
      int tdiff = t - old_t;
      
      c1 = tdiff + c1;  //'c1-c1 - 't+t = 0
      c2 = tdiff + c2;
    }

    //transition t3: l2,
    if(loc==2 && rd == 3 && x2 -8 <=0){
      //printf("3\n");
      
      incr_tracker_pos(rd);

       int old_x2 = x2;
      x2 =randrange_i(old_x2,8,INCLUDE);
      int x2diff = x2 - old_x2;

      int old_t = t;
      t = x2diff + old_t ;
      int tdiff = t - old_t;

      c1 = tdiff + c1;
      c2 = tdiff + c2;
    }


    //transition t8: l1,
    if(loc == 1 && rd == 8 && c1 >= 10){
      //printf("8\n");
      incr_tracker_pos(rd);

      k1 = k1+1;
      c1=0;
    }



    //transition t9:l1,
    if(loc == 1 && rd == 9 && x1 == 4 && k1 - 2 >= 0){
      //printf("9\n");
      incr_tracker_pos(rd);

      k1 = k1- 1;
      x1=0;
    }


    //transition t10: l2,
    if(loc == 2 && rd == 10 && c1 >= 10){
      //printf("10\n");
      incr_tracker_pos(rd);
      k1 = k1 + 1;
      c1 = 0;
    }


    //transition t11:l1,l2,
    if(rd == 11 && 
       loc==1 && c2 >= 20){
      //printf("11\n");
      incr_tracker_pos(rd);

      c2=0;
      k2=1;

      loc=2;
    }

    //transition t12: l2,l1,
    if(loc==2 && rd == 12 && x2 - 8==0 && k2 - 1==0 && k1 - 1 >=0){
      //printf("12\n");
      incr_tracker_pos(rd);

      k2 = k2 - 1;
      x2=0;

      loc=1;
    }
  }//while


  print_tracker(TRUE);
  return -1;
}


int schedule3p(int seed){
  srand(seed);
  int c1, c2, c3, x1, x2, x3, k1, k2, k3, t;
  int tval = 10;
  int loc = randrange_i(1,3,INCLUDE);

  //#Location l1 where process 1 is executed
  //location l1
  if (loc==1){
    c1=0;
    c2=randrange_i(5,5+tval,INCLUDE);
    c3=randrange_i(5,5+tval,INCLUDE);
    
    k1=1;
    k2=0;
    k3=0;
    
    x1=0;
    x2=0;
    x3=0;
    t=c2;
    t=c3;
  }

  //Process 2 is executed in location l2
  //location l2
  if(loc==2){
    c1=randrange_i(10,10+tval,INCLUDE);
    c2=0;
    c3=c1;//becase t=c1=c3;

    k1=0;
    k2=1;
    k3=0;

    x1=0;
    x2=0;
    x3=0;

    t=c1;
    //t-c3=0;
  }
    //Process 3 in location l3
    //Location l3
  if (loc==3){
    c1=randrange_i(20,20+tval,INCLUDE);
    c2=c1;
    c3=0;
    k1=0;
    k2=0;
    k3=1;

    x1=0;
    x2=0;
    x3=0;

    t=c1;
    //t-c2=0;
  }

  set_tracker(13);

  printf("c1, c2, c3, x1, x2, x3, k1, k2, k3, t\n");
  while(get_n_incr_loop_ctr_tracker() < 1000){
    //invs we want to discover


    //Location:l1
    if (loc == 1){
      assert(1*k3   == 0 );
      assert(1*k2   == 0); 
      assert(1*x3   == 0 );
      assert(-20*c1 -20*c2 -27*c3 +20*x1 +20*x2 -100*k1 +47*t  + 100 >= 0);
      assert(-1*c1 -1*c2 -1*c3 +1*x1 +1*x2 -5*k1 +2*t  + 12 >= 0);
      assert(-1*c1 -5*k1 +1*t  >= 0);
      assert(-1*c2 +1*t  >= 0);
      assert(-1*c3 +1*t  >= 0);
      assert(-1*x1 -1*x2 +1*t -5 >= 0);
      assert(-1*x1  + 2 >= 0);
      assert(-1*x2  + 4 >= 0);
      assert(1*k1 -1 >= 0);
      assert(1*x2  >= 0);
      assert(1*x1  >= 0);
      assert(1*c3  >= 0);
      assert(1*c2  >= 0);
      assert(1*c1  >= 0);
      sprintf(buf, "loc1: %d, %d, %d, %d, %d, %d, %d, %d, %d, %d\n",
              c1, c2, c3, x1, x2, x3, k1, k2, k3, t);
      hash_print(buf);
    }
    if (loc == 2){
      assert(1*k3   == 0 );
      assert(1*x3   == 0 );
      assert(-13*c1 -9*c2 -5*x1 -5*x2 +10*k1 +27*t -140 >= 0);
      assert(-5*c1 -5*c2 -7*c3 +5*x1 +5*x2 -25*k1 +12*t  >= 0);
      assert(-3*c1 -4*c2 -5*x1 -5*x2 +10*k1 +12*t -90 >= 0);
      assert(-3*c1 -5*x1 -5*x2 +10*k1 +8*t -50 >= 0);
      assert(-1*c1 -1*c2 -1*c3 +1*x1 +1*x2 -5*k1 +2*t  + 8 >= 0);
      assert(-1*c1 -5*k1 +1*t  >= 0);
      assert(-4*c2 -5*x1 -5*x2 +9*t -65 >= 0);
      assert(-4*c2 -5*x1 -5*x2 +10*k1 +9*t -75 >= 0);
      assert(-2*c2 -1*c3 +3*t -20 >= 0);
      assert(-1*c2 +1*t  >= 0);
      assert(-1*c3 +1*t  >= 0);
      assert(-1*x1 -1*x2 +1*t -5 >= 0);
      assert(-1*x1 -1*x2 +2*k1 +1*t -7 >= 0);
      assert(-1*x1  + 2 >= 0);
      assert(-1*x2  + 4 >= 0);
      assert(1*k2 -1 >= 0);
      assert(1*k1  >= 0);
      assert(1*x2  >= 0);
      assert(1*x1  >= 0);
      assert(1*c3  >= 0);
      assert(1*c2  >= 0);
      assert(1*c1  >= 0);
      sprintf(buf, "loc2: %d, %d, %d, %d, %d, %d, %d, %d, %d, %d\n",
              c1, c2, c3, x1, x2, x3, k1, k2, k3, t);
      hash_print(buf);
    }
    if (loc == 3){
      assert(1*k3 -1  == 0 );
        assert(1*c3 -1*x3   == 0 );
        assert(-13*c1 -5*c2 -5*c3 -5*x1 -5*x2 +10*k1 +23*t -100 >= 0);
        assert(-1*c1 -5*k1 +1*t  >= 0);
        assert(-1*c2 +1*t  >= 0);
        assert(-1*c3  + 8 >= 0);
        assert(-1*c3 +1*t -20 >= 0);
        assert(-1*x1  + 2 >= 0);
        assert(-1*x2  + 4 >= 0);
        assert(1*k2  >= 0);
        assert(1*k1  >= 0);
        assert(1*x2  >= 0);
        assert(1*x1  >= 0);
        assert(1*c3  >= 0);
        assert(1*c2  >= 0);
        assert(1*c1  >= 0);

      sprintf(buf, "loc3: %d, %d, %d, %d, %d, %d, %d, %d, %d, %d\n",
              c1, c2, c3, x1, x2, x3, k1, k2, k3, t);
      hash_print(buf);
      }
    //Time evolution in location l1
    //transition tl1evolve: l1,
    
    int rd = randrange_i(1,13,INCLUDE);
    if(	rd == 1 && 
        loc==1 && x2==0 &&  x3==0 && x1 -2 <=0){
      incr_tracker_pos(rd);

      int old_x1 = x1;
      x1 = randrange_i(old_x1, 2, INCLUDE);
      int x1diff = x1 - old_x1;
      
      int old_t = t;
      t = x1diff + old_t;
      int tdiff = t - old_t;

      c1 = tdiff + c1;
      c2 = tdiff + c2;
      c3 = tdiff + c3;
    }

    //Time evolution in location l2

    //transition tl2evolve: l2,
    if (rd == 2 && 
        loc == 2 &&  x2 -4 <=0){
      incr_tracker_pos(rd);

      int old_x2 = x2;
      x2 = randrange_i(old_x2,4,INCLUDE);
      int x2diff = x2-old_x2;

      if (x1 -2 <=0 && x3==0){
        int old_t = t;
        t = x2diff + old_t;
        int tdiff = t - old_t;
        c1 = tdiff + c1;
        c2 = tdiff + c2;
        c3 = tdiff + c3;
      }
    }

    //Time evolution in location l3

    //transition tl3evolve: l3,
    if ( rd == 3 && 
         loc == 3 && x3 -8 <= 0){
      incr_tracker_pos(rd);

      int old_x3 = x3;
      x3 = randrange_i(old_x3, 8, INCLUDE);
      int x3diff = x3 - old_x3;
      
      if (x1 <= 2 && x2 <= 4){
        int old_t = t;
        t = x3diff + old_t;
        int tdiff = t - old_t;
        c1 = tdiff + c1;
        c2 = tdiff + c2;
        c3 = tdiff + c3;
      }
    }

    //Extra process 1 arrives in location l1
    //transition t8: l1,
    if (rd == 4 && 
        loc == 1 && c1>=5){
      incr_tracker_pos(rd);

      k1 = k1 + 1;
      c1=0;
    }

    //Process completes execution in location l1
    //transition t9:l1,
    if (rd == 5 &&
        loc == 1 && x1 == 2 && k1 - 2 >=0){
      incr_tracker_pos(rd);
      k1 = k1 - 1;
      x1 = 0;
    }

    //Process 1 arrives  in location l2
    //transition t10: l2,
    if (rd == 6 &&
        loc == 2 && c1>=5){
      incr_tracker_pos(rd);

      k1 = k1 + 1;
      c1=0;
    }

    // Process 1 arrives in location l3
    //transition t13: l3,
    if (rd == 13 && 
        loc == 3 && c1>=5){
      incr_tracker_pos(rd);

      k1 = k1 + 1;
      c1=0;
    }

    //Process 2 arrives in location l1
    // Make a switch to location l2
    //transition t11:l1,l2,
    if (rd == 7 && 
        loc == 1 && c2 >=10){
      incr_tracker_pos(rd);

      c2=0;
      loc = 2;
      k2 = 1;
    }

    //Process 2 arrives in location l3

    //transition t17: l3,
    if (rd == 8 && 
        loc == 3 && c2 >=10){
      incr_tracker_pos(rd);

      c2=0;
      k2=k2+1;
    }


    //Process 3 arrives in location l1
    // Make a switch to location l3

    //transition t14: l1,l3,
    if (rd == 9 && 
        loc == 1 && c3 >= 20){
      incr_tracker_pos(rd);

      c3=0;
      k3=1;
      loc = 3;
    }

    //Process 3 arrives in location l2
    //Make a switch to location l3

    //transition t18: l2,l3,
    else if (rd == 10 && 
        loc == 2 &&  c3 >= 20){
      incr_tracker_pos(rd);
       
      c3=0;
      k3 = 1;
      loc = 3;
    }

    //Process 2 completes in location l2
    // Extra process 1 exists
	    
    //transition t12: l2,l1,
    if(rd == 11 && 
       loc == 2 && 	x2 - 4 == 0 && k2 - 1== 0 && k1 - 1 >= 0){
       incr_tracker_pos(rd);

      k2 = k2 - 1;
      x2 = 0;
      loc = 1;
    }

    //Process 3 completes from l3 and extra process 2 exists
    //transition t15:l3,l2,
    if (rd == 12 && 
        loc == 3 && x3 - 8 == 0 && k3 - 1 == 0 && k2 -1 >= 0){
      incr_tracker_pos(rd);

      k3 = k3 - 1;
      x3 = 0;
      loc = 2;
    }

    //Process 3 completes and extra process 1 exists

    //transition t16:l3,l1,
    if (rd == 13 && 
        loc == 3 && x3 - 8 == 0 && k3 - 1 == 0 && k2 == 0 && k1 - 1 >= 0){
        
      incr_tracker_pos(rd);

      k3 = k3 - 1;
      x3=0;
      loc = 1;
    }
  }//while

  print_tracker(TRUE);
  return -1;
}


int schedule4p(int seed){
  srand(seed);

  int c1, c2, c3, c4, x1, x2, x3, x4, k1, k2, k3, k4, t;
  int tval = 10;
  int loc = randrange_i(1,4,INCLUDE);

  //#Location l1 where process 1 is executed
  //location l1
  if (loc==1){
    c1=0;
    c2>=5;
    c3>=5;
    c4>=5;

    k1=1;
    k2=0;
    k3=0;
    k4=0;

    x1=0;
    x2=0;
    x3=0;
    x4=0;

    t-c2=0;
    t-c3=0;
    t-c4=0;
  }

  //Process 2 is executed in location l2
  //location l2
  if (loc==2){
    c1>=10;
    c2=0;
    c3>=10;
    c4>=10;
      
    k1=0;
    k2=1;
    k3=0;
    k4=0;

    x1=0;
    x2=0;
    x3=0;
    x4=0;
    
    t-c1=0;
    t-c3=0;
    t-c4=0;
    
    //Process 3 in location l3
    //Location l3
    if(loc==3){
      c1>=20;
      c2>=20;
      c3=0;
      c4>=20;

      k1=0;
      k2=0;
      k3=1
        k4=0;
      
      x1=0;
      x2=0;
      x3=0;
      x4=0;
      
      t-c1=0;
      t-c2=0;
      t-c4=0;
    }

    //Process 4 in location l4
    //location l4
    if (loc==4){
      c1 >= 40;
      c2 >= 40;
      c3 >=40;
      c4=0;
      
      k1=0;
      k2=0;
      k3=0;
      k4=1
        
        x1=0;
      x2=0;
      x3=0;
      x4=0;
      
      t-c1=0;
      t-c2=0;
      t-c3=0;
    }


    set_tracker(SETME);

    printf("c1 c2 c3 c4 x1 x2 x3 x4 k1 k2 k3 k4 t\n");
    while(get_n_incr_loop_ctr_tracker() < 1000){
      //invs we want to discover

      if (loc == 1){
        assert(1*k4   == 0); 
        assert(1*k3   == 0); 
        assert(1*k2   == 0); 
        assert(-40*c1 -40*c2 -54*c3 -47*c4 +40*x1 +40*x2 +40*x3 +
               40*x4 -200*k1 +141*t  + 200 >= 0);
        assert(-1*c1 -1*c2 -1*c3 -1*c4 +1*x1 +1*x2 +1*x3 +
               1*x4 -5*k1 +3*t  + 12 >= 0);
        assert(-1*c1 -5*k1 +1*t  >= 0);
        assert(-1*c2 +1*t  >= 0);
        assert(-1*c3 +1*t  >= 0);
        assert(-1*c4 +1*t  >= 0);
        assert(-1*x1 -1*x2 -1*x3 -1*x4 +1*t -5 >= 0);
        assert(-1*x1  + 2 >= 0);
        assert(-1*x2  + 4 >= 0);
        assert(-1*x3  + 8 >= 0);
        assert(-1*x4  + 4 >= 0);
        assert(1*k1 -1 >= 0);
        assert(1*x4  >= 0);
        assert(1*x3  >= 0);
        assert(1*x2  >= 0);
        assert(1*x1  >= 0);
        assert(4*c4 +5*x4 -20 >= 0);
        assert(1*c3  >= 0);
        assert(1*c2  >= 0);
        assert(1*c1  >= 0);
        
        sprintf(buf, "loc1: %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
                c1, c2, c3, c4, x1, x2, x3, x4, k1, k2, k3, k4, t);
        hash_print(buf);
      }
      if (loc == 2){
        
        assert(1*k4   == 0); 
        assert(1*k3   == 0); 
        assert(-33*c1 -19*c2 -5*c3 -1*c4 -5*x1 -5*x2 -5*x3 
               -5*x4 +10*k1 +63*t -240 >= 0);
        assert(-33*c1 -15*c2 -5*c3 -5*x1 -5*x2 -5*x3 
               -5*x4 +10*k1 +58*t -200 >= 0);
        assert(-13*c1 -9*c2 -1*c4 -5*x1 -5*x2 -5*x3 
               -5*x4 +10*k1 +28*t -140 >= 0);
        assert(-13*c1 -5*c2 -5*x1 -5*x2 -5*x3 -5*x4 +10*k1 +23*t -100 >= 0);
        assert(-5*c1 -5*c2 -7*c3 -6*c4 +5*x1 +5*x2 +5*x3 +5*x4 -25*k1 +18*t  >= 0);
        assert(-3*c1 -4*c2 -1*c4 -5*x1 -5*x2 -5*x3 -5*x4 +10*k1 +13*t -90 >= 0);
        assert(-3*c1 -5*x1 -5*x2 -5*x3 -5*x4 +10*k1 +8*t -50 >= 0);
        assert(-1*c1 -1*c2 -1*c3 -1*c4 +1*x1 +1*x2 +1*x3 +1*x4 -5*k1 +3*t  + 8 >= 0);
        assert(-1*c1 -5*k1 +1*t  >= 0);
        assert(-4*c2 -2*c3 -1*c4 +7*t -40 >= 0);
        assert(-4*c2 -1*c4 -5*x1 -5*x2 -5*x3 -5*x4 +10*t -65 >= 0);
        assert(-4*c2 -1*c4 -5*x1 -5*x2 -5*x3 -5*x4 +10*k1 +10*t -75 >= 0);
        assert(-1*c2 +1*t  >= 0);
        assert(-1*c3 +1*t  >= 0);
        assert(-1*c4 +1*t  >= 0);
        assert(-1*x1 -1*x2 -1*x3 -1*x4 +1*t -5 >= 0);
        assert(-1*x1 -1*x2 -1*x3 -1*x4 +2*k1 +1*t -7 >= 0);
        assert(-1*x1  + 2 >= 0);
        assert(-1*x2  + 4 >= 0);
        assert(-1*x3  + 8 >= 0);
        assert(-1*x4  + 4 >= 0);
        assert(1*k2 -1 >= 0);
        assert(1*k1  >= 0);
        assert(1*x4  >= 0);
        assert(1*x3  >= 0);
        assert(1*x2  >= 0);
        assert(1*x1  >= 0);
        assert(4*c4 +5*x4 -20 >= 0);
        assert(1*c3  >= 0);
        assert(1*c2  >= 0);
        assert(1*c1  >= 0);
        sprintf(buf, "loc2: %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
                c1, c2, c3, c4, x1, x2, x3, x4, k1, k2, k3, k4, t);
        hash_print(buf);
      }

      if (loc == 3){

        assert(1*k4   == 0); 
        assert(-33*c1 -15*c2 -5*c3 -5*x1 -5*x2 -5*x3 -5*x4 +10*k1 +58*t -200 >= 0);
        assert(-13*c1 -5*c2 -5*x1 -5*x2 -5*x3 -5*x4 +10*k1 +23*t -100 >= 0);
        assert(-3*c1 -5*x1 -5*x2 -5*x3 -5*x4 +10*k1 +8*t -50 >= 0);
        assert(-1*c1 -1*c2 -1*c3 -1*c4 +1*x1 +1*x2 +1*x3 +1*x4 -5*k1 +3*t  >= 0);
        assert(-1*c1 -5*k1 +1*t  >= 0);
        assert(-1*c2 +1*t  >= 0);
        assert(-2*c3 -1*c4 +3*t -40 >= 0);
        assert(-1*c3 +1*t  >= 0);
        assert(-1*c4 +1*t  >= 0);
        assert(-1*x1 -1*x2 -1*x3 -1*x4 +1*t -5 >= 0);
        assert(-1*x1 -1*x2 -1*x3 -1*x4 +2*k1 +1*t -7 >= 0);
        assert(-1*x1  + 2 >= 0);
        assert(-1*x2  + 4 >= 0);
        assert(-1*x3  + 8 >= 0);
        assert(-1*x4  + 4 >= 0);
        assert(1*k3 -1 >= 0);
        assert(1*k2  >= 0);
        assert(1*k1  >= 0);
        assert(1*x4  >= 0);
        assert(1*x3  >= 0);
        assert(1*x2  >= 0);
        assert(1*x1  >= 0);
        assert(4*c4 +5*x4 -20 >= 0);
        assert(1*c3  >= 0);
        assert(1*c2  >= 0);
        assert(1*c1  >= 0);

        sprintf(buf, "loc3: %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
                c1, c2, c3, c4, x1, x2, x3, x4, k1, k2, k3, k4, t);
        hash_print(buf);
      }

      if (loc == 4){


        assert(1*k4 -1  == 0); 
        assert(-33*c1 -15*c2 -5*c3 -5*x1 -5*x2 -5*x3 -5*x4 +10*k1 +58*t -200 >= 0);
        assert(-1*c1 -5*k1 +1*t  >= 0);
        assert(-1*c2 +1*t  >= 0);
        assert(-1*c3 +1*t  >= 0);
        assert(-1*c4 +1*t -40 >= 0);
        assert(-1*c4 +1*x4  >= 0);
        assert(-1*x1  + 2 >= 0);
        assert(-1*x2  + 4 >= 0);
        assert(-1*x3  + 8 >= 0);
        assert(-1*x4  + 4 >= 0);
        assert(1*k3  >= 0);
        assert(1*k2  >= 0);
        assert(1*k1  >= 0);
        assert(1*x3  >= 0);
        assert(1*x2  >= 0);
        assert(1*x1  >= 0);
        assert(1*c4  >= 0);
        assert(1*c3  >= 0);
        assert(1*c2  >= 0);
        assert(1*c1  >= 0);


        sprintf(buf, "loc4: %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
                c1, c2, c3, c4, x1, x2, x3, x4, k1, k2, k3, k4, t);
        hash_print(buf);
      }
      
//Time evolution in location l1
//transition tl1evolve: l1,

         x1 -2 <=0;
	_x1-2 <=0;

	x2=0;
	x3=0;
	x4=0;
	
	_t-t >=0;
	
	_c1-c1 -_t+t =0;
	_c2-c2-_t+t=0;
	_c3-c3-_t+t=0;
	_c4-c4-_t+t=0;

	_x1-x1-_t+t=0;
	_x2-x2=0;
	_x3-x3=0;
	_x4-x4=0;

	_k1-k1=0;
	_k2-k2=0;
	_k3-k3=0;
	_k4-k4=0;

//Time evolution in location l2

//transition tl2evolve: l2,
	 x2 -4 <=0;
	 _x2-4 <=0;

	 x1 -2 <=0;
	 x3=0;
	 x4=0;
	 
	 _t-t >=0;

	_c1-c1 -_t+t =0;
	_c2-c2-_t+t=0;
	_c3-c3-_t+t=0;
	_c4-c4-_t+t=0;

	_x2-x2-_t+t=0;
	_x1-x1=0;
	_x3-x3=0;
	_x4-x4=0;

	_k1-k1=0;
	_k2-k2=0;
	_k3-k3=0;
	_k4-k4=0;

//Time evolution in location l3

//transition tl3evolve: l3,
	 x3 -8 <=0;
	_x3-8<=0;
	   
	x1<=2
	x2<=4
	x4=0;

	_t-t>=0;
	   
	_c1-c1-_t+t=0;
	_c2-c2-_t+t=0;
	_c3-c3-_t+t=0;
	_c4-c4-_t+t=0;

	_x1-x1=0;
	_x2-x2=0;
	_x3-x3-_t+t=0;
	_x4-x4=0;

	_k1-k1=0;
	_k2-k2=0;
	_k3-k3=0;
	_k4-k4=0;

//Time evolution in location l4

//transition tl4evolve: l4,
	   x4-4 <=0;
	   _x4-4<=0;
	   
	   x1 <= 2
	   x2 <= 4
	   x3 <= 8
	   
	   _t-t>=0;
	   
	      
	_c1-c1-_t+t=0;
	_c2-c2-_t+t=0;
	_c3-c3-_t+t=0;
	_c4-c4-_t+t=0;

	  _x1-x1=0;
	  _x2-x2=0;
	  _x3-x3=0;
	  _x4-x4-_t+t=0;

	  _k1-k1=0;
	  _k2-k2=0;
	  _k3-k3=0;
	  _k4-k4=0;

	   

//Extra process 1 arrives in location l1

//transition t8: l1,
	   c1>=5

	   _k1-k1-1=0;
	   _k2-k2=0;	   
	   _k3-k3=0;
	   _k4-k4=0;
	   

	   _c1=0;
	   _c2-c2=0;
	   _c3-c3=0;
	   _c4-c4=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
	   _x4-x4=0;

	   _t-t=0;

//Process completes execution in location l1

//transition t9:l1,
	   x1=2
	   k1 -2 >=0;

	   _k1-k1+1=0;
	   _k2-k2=0;
	   _k3-k3=0;
	   _k4-k4=0;
	   
	   _x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
	   _x4-x4=0;

	   _c1-c1=0;
	   _c2-c2=0;
	   _c3-c3=0;
	   _c4-c4=0;

	   _t-t=0;


//Process 1 arrives  in location l2

//transition t10: l2,

	   c1>=5

	   _k1-k1-1=0;
	   _k2-k2=0;	   
	   _k3-k3=0;
	   _k4-k4=0;

	   _c1=0;
	   _c2-c2=0;
	   _c3-c3=0;
	   _c4-c4=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
 	   _x4-x4=0;

	   _t-t=0;

// Process 1 arrives in location l3
//transition t13: l3,

	   c1>=5

	   _k1-k1-1=0;
	   _k2-k2=0;	   
	   _k3-k3=0;
	   _k4-k4=0;

	   _c1=0;
	   _c2-c2=0;
	   _c3-c3=0;
	   _c4-c4=0;

	   _x1-x1=0;
	   _x2-x2=0;
	    _x3-x3=0;
            _x4-x4=0;

	   _t-t=0;

//Process 1 arrives in location l4

//transition t19: l4,
	   
	   c1>=5

	   _k1-k1-1=0;
	   _k2-k2=0;	   
	   _k3-k3=0;
	   _k4-k4=0;

	   _c1=0;
	   _c2-c2=0;
	   _c3-c3=0;
	   _c4-c4=0;

	   _x1-x1=0;
	   _x2-x2=0;
	    _x3-x3=0;
            _x4-x4=0;

	   _t-t=0;


//Process 2 arrives in location l1
// Make a switch to location l2

//transition t11:l1,l2,

	   c2 >=10

	   _c2=0;
	   _c1-c1=0;
	   _c3-c3=0;
	   _c4-c4=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
	   _x4-x4=0;

	   _k1-k1=0;
	   _k2-1=0;
	   _k3-k3=0;
	   _k4-k4=0;

	   _t-t=0;


//Process 2 arrives in location l3

//transition t17: l3,

	   c2 >=10

	   _c2=0;
	   _c1-c1=0;
	    _c3-c3=0;
            _c4-c4=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
	   _x4-x4=0;

	   _k1-k1=0;
	   _k2-k2-1=0;
	   _k3-k3=0;
           _k4-k4=0;

	   _t-t=0;

//Process 2 arrives in location l4

//transition t20: l4,

	   c2 >=10

	   _c2=0;
	   _c1-c1=0;
	   _c3-c3=0;
	    _c4-c4=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
           _x4-x4=0;

	   _k1-k1=0;
	   _k2-k2-1=0;
	   _k3-k3=0;
           _k4-k4=0;

	   _t-t=0;


//Process 3 arrives in location l1
// Make a switch to location l3

//transition t14: l1,l3,
       c3 >= 20
       
       _c3=0;
       _c2-c2=0;
       _c1-c1=0;
       _c4-c4=0;

       _x1-x1=0;
       _x2-x2=0;
       _x3-x3=0;
       _x4-x4=0;
      
       _k1-k1=0;
       _k3-1=0;
       _k2-k2=0;
       _k4-k4=0;

       _t-t=0;

//Process 3 arrives in location l2
//Make a switch to location l3

 //transition t18: l2,l3,
       c3 >= 20
       
       _c3=0;
       _c2-c2=0;
       _c1-c1=0;
       _c4-c4=0;

       _x1-x1=0;
       _x2-x2=0;
       _x3-x3=0;
       _x4-x4=0;
       
       _k1-k1=0;
       _k3-1=0;
       _k2-k2=0;
       _k4-k4=0;

       _t-t=0;

//Process 3 arrives in location l4

 //transition t21: l4,
       c3 >= 20
       
       _c3=0;
       _c2-c2=0;
       _c1-c1=0;
       _c4-c4=0;

       _x1-x1=0;
       _x2-x2=0;
       _x3-x3=0;
       _x4-x4=0;
       
       _k1-k1=0;
       _k3-k3-1=0;
       _k2-k2=0;
       _k4-k4=0;

       _t-t=0;




//Process 2 completes in location l2
// Extra process 1 exists
	    
//transition t12: l2,l1,
	   x2-4=0;
	   k2-1=0;
	   k1 -1 >=0;
	   
	   _k2-k2+1=0;
	   _k1-k1=0;
	   _k3-k3=0;
	   _k4-k4=0;

	   _x2=0;
	   _x1-x1=0;
	   _x3-x3=0;
           _x4-x4=0;

	   _t-t=0;

	   _c1-c1=0;
	   _c2-c2=0;   
	   _c3-c3=0;
           _c4-c4=0;

//Process 3 completes from l3 and extra process 2 exists

//transition t15:l3,l2,
	   x3-8=0;
	   k3-1=0;
	   k2 -1 >=0;

	   _k3-k3+1=0;
	   _k2-k2=0;
	   _k1-k1=0;
           _k4-k4=0;

	   _x3=0;
	   _x2-x2=0;
	   _x1-x1=0;
           _x4-x4=0;

	   _t-t=0;
	   
	   _c1-c1=0;
	   _c2-c2=0;   
	   _c3-c3=0;
           _c4-c4=0;

//Process 3 completes and extra process 1 exists

//transition t16:l3,l1,
	   x3-8=0;
	   k3-1=0;
	   k2 =0;
	   k1 -1 >=0;

	   _k3-k3+1=0;
	   _k2-k2=0;
	   _k1-k1=0;
           _k4-k4=0;

	   _x3=0;
	   _x2-x2=0;
	   _x1-x1=0;
           _x4-x4=0;

	   _t-t=0;
	   
	   _c1-c1=0;
	   _c2-c2=0;   
	   _c3-c3=0;
	   _c4-c4=0;

//Process 4 arrives in location l1
// Switch to location l4

//transition t23: l1,l4,
	   c4 >= 40
	   _c4=0;
	   
	   _c1-c1=0;
	   _c2-c2=0;
	   _c3-c3=0;

	   _k4=1
	   
	   _k1-k1=0;
	   _k2-k2=0;
	   _k3-k3=0;
	   
	   _t-t=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
	   _x4-x4=0;
//Process 4 arrives in location l2
// Switch to location l4

//transition t24: l2,l4,
	   c4 >= 40
	   _c4=0;
	   
	   _c1-c1=0;
	   _c2-c2=0;
	   _c3-c3=0;

	   _k4=1
	   
	   _k1-k1=0;
	   _k2-k2=0;
	   _k3-k3=0;
	   
	   _t-t=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
	   _x4-x4=0;

//Process 4 arrives in location l3
// Switch to location l4

//transition t25: l3,l4,
	   c4 >= 40
	   _c4=0;
	   
	   _c1-c1=0;
	   _c2-c2=0;
	   _c3-c3=0;

	   _k4=1
	   
	   _k1-k1=0;
	   _k2-k2=0;
	   _k3-k3=0;
	   
	   _t-t=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
	   _x4-x4=0;

	   	
//Process 4 completes in location l4
//Incomplete process 3 exists

//transition t26: l4,l3,
	   k4-1=0;
	   x4-4=0;
	   k3>=1
	   
	   _k4-k4+1=0;
	   _k1-k1=0;
	   _k2-k2=0;
	   _k3-k3=0;
	   
	   	   
	   _t-t=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
	   _x4-x4=0;


	   _c1-c1=0;
	   _c2-c2=0;
	   _c3-c3=0;
	   _c4-c4=0;
	  
	
//Process 4 completes in location l4
//Incomplete process 2 exists

//transition t27: l4,l2,
	   k4-1=0;
	   x4-4=0;
	   k3=0;
	   k2 >= 1
 
	   _k4-k4+1=0;
	   _k1-k1=0;
	   _k2-k2=0;
	   _k3-k3=0;
	   
	   	   
	   _t-t=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
	   _x4-x4=0;


	   _c1-c1=0;
	   _c2-c2=0;
	   _c3-c3=0;
	   _c4-c4=0;
	  
	   
	
//Process 4 completes in location l4
//Incomplete process 1 exists

//transition t28: l4,l1,
	   k4-1=0;
	   x4-4=0;
	   k3=0;
	   k2=0;
	   k1>=1
 
	   _k4-k4+1=0;
	   _k1-k1=0;
	   _k2-k2=0;
	   _k3-k3=0;
	   
	   	   
	   _t-t=0;

	   _x1-x1=0;
	   _x2-x2=0;
	   _x3-x3=0;
	   _x4-x4=0;


	   _c1-c1=0;
	   _c2-c2=0;
	   _c3-c3=0;
	   c4-c4=0;
	  
	   	   
  }//while


  return -1;
}


int schedule5p(int seed){
  srand(seed);

  return -1;
}


//STING High Dimension (Convoy of Cars)

void cars2p_dummy(int x1, int x2, int v1, int v2, 
                  int a1, int a2, int r2, int tt, int br, int ac){}
int cars2p(int seed){

  //todo  
  //./inv cars2p 941547
  //inv: inv_sting.h:1718: cars2p: Assertion `r2 <= 5' failed.

  srand(seed);

  //location l0
	int x1 = randrange_i(100,150,INCLUDE);
	int x2 = randrange_i(50,80,INCLUDE);
  int v1 = 15;
  int v2 = 5;
  int a1=0;
  int a2=0;
  int r2=0;
  int tt=0;

  const int br=-2;
  const int ac=1; 

  /*time step is 1 seconds
  //let us assume that things are 
  //normalized to this time step
  //when things are fine in terms of braking with car 1*/


  //invariant l0:
  assert(a1 - br >= 0 && a1 - ac <= 0 && a2 - br >= 0 && 
         a2 - ac <= 0 && r2 <= 5 && r2 >= 0);
  


  set_tracker(6);


  printf("x1 x2 v1 v2 a1 a2  r2 tt br ac\n");
  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){
    

    //invs we want to discover
    assert (ac -1  == 0);
    assert (br  + 2  == 0); 
    assert (-v1 +tt  + 15 >= 0);
    assert (-v2 +tt  + 5 >= 0);
    assert (-a1  + 1 >= 0);
    assert (-a2  + 1 >= 0);
    assert (-r2  + 6 >= 0);
    assert (-r2 +tt  >= 0);
    assert (r2  >= 0);
    assert (a2  + 2 >= 0);
    assert (a1  + 2 >= 0);
    assert (v2 -a2 -r2  + 6 >= 0);
    assert (v2 +2*tt -5 >= 0);
    assert (3*v2 -2*a2  + 2 >= 0);
    assert (v1 -a1 -r2  + 6 >= 0);
    assert (v1 +2*tt -15 >= 0);
    assert (v1 +2*v2 -2*a2  + 2 >= 0);
    assert (2*v1 +v2 -2*a1  + 2 >= 0);
    assert (3*v1 -2*a1  + 2 >= 0);
    assert (x2 -50 >= 0);
    assert (x1 -x2 -v1 +v2  + 3 >= 0);
    assert (x1 -x2 +v2 -31*a2 +30*r2  >= 0);
    assert (x1 -x2 +v2 -a2  >= 0);
    assert (x1 -x2 +v2 +2*r2  >= 0);
    assert (x1 -x2 +15*v2 +30*r2  >= 0);
    assert (x1 -x2 +20*v2 -50*a2 +30*r2  >= 0);
    assert (x1 -x2 +50*v2 -50*a2  >= 0);
    assert (x1 -x2 +65*v2 -50*a2 +30*r2  >= 0);
    assert (x1 -x2 +2*v1 +v2 -2*a1  + 2 >= 0);
    assert (x1 -x2 +14*v1 +v2 +30*r2  >= 0);
    assert (x1 -x2 +15*v1 +v2 -a2 +30*r2  >= 0);
    assert (x1 -x2 +15*v1 +50*v2 -50*a2 +30*r2  >= 0);
    assert (x1 -100 >= 0);

    sprintf(buf,"%d %d %d %d %d %d %d %d %d %d\n",
            x1, x2, v1, v2, a1, a2, r2, tt, br, ac);
    hash_print(buf);
    cars2p_dummy(x1, x2, v1, v2, a1, a2, r2, tt, br, ac);



    int rd = randrange_i(1,6,INCLUDE);

    //transition telapse: l0,
    if (rd==1 && 
        br+2 == 0 && ac -1 == 0 && x1 - x2 -30 >=0 && 
        r2 == 0 && v1 >=0 && v2 >=0 &&

        //l0 invs
        a1 - br >= 0 && a1 - ac <= 0 && a2 - br >= 0 && 
        a2 - ac <= 0 && r2 <= 5 && r2 >= 0){

      incr_tracker_pos(rd);

      x1 = x1 + v1;
      x2 = x2 + v2;
      v1 = v1 + a1;
      v2 = v2 + a2;
      r2 = 0	;
      tt = tt + 1;
      //preserve[a1,a2,br,ac]
    }

    //Car2 is too close start the reaction variable
    //transition telapse1: l0,
    if (rd==2 && 
        br+2==0 && ac -1==0 && x1 - x2  >=0 && x1 - x2 -30 <= 0 && 
        r2 - 5 <=0 && v1 >=0 && v2 >=0  &&

        //l0 invs
        a1 - br >= 0 && a1 - ac <= 0 && a2 - br >= 0 && 
        a2 - ac <= 0 && r2 <= 5 && r2 >= 0){
      incr_tracker_pos(rd);

      x1 = x1 + v1;
      x2 = x2 + v2;

      v1 = v1 + a1;
      v2 = v2 + a2;

      r2 = r2 + 1;
      tt = tt + 1;
      //preserve[a1,a2,br,ac]
    }


    /*lead car transitions 
      it can decide to do anything quirky 
      like set its acceleration to anywhere between 
      br && ac*/

    //transition tlead: l0,
    if (rd == 3 && 
        br +2 == 0 && ac -1 == 0 && x1 -x2 >=0 && r2 -10 <=0	&&
        v1 >= 0 && v2 >= 0 && ac -br >= 0  &&

        //l0 invs
        a1 - br >= 0 && a1 - ac <= 0 && a2 - br >= 0 && 
        a2 - ac <= 0 && r2 <= 5 && r2 >= 0){
      incr_tracker_pos(rd);

      a1 = randrange_i(br,ac,INCLUDE);
      assert(a1 - ac <=0 && a1 - br >=0);

      //preserve[x1,x2,v1,v2,a2,t,br,ac,r2,t]
    }

    //car 2 senses the position of x1 && breaks if it is too close
    //reset reactopm variable too 

    //transition t1: l0,
    if (rd==4 && 

        br +2 == 0 && ac -1==0 && x1 -x2 >=0 && r2 -10 <=0 && 
        v1 >=0 && v2 >=0 && x1 -x2 <= 30 &&

        //l0 invs
        a1 - br >= 0 && a1 - ac <= 0 && a2 - br >= 0 && 
        a2 - ac <= 0 && r2 <= 5 && r2 >= 0){
      incr_tracker_pos(rd);
      
      a2 = randrange_i(br,min(a1,0),INCLUDE);
      assert(a2 -br >= 0 && a2 -a1 <=0 && a2 <=0);

      r2=0;
      //preserve[x1,x2,v1,v2,a1,t,br,ac,t]
    }

    //car 2 senses the position of x1 && accelerates if it is too far
    //transition t2: l0,
    if (rd==5 && 
        
        br +2 == 0 && ac -1==0 && x1 -x2 >=0 &&
        r2 -10 <=0 && v1 >=0 && v2 >=0 && x1 -x2 >= 50  &&

        //l0 invs
        a1 - br >= 0 && a1 - ac <= 0 && a2 - br >= 0 && 
        a2 - ac <= 0 && r2 <= 5 && r2 >= 0){
      incr_tracker_pos(rd);

      a2 = randrange_i(max(0,a1),ac,INCLUDE);
      assert(a2 >=0 && a2 -ac <=0 && a2 - a1 >=0);
      //preserve[x1,x2,v1,v2,a1,t,br,ac,r2,t]
    }

    //If in optimal range, car 2 will just coast 
    //(i.e., cruise, no brake or accerlation)
    //transition t5: l0,
    if (rd==6 && 

        br +2 ==0 && ac -1==0 && x1 -x2 >=0 && r2 -10 <=0 &&
        v1 >=0 && v2 >=0 && x1 -x2 >= 30 && x1 -x2 <= 50  &&

        //l0 invs
        a1 - br >= 0 && a1 - ac <= 0 && a2 - br >= 0 && 
        a2 - ac <= 0 && r2 <= 5 && r2 >= 0){
      incr_tracker_pos(rd);

      a2  = 0;
      //preserve[x1,x2,v1,v2,a1,t,br,ac,r2,t]
    }
  }

  print_tracker(TRUE);
  return -1;
}


void cars3p_dummy(int x1, int x2, int x3, int v1, int v2, 
                  int v3, int a1, int a2, int a3, int t, 
                  int br, int ac, int r2, int r3){}
int cars3p(int seed){

  srand(seed);

  //location l0
	int x1 = randrange_i(100,150,INCLUDE);
	int x2 = randrange_i(50,80,INCLUDE);
	int x3 = 0;
	int v1 = randrange_i(15,20,INCLUDE);
	int v2 = randrange_i(5,10,INCLUDE);
	int v3 = randrange_i(10,15,INCLUDE);
	int br = -1;
	int ac = 1;

	int a1 = 0;
	int a2 = 0;
	int a3 = 0;

	int r2 = randrange_i(0,5,INCLUDE);
	int r3 = randrange_i(0,5,INCLUDE);

	int tt = max(r2,r3);

  //invariant l0:
  assert(r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5);

  /*time step is 1 seconds
    let us assume that things are 
    normalized to this time step*/
  

  printf("x1 x2 x3 v1 v2 v3 a1 a2 a3 t br ac r2 r3\n");

  set_tracker(11);
  while (get_n_incr_loop_ctr_tracker() < MAX_LOOP){
         
    
    assert (ac -1  == 0); 
    assert (br  + 1  == 0); 
    assert (-a1  + 1 >= 0);
    assert (-a2  + 1 >= 0);
    assert (-a3  + 1 >= 0);
    assert (-r2  + 6 >= 0);
    assert (-r3  + 6 >= 0);
    assert (r3  >= 0);
    assert (r2  >= 0);
    assert (tt - r2  >= 0);
    assert (tt - r3  >= 0);
    assert (a3  + 1 >= 0);
    assert (a2  + 1 >= 0);
    assert (a1  + 1 >= 0);
    assert (v3 -a3 -r2  + 6 >= 0);
    assert (v3 -a3 -r3  + 6 >= 0);
    assert (v3 -a3  + 1 >= 0);
    assert (v2 -a2 -r2  + 6 >= 0);
    assert (v2 -a2 -r3  + 6 >= 0);
    assert (v2 -a2  + 1 >= 0);
    assert (v1 -a1 -r2  + 6 >= 0);
    assert (v1 -a1 -r3  + 6 >= 0);
    assert (v1 -a1  + 1 >= 0);
    assert (x3  >= 0);
    assert (x2 -x3 +v3 -a3 -30*r2 +30*r3  + 150 >= 0);
    assert (x2 -x3 +v3 -a3  >= 0);
    assert (x2 -x3 +50*v3 -50*a3 -30*r2 +30*r3  + 150 >= 0);
    assert (x2 -x3 +50*v3 -50*a3  >= 0);
    assert (x2 -50 >= 0);
    assert (x1 -x2 +v2 -a2  >= 0);
    assert (x1 -x2 +v2 -a2 +30*r2 -30*r3  + 150 >= 0);
    assert (x1 -x2 +50*v2 -50*a2  >= 0);
    assert (x1 -x2 +50*v2 -50*a2 +30*r2 -30*r3  + 150 >= 0);
    assert (x1 -x3 +v3 -a3 -30*r2 +30*r3  + 150 >= 0);
    assert (x1 -x3 +v3 -a3  >= 0);
    assert (x1 -x3 +50*v3 -50*a3 -30*r2 +30*r3  + 150 >= 0);
    assert (x1 -x3 +50*v3 -50*a3  >= 0);
    assert (x1 -100 >= 0);
    
    sprintf(buf,"%d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
            x1, x2, x3, v1, v2, v3, a1, a2, a3, tt, br, ac, r2, r3);
    hash_print(buf);
    cars3p_dummy(x1, x2, x3, v1, v2, v3, a1, a2, a3, tt, br, ac, r2, r3);
    

    int rd = randrange_i(1,11,INCLUDE);

    //transition telapse1: l0,
    if (rd == 1 && 
        br+1==0 && ac -1 == 0 && x1 -x2 >=30 && x2 - x3 >=30 && 
        r2==0 && r3==0 && v1 >=0 &&	v2 >=0 && v3 >=0 &&

        //l0 invs
        r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5){

      incr_tracker_pos(rd);

      x1 =  x1 + v1;
      x2 =  x2 + v2;
      x3 =  x3 + v3;
    
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;
      tt = tt + 1;

      //preserve[a1,a2,a3,br,ac,r2,r3]
    }

    //transition telapse2: l0,
    if (rd == 2 && 
        br+1==0 &&	ac -1==0 && x1 -x2 >=30 &&
        x2 - x3 >=0 && x2-x3 <= 30 && r2 == 0 &&
        v1 >=0 && v2 >=0 && v3 >=0 &&

        //l0 invs
        r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5){
	
      incr_tracker_pos(rd);

      x1 =  x1 + v1;
      x2 =  x2 + v2;
      x3 =  x3 + v3;
	
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;

      tt = tt + 1;
      r3 = r3 + 1;

      //preserve[a1,a2,a3,br,ac,r2]
    }

    //transition telapse3: l0,
    if(rd==3 && br+1==0 && ac -1==0 && x2 - x3 >= 30 &&
       x1 - x2 >= 0&& x1 - x2 <= 30 && r3 == 0&&
       v1 >=0 && v2 >=0 && v3 >=0  &&

       //l0 invs
       r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5){
     
      incr_tracker_pos(rd);

      x1 =  x1 + v1;
      x2 =  x2 + v2;
      x3 =  x3 + v3;
	
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;
		
      tt = tt + 1;
      r2 = r2 + 1;
      //preserve[a1,a2,a3,br,ac,r3]
    }

    //transition telapse4: l0,
    if (rd==4 && br+1==0 && ac -1==0 &&	x2 - x3 >= 0 &&
        x2 - x3 <= 30 && x1 - x2 >= 0 && x1 - x2 <= 30 && 
        v1 >=0 && v2 >=0 && v3 >=0 &&

        //l0 invs
        r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5){
      //todo: never reached here
      incr_tracker_pos(rd);

      x1 =  x1 + v1;
      x2 =  x2 + v2;
      x3 =  x3 - v3;
	
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;
		
      tt = tt + 1;
      r2 = r2  + 1;
      r3 = r3 + 1;
      //preserve[a1,a2,a3,br,ac]
    }


    /*lead car transitions 
      it can decide to do anything quirky 
      like set its acceleration to anywhere between 
      br and ac*/

    //transition tlead: l0,
    if (rd == 5 && 
        br +1 == 0 && ac -1 == 0 && x1 -x2 >=0 && 
        x2 - x3 >=0 && v1 >=0 && v2 >=0 && v3 >=0 && ac -br >=0 &&

        //l0 invs
        r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5){
        
      incr_tracker_pos(rd);

      a1 = randrange_i(br, ac, INCLUDE);
      assert(a1 - ac <=0 && a1 - br >=0);
           
      //preserve[x1,x2,x3,v1,v2,v3,a2,a3,t,br,ac,r2,r3]
    }


    //car 2 senses the position of x1 and breaks if it is too close
    //transition t1: l0,
    if (br +1 == 0 && ac - 1 == 0 && x1 - x2 >=0 && x2 - x3 >=0 &&
        v1 >=0 && v2 >=0 && v3 >=0 &&     x1 -x2 <= 30 && rd == 6  &&

        //l0 invs
        r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5){
      
      incr_tracker_pos(rd);

      a2 = randrange_i(br, min(0,a1), INCLUDE);
      assert(a2 <=0 && a2 -br >= 0 && a2 -a1 <= 0);
      r2=0;
           
      //preserve[x1,x2,x3,v1,v2,v3,a1,a3,t,br,ac,r3]
    }

    //car 2 senses the position of x1 and accelerates if it is too far
    //transition t2: l0,
    if (br +1 == 0 && ac -1 == 0 && x1 -x2 >=0 && x2 - x3 >=0 && 
        v1 >=0 && v2 >=0 && v3 >=0 && x1 -x2 >= 50 && rd == 7 &&

        //l0 invs
        r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5){
      
      incr_tracker_pos(rd);

      a2 = randrange_i(max(0,a1), ac, INCLUDE);
      assert(a2 >=0 && a2 -ac <=0 && a2 - a1 >=0);
           
      //preserve[x1,x2,x3,v1,v2,v3,a1,a3,t,br,ac,r2,r3]
    }

    //If in optimal range, car 2 will just coast

    //transition t5: l0,
    if (br +1 == 0 && ac -1 == 0 && x1 -x2 >=0 && x2 - x3 >=0 &&
        v1 >=0 && v2 >=0 && v3 >=0 && x1 -x2 >= 30 && 
        x1 -x2 <= 50 && rd == 8  &&

        //l0 invs
        r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5){

      incr_tracker_pos(rd);
      
      a2 =0;
      //preserve[x1,x2,x3,v1,v2,v3,a1,a3,t,br,ac,r2,r3]
    }

    //car 3 senses the position of car 2 and 
    //does some adjustments to its position
    //transition t3: l0,
    if (br +1 ==0 && ac -1 == 0 && x1 -x2 >=0 && x2 - x3 >=0 &&
        v1 >=0 && v2 >=0 && v3 >=0 && x2 - x3 <= 30 && rd == 9){
      
      incr_tracker_pos(rd);

      a3= randrange_i(br,min(0,a2),INCLUDE);
      assert (a3 <=0 && a3 -br >= 0 && a3 - a2 <=0);
      r3=0;

      //preserve[x1,x2,x3,v1,v2,v3,a1,a2,t,br,ac,r2]
    }


    //transition t4: l0,
    if (br +1 == 0 && ac -1== 0 && x1 -x2 >=0 && x2 - x3 >=0 && 
        v1 >=0 && v2 >=0 && v3 >=0 && x2 - x3 >= 50 && rd == 10 &&

        //l0 invs
        r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5){
    
      incr_tracker_pos(rd);

      a3 = randrange_i(max(0,a2),ac,INCLUDE);
      assert(a3 >=0 && a3 -ac <= 0 && a3 -a2 >=0);
      //preserve[x1,x2,x3,v1,v2,v3,a1,a2,t,br,ac,r2,r3]
    }


    //transition t6: l0,
    if (br +1 ==0 && ac -1==0 && x1 -x2 >=0 && 	x2 - x3 >=0 &&
        v1 >=0 && v2 >=0 && v3 >=0 && x2 -x3 >= 30 && x2 - x3 <= 50 && 
        rd == 11 &&

        //l0 invs
        r2 >=0 && r3 >=0 && r2 <= 5 && r3 <= 5){

      incr_tracker_pos(rd);

      a3 =0;
      //preserve[x1,x2,x3,v1,v2,v3,a1,a2,t,br,ac,r2,r3]
    }
  }

  print_tracker(TRUE);
  return -1;
}


void cars4p_dummy(int x1, int x2, int x3, int x4, 
                  int v1, int v2, int v3, int v4, 
                  int a1, int a2, int a3, 
                  int tt, int br, int ac, 
                  int r2, int r3, int r4){}

int cars4p(int seed){

  //todo

  //variable [ x1 x2 x3 x4  v1 v2 v3 v4 a1 a2 a3 a4 t br ac r2 r3 r4]
  
  srand(seed);

  //location l0
	int x1 = 100;//randrange_i(100,150,INCLUDE);
  int x2 = 50;//randrange_i(50,80,INCLUDE);
	int x3 = 0;
	int x4 = -50;

	int v1 = 15;//randrange_i(15,20,INCLUDE);
	int v2 = 5;//randrange_i(5,10,INCLUDE);
	int v3 = 10;//randrange_i(10,15,INCLUDE);
	int v4 = 5;//randrange_i(5,10,INCLUDE);

	int br = -1;
	int ac = 1;

	int a1 = 0;
	int a2 = 0;	
	int a3 = 0;
	int a4 = 0;

	int r2 = 0;
	int r3 = 0;
	int r4 = 0;
	
	int tt = 0;

  //invariant l0:
  assert(r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
         r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0);


  set_tracker(18);

  printf("x1 x2 x3 x4 v1 v2 v3 v4 a1 a2 a3 tt br ac r2 r3 r4\n");
  while(get_n_incr_loop_ctr_tracker() < MAX_LOOP){


    assert (ac -1  == 0);
    assert (br  + 1  == 0); 
    assert (-r2  + 6 >= 0);
    assert (-r3  + 6 >= 0);
    assert (-r4  + 6 >= 0); 
    assert (r4  >= 0);
    assert (r3  >= 0);
    assert (r2  >= 0);
    assert (r2 +r3 -r4  + 5 >= 0);
    assert (tt -r2  >= 0);
    assert (tt -r3  >= 0);
    assert (tt -r4  >= 0);
    assert (x3 -x4 +v4 -a4 -30*r2 +30*r4  + 150 >= 0);
    assert (x3 -x4 +v4 -a4 -30*r3 +30*r4  + 150 >= 0);
    assert (x3 -x4 +v4 -a4  >= 0);
    assert (x3  >= 0);
    assert (x2 -x4 +v4 -a4 -30*r2 +30*r4  + 150 >= 0);
    assert (x2 -x4 +v4 -a4 -30*r3 +30*r4  + 150 >= 0);
    assert (x2 -x4 +v4 -a4  >= 0);
    assert (x2 -50 >= 0);
    assert (x1 -x4 +v4 -a4 -30*r2 +30*r4  + 150 >= 0);
    assert (x1 -x4 +v4 -a4 -30*r3 +30*r4  + 150 >= 0);
    assert (x1 -x4 +v4 -a4  >= 0);
    assert (1*x1 -100 >= 0);
    
    sprintf(buf,"%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
            x1,x2,x3,x4,v1,v2,v3,v4,a1,a2,a3,tt,br,ac,r2,r3,r4);
    hash_print(buf);

    cars4p_dummy(x1,x2,x3,x4,v1,v2,v3,v4,a1,a2,a3,tt,br,ac,r2,r3,r4);

    int rd = randrange_i(1,18,INCLUDE);

    /*time step is 1 seconds
      let us assume that things are 
      normalized to this time step*/
    
    
    //transition telapse11: l0,
    if (br+1==0 && ac -1==0 && x1 -x2 >=30 && x2 - x3 >=30 && r2==0 && r3==0&&
        x3 -x4 >= 30&& r4==0&& v1 >=0&& v2 >=0&& v3 >=0&& v4 >=0&& rd==1){
      incr_tracker_pos(rd);
      x1 = x1 + v1;
      x2 = x2 + v2;
      x3 = x3 + v3;
      x4 = x4 + v4;
      
      v4 = v4 + a4;
      
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;
      
      tt = tt + 1;
      
      //preserve[a1,a2,a3,br,ac,r2,r3,r4]
    }

    //transition telapse12: l0,
    if (br+1==0 &&  ac -1 == 0 && x1 -x2 >=30 && x2 - x3 >=0 &&
        x2-x3 <= 30 && x3 - x4 >= 30 && r4==0 && r2 == 0 &&
        v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0 && rd == 2){
        
      incr_tracker_pos(rd);
      x1 =  x1 + v1 ;
      x2 =  x2 + v2 ;
      x3 =  x3 + v3 ;
        
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;
        
      x4 = x4 + v4;
      v4 = v4 + a4;
      tt = tt + 1;
      r3 = r3 + 1;
        
      //preserve[a1,a2,a3,br,ac,r2,r4]
    }
      
    //transition telapse13: l0,
    if (br+1==0 && ac -1==0 && x2 - x3 >= 30&& x1 - x2 >= 0&&
        x1 - x2 <= 30 && r3 == 0&& x3 -x4 >= 30&& r4==0&&
        v1 >=0&& v2 >=0&& v3 >=0&& v4 >=0&& rd == 3){
      
      incr_tracker_pos(rd);
      x1 = x1 + v1;
      x2 = x2 + v2;
      x3 = x3 + v3;
        
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;
        
      x4 = x4 + v4;
      v4 = v4 + a4;
        
      tt = tt + 1;
      r2 = r2 + 1;
        
      //preserve[a1,a2,a3,br,ac,r3,r4]
    }

    //transition telapse14: l0,
    if (br+1==0 && ac -1==0 && x2 - x3 >= 0 && x2 - x3 <= 30 &&
        x1 - x2 >= 0 && x1 - x2 <= 30 && x3 -x4 >= 30 && r4 == 0 &&
        v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0 && rd == 4 &&

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){
        
      incr_tracker_pos(rd);        
      x1 =  x1 + v1;
      x2 =  x2 + v2;
      x3 =  x3 + v3;
        
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;
        
      tt = tt + 1;
	
      x4 = x4 + v4;
      v4 = v4 + a4;
        
      r2 = r2 + 1;
      r3 = r3 + 1;
        
      //preserve[a1,a2,a3,br,ac,r4]
    }
      
      
      
    //transition telapse21: l0,
    if(rd == 5 &&

       br+1==0 && ac -1==0 && x1 -x2 >=30 && x2 - x3 >=30 && 
       x3 -x4 >= 0 && x3-x4 <=30 && 

       //l0 invs
       r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
       r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
       ){

      incr_tracker_pos(rd);        
      printf("v1 %d,v2 %d,v3 %d, v4 %d, x1 %d, x2 %d, x3 %d, x4 %d, r2 %d, r3 %d, r4 %d\n",
             v1,v2,v3,v4,x1,x2,x3,x4,r2,r3,r4);
      
      r4 = r4 + 1;
      

      if(r2==0 && r3==0 &&
         v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0
         ){

        x1 = x1 + v1;
        x2 = x2 + v2;
        x3 = x3 + v3;
        
        x4 = x4 + v4;
        v4 = v4 + a4;
        
        v1 = v1 + a1;
        v2 = v2 + a2;
        v3 = v3 + a3;
        
        tt = tt + 1;
        
      }

      printf("new v1 %d,v2 %d,v3 %d, v4 %d, x1 %d, x2 %d, x3 %d, x4 %d, r2 %d, r3 %d, r4 %d\n",
             v1,v2,v3,v4,x1,x2,x3,x4,r2,r3,r4);
      assert(r2+r3-r4>=-5);
      //preserve[a1,a2,a3,br,ac,r2,r3]
    }
      

    //transition telapse22: l0,
    if(rd==6 && 

       br+1==0&& ac -1==0 && x1 -x2 >=30 && x2 - x3 >=0 && x2-x3 <= 30 &&
       r2 ==0&& v1 >=0&& v2 >=0&& v3 >=0&& v4 >=0&& 
       
       //l0 invs
       r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
       r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
       ){

      incr_tracker_pos(rd);
        
      x1 =  x1 + v1;
      x2 =  x2 + v2;
      x3 =  x3 + v3;
	
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;
	
      x4 = x4 + v4;
      v4 = v4 + a4;
		
      if (!(x3-x4 >= 0 && x3 - x4 <= 30)){
        x4 = randrange_i(x3-30,x3,INCLUDE);
      }

      if(x3 - x4 >= 0 && x3 - x4 <=30){
        r4 = r4 + 1;
        tt = tt + 1;
        r3 = r3 + 1;
      }
      //preserve[a1,a2,a3,br,ac,r2]
    }

    //transition telapse23: l0,

    if (rd == 7&&
        
        br+1==0 && ac -1==0 && x2 - x3 >= 30 && x1 - x2 >= 0 && x1 - x2 <= 30 &&
        r3 == 0 && v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0 && 

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){

      incr_tracker_pos(rd);
	
      x1 = x1 + v1;
      x2 = x2 + v2;
      x3 = x3 + v3;
	
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;
	
      x4 = x4 + v4;
      v4 = v4 + a4;

      if (x3 - x4 >= 0 && x3 - x4 <=30){
        r4 = r4 + 1;
        tt = tt + 1;
        r2 = r2 + 1;
      }

      //preserve[a1,a2,a3,br,ac,r3]
    }

    //transition telapse24: l0,
    if(br+1==0 && ac -1== 0&& x2 - x3 >= 0 && x2 - x3 <= 30 && x1 - x2 >= 0 &&
       x1 - x2 <= 30 &&  v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0 && rd ==8 &&

       //l0 invs
       r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
       r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
       ){

      incr_tracker_pos(rd);
	
      x1 =  x1 + v1;
      x2 =  x2 + v2;
      x3 =  x3 + v3;
	
      v1 = v1 + a1;
      v2 = v2 + a2;
      v3 = v3 + a3;
		
      x4 = x4 + v4;
      v4 = v4 + a4;
      
      if(x3 -x4 >= 0 && x3-x4 <=30){
           
        r4 = r4 + 1;
        
        tt = tt + 1;

        r2 = r2 + 1;
        r3 = r3 + 1;
      }
      //preserve[a1,a2,a3,br,ac]
    }


    /*lead car //transitions
      it can decide to do anything quirky
      like set its acceleration to anywhere between
      br and ac  */


    //transition tlead: l0,
    if (br +1 == 0&& ac -1==0 && x1 -x2 >=0&& x2 - x3 >=0&&
        x3 - x4 >= 0 && v1 >=0&& v2 >=0&& v3 >=0&& v4 >=0&& rd == 9 &&

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){

      incr_tracker_pos(rd);
 
      a1=randrange_i(br,ac,INCLUDE);
      assert(a1 - ac <=0 && a1 - br >=0);
           
      //preserve[x1,x2,x3,x4,v1,v2,v3,v4,a2,a3,a4,t,br,ac,r2,r3,r4]
    }


    //car 2 senses the position of x1 and breaks if it is too close
    //transition t1: l0,
    if (rd == 10 && 
        br +1 == 0 && ac -1 == 0 && x1 -x2 >=0 && x2 - x3 >=0 && 
        x3 - x4 >=0 && v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0 && 
        x1 -x2 <= 30 && 
        

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){
      
      incr_tracker_pos(rd);

      a2 = randrange_i(br,min(0,a1),INCLUDE);
      assert(a2 <=0 && a2 -a1 <= 0 && a2 -br >= 0);
      r2 =0;
	
      //preserve[x1,x2,x3,x4,v1,v2,v3,v4,a1,a3,a4,t,br,ac,r3,r4]
    }

    //car 2 senses the position of x1 and accelerates if it is too far
    //transition t2: l0,
    if (rd == 11 &&
        br +1 == 0 && ac -1 == 0 && x1 -x2 >=0 && x2 - x3 >=0 && 
        x3-x4>=0 && v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0 && 
        x1 -x2 >= 50 && 
        
        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){

      incr_tracker_pos(rd);
 
      a2 = randrange_i(max(0,a1),ac,INCLUDE);
      assert(a2 >=0 && a2 -a1 >=0 && a2 -ac <=0);
      //preserve[x1,x2,x3,x4,v1,v2,v3,v4,a1,a3,a4,t,br,ac,r2,r3,r4]
    }
         

    //If in optimal range, car 2 will just coast

    //transition t5: l0,
    if (rd == 12 &&
        br +1 == 0 && ac -1 == 0 && x1 -x2 >=0 && x2 - x3 >=0 && 
        x3-x4>=0 && v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0 &&
        x1 -x2 >= 30 && x1 -x2 <= 50 && 

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){
      
      incr_tracker_pos(rd);
      a2 =0;
      //preserve[x1,x2,x3,x4,v1,v2,v3,v4,a1,a3,a4,t,br,ac,r2,r3,r4]
    }


    //car 3 senses the position of car 2 and
    //does some adjustments to its position
    //transition t3: l0,
    if (rd == 13 && 
        br +1 == 0 && ac -1 == 0 && x1 -x2 >=0 && x2 - x3 >=0 && 
        x3-x4>=0 && v1 >= 0 && v2 >= 0 && v3 >= 0 && v4 >= 0 && 
        x2 - x3 <= 30 && 

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){
      
      incr_tracker_pos(rd);

      a3 = randrange_i(br,min(0,a2),INCLUDE);
      assert(a3 -a2 <=0&& a3 <=0 && a3 -br >= 0);
      r3=0;
      //preserve[x1,x2,x3,x4,v1,v2,v3,v4,a1,a2,a4,t,br,ac,r2,r4]
    }


    //transition t4: l0,
    if (rd==14 &&
        br +1 == 0 && ac -1==0 && x1 - x2 >=0 && x2 - x3 >=0 && 	
        x3 - x4 >=0 && v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0 && 
        x2 - x3 >= 50 && 

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){
      
      incr_tracker_pos(rd);

      a3=randrange_i(max(a2,0),ac,INCLUDE);
      assert(a3 >=0 && a3 -ac <= 0 && a3 -a2 >=0);
      
      //preserve[x1,x2,x3,x4,v1,v2,v3,v4,a1,a2,a4,t,br,ac,r2,r3,r4]
    }


    //transition t6: l0,
    if (rd==15 && 
        br +1 == 0 && ac -1 == 0 && x1 -x2 >=0 && x2 - x3 >=0 &&
        x3 - x4 >=0 && v1 >=0 && v2 >=0 &&v3 >=0 && v4 >=0 &&
        x2 -x3 >= 30 && x2 - x3 <= 50 && 

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){

      incr_tracker_pos(rd);
      
      a3 =0;
	
      //preserve[x1,x2,x3,x4,v1,v2,v3,v4,a1,a2,a4,t,br,ac,r2,r3,r4]
    }


    //For the car 4 in the platoon,  needs to look at car 3 and adjust

    //transition t7: l0,
    if (rd == 16 && 
        br +1 == 0 && ac -1 == 0 && x1 -x2 >=0 && x2 - x3 >=0 &&
        x3-x4>=0 && v1 >= 0 && v2 >= 0 && v3 >= 0 && v4 >= 0 && 
        x3 - x4 <= 30 && 

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){
      incr_tracker_pos(rd);

      a4 = randrange_i(br, min(0,a3),INCLUDE);
      assert(a4 <= 0 && a4 -a3 <= 0 && a4 -br >= 0);
      r4=0;

      //preserve[x1,x2,x3,x4,v1,v2,v3,v4,a1,a2,a3,t,br,ac,r2,r3]
    }

    //transition t8: l0,
    if (rd == 17 &&
        br +1 == 0 && ac -1== 0&& x1 - x2 >=0 && x2 - x3 >=0 &&
        x3 - x4 >=0 && v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0 && 
        x3 - x4 >= 50 && 
        

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){

      incr_tracker_pos(rd);

      a4 = randrange_i(max(0,a3),ac,INCLUDE);
      assert(a4 >= 0 && a4 -a3 >= 0 &&  a4 -ac <= 0);
      //preserve[x1,x2,x3,x4,v1,v2,v3,v4,a1,a2,a3,t,br,ac,r2,r3,r4]
    }


    //transition t9: l0,

    if (br +1 == 0 && ac -1 == 0 && x1 -x2 >=0 && x2 - x3 >=0 &&
        x3 - x4 >=0 && v1 >=0 && v2 >=0 && v3 >=0 && v4 >=0 &&
        x3 -x4 >= 30 && x3 - x4 <= 50 && rd == 18 &&

        //l0 invs
        r2 >=0 && r2 -5 <= 0 && r3 >=0 && r3-5<=0 && 
        r4 >= 0 && r4 - 5 <= 0 && x4+50 >= 0
        ){
	
      incr_tracker_pos(rd);

      a4 =0;
      //preserve[x1,x2,x3,x4,v1,v2,v3,v4,a1,a2,a3,t,br,ac,r2,r3,r4]
    }


  }
  return -1;
}





    //STING
    /* else if (strcmp(argv[1],"seesaw")==0){ */
    /*   printf("#result = %d\n", seesaw(atoi(argv[2]))); */
    /* } */
    /* else if (strcmp(argv[1],"robot")==0){ */
    /*   printf("#result = %d\n", robot(atoi(argv[2]))); */
    /* } */
    /* else if (strcmp(argv[1],"berkeley")==0){ */
    /*   printf("#result = %d\n",  */
    /*          berkeley(atoi(argv[2]),atoi(argv[3]), */
    /*                   atoi(argv[4]),atoi(argv[5]))); */
    /* } */
    /* else if (strcmp(argv[1],"berkeley_nat")==0){ */
    /*   printf("#result = %d\n",  */
    /*          berkeley(atoi(argv[2]),atoi(argv[3]), */
    /*                   atoi(argv[4]),atoi(argv[5]))); */
    /* } */
    /* else if (strcmp(argv[1],"heap")==0){ */
    /*   printf("#result = %d\n",  */
    /*          heap(atoi(argv[2]), atoi(argv[3]))); */
    /* } */
    /* else if (strcmp(argv[1],"efm")==0){ */
    /*   printf("#result = %d\n",  */
    /*          efm(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]), */
    /*              atoi(argv[5]),atoi(argv[6]),atoi(argv[7]) */
    /*              )); */
    /* } */
    /* else if (strcmp(argv[1],"efm1")==0){ */
    /*   printf("#result = %d\n",  */
    /*          efm1(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]), */
    /*              atoi(argv[5]),atoi(argv[6]),atoi(argv[7]) */
    /*              )); */

    /* } */
    /* else if (strcmp(argv[1],"lifo")==0){ */
    /*   printf("#result = %d\n", lifo(atoi(argv[2]))); */
    /* } */
    /* else if (strcmp(argv[1],"lifo_nat")==0){ */
    /*   printf("#result = %d\n", lifo_nat(atoi(argv[2]))); */
    /* } */
    /* else if (strcmp(argv[1],"cars_midpt")==0){ */
    /*   printf("#result = %d\n",  */
    /*          cars_midpt(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]))); */
    /* } */
    /* else if (strcmp(argv[1],"swim_pool")==0){ */
    /*   printf("#result = %d\n",  */
    /*          swim_pool(atoi(argv[2]),atoi(argv[3]))); */
    /* } */
    /* else if (strcmp(argv[1],"swim_pool1")==0){ */
    /*   printf("#result = %d\n",  */
    /*          swim_pool1(atoi(argv[2]),atoi(argv[3]))); */
    /* } */
    /* else if (strcmp(argv[1],"schedule2p")==0){ */
    /*   printf("#result = %d\n", schedule2p(atoi(argv[2]))); */
    /* } */
    /* else if (strcmp(argv[1],"train_rm03")==0){ */
    /*   printf("#result = %d\n",  */
    /*          train_rm03(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),atoi(argv[5]),atoi(argv[6]))); */
    /* } */
    /* else if (strcmp(argv[1],"cars2p")==0){ */
    /*   printf("#result = %d\n", cars2p(atoi(argv[2]))); */
    /* } */
    /* else if (strcmp(argv[1],"cars3p")==0){ */
    /*   printf("#result = %d\n", cars3p(atoi(argv[2]))); */
    /* } */
    /* else if (strcmp(argv[1],"cars4p")==0){ */
    /*   printf("#result = %d\n", cars4p(atoi(argv[2]))); */
    /* } */
