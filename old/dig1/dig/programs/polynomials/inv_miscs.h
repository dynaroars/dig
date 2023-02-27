//From Static Analysis of Digital Filters presentation by Jérôme Feret http://www.di.ens.fr/~feret
float high_filter1(float V,float T){
  //Static Analysis of Digital Filters presentation by Jérôme Feret 
  //page 5
  //question: what's T? 
  
  
  float E0 = 0.0;
  float E1 = 0.0;
  float S  = 0.0;
  while (V >= 0) {
    E0 = randrange_p(-1.0,1.0,1,2);// E0 = [−1;1];
    printf("E0 = %f\n",E0);
    if (T >= 0.0) {
      S = 0.0;
    }
    else {
      S = 0.999 * S + E0 - E1;
      }
    E1 = E0;
  }

  return 0.0;
}


float high_filter2(float V, float T){

  float E0 = 0.0;
  float E1 = 0.0; 
  float E2 = 0.0; 
  float S0 = 0.0; 
  float S1 = 0.0; 
  float S2 = 0.0;
  
 
  while (V >= 0) {
    E0 = randrange_p(-1.0,1.0,1,2);// E0 = [−1;1];
    printf("E0 = %f\n",E0);
    if (T >= 0) {
      S0 = E0;
      S1 = E0;
      E1 = E0;
    }
    else {
      S0 = 1.5 * S1 - 0.7 * S2 + 0.5 * E0 - 0.7 * E1 + 0.4 * E2;
    }

    E2 = E1;
    E1 = E0;
    S2 = S1;
    S1 = S0;
    
  }

  return 0.0;
}

int driver_miscs(char **argv){
  if (strcmp(argv[1],"high_filter1")==0){
    printf("#results = %g\n",high_filter1(atof(argv[2]),atof(argv[3])));
    return 1;
  }
  else if (strcmp(argv[1],"high_filter2")==0){
    printf("#results = %g\n",high_filter2(atof(argv[2]),atof(argv[3])));
    return 1;
  }
  return 0;
}
