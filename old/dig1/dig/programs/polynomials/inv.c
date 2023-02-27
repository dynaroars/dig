/* ThanhVu Nguyen */
/* benchmark programs for  DIG */

/* Linux: compile with gcc inv.c -o inv -lm -gdwarf-2 */


#include "inv_common.h"
#include "inv_nla.h"


#include "inv_seeded_bugs.h"
#include "inv_allamigeon.h"

//experimental
#include "inv_nla_rec.h"
#include "inv_arith_algs2.h"
#include "inv_knuth.h"
#include "inv_mccune.h"
#include "inv_miscs.h"
#include "inv_arrays.h"
#include "inv_lgc.h"
#include "inv_nec.h"
#include "inv_dk.h"

/***** Driver *****/
int main(int argc, char **argv){
  int i ;
  srand((unsigned int)(time(0)));

  init_tracker();

  printf("#cmd: ");
  for (i=0; i < argc ; ++i){
    printf("%s ", argv[i]);
  }
  printf("\n");


  if (argc >= 2 ){
    if (strcmp(argv[1],"myisprime")==0){
      printf("#result = %d\n", myisprime(atoi(argv[2])));
    }
    else if (strcmp(argv[1],"randrange_f")==0){
      for(i=0; i < 100 ; ++i){
        printf("#result = %g\n", 
               randrange_f(atof(argv[2]),atof(argv[3]),TRUE));
      }
    }
    else if (driver_nla(argv)){} //inv_nla.h
    else if (driver_nla_others(argv)){} //inv_nla.h
    else if (strcmp(argv[1],"sqrt1rec")==0){
      printf("#result = %d\n", sqrt1rec(atoi(argv[2])));
    }
    else if (driver_mccune(argv)){} //inv_mccune.h
    else if (driver_lgc(argv)){} //inv_lgc.h
    else if(driver_nec(argv)){} //inv_nec.h
    

    else if (strcmp(argv[1],"daikon_test")==0){
      printf("#result = %d\n", daikon_test(atoi(argv[2])));
    }
    else if (driver_knuth(argc,argv)){} //inv_knuth.h
    
    /* else if (strcmp(argv[1],"myheapsort")==0){ */
    /*   printf("#result = %d\n", myheapsort(atoi(argv[2]))); */
    /* } */


    //AES 
    /* else if (strcmp(argv[1],"xor")==0){ */
    /*   printf("#results = %d\n",xor(atoi(argv[2]),atoi(argv[3]))); */
    /* } */

    /* else if (strcmp(argv[1],"xor")==0){ */
    /*   printf("#results = %d\n",xor(atoi(argv[2]),atoi(argv[3]))); */
    /* } */

    else if (driver_miscs(argv)){} //inv_miscs.h
    
    //BUGS
    else if (strcmp(argv[1],"euclidex2_bug")==0){
      printf("#result = %d\n", 
             euclidex2_bug(atoi(argv[2]),atoi(argv[3])));
    }
  
    else if(driver_dk(argv)){}//inv_dk.h
    else{
      printf("unrecognized program \'%s\'\n", argv[1]);
    }

  }
  
  
  
  clean_tracker();
  return 0;
}

