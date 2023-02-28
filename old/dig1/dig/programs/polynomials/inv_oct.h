/*
  Programs with Octagonal Invariants
  X + Y <= c
 */


// from The Octagon Abstract Domain, http://www.di.ens.fr/~mine/publi/article-mine-ast01.pdf


/* int rand_walk(const int M){ */
/*   const int m = 100; */
/*   int tab[2*m]; */
/*   int i,j; */
  
/*   for(i = -m ; i< m ; ++i){ */
/*     tab[i+m] = 0; */
/*   } */


/*   for (j = 0 ; j< M ; ++j){ */
/*     int a = 0;  */
/*     for (i = 0, i < m; ++i){ */
/*       if (rand_range(1,INCLUDE) == 0){ */
/* 	a = a + 1; */
/*       } */
/*       else: */
/* 	a = a - 1; */
/*     } */
/*     tab[a]=tab[a]+1;  */
/*   } */
/* } */

//from http://www.di.ens.fr/~mine/publi/article-mine-HOSC06.pdf

int rate_limitter(){
  int Y = 0;
  int X = 0, D = 0, S = 0, R = 0;
  while(1){
    X = randrange(-128,128,INCLUDE);
    D = randrange(0,16,INCLUDE);
    S = Y;
    R = X- S;
    Y = X;
    if(R <= -D){
      Y = S - D;
    }
    if (D <= R){
      Y = S + D;
    }
  }
  return Y;
}
