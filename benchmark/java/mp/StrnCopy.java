public class StrnCopy {
    public static void vtrace1(int q, int r, int a, int b, int x, int y){}
    public static void vtrace2(int q, int r, int a, int b, int x, int y){}
    public static void vtrace3(int x, int y, int q, int r){}

    public static void main (String[] args) {}
     

    public static int mainQ_cohendiv(int n, int siz) {

	
	
	assert(!(n <= ls) || ld >= n);
	assert(!(n > ls) || ld == ls);

	vtrace1(n,siz,ls,ld)

    }


    /*  Orig C code
int mylen(const int k,int arr[], const int arr_siz){
  int i = 0;
  for(; i < arr_siz; ++i){
    if (arr[i] == '\0'){return i;}
  }

  return arr_siz - 1 ;
  //return randrange_i(k, arr_siz - 1, INCLUDE);
}


void mk_rand_list(int arr[], const int arr_siz){
  int i = 0 ;
  for (;i< arr_siz; ++i){arr[i] = ' ';}


  int null_idx = randrange_i(0, arr_siz -1, INCLUDE);
  arr[null_idx]='\0';
}

	assert (1 <= siz);
	assert (0 <= n);
	assert (n <= siz-1);
	
	int src[siz];
	int dst[siz];
	mk_rand_list(src, siz);
	mk_rand_list(dst, siz);
  
	int i = 0;
	while(i < n && src[i] != '\0'){
	    dst[i] = src[i];
	    i = i + 1;
	}
	while(i < n){
	    dst[i] = '\0';
	    i = i + 1;
	}

	int ls = mylen(n,src,siz);
	int ld = mylen(n,dst,siz);

	printf("l_post: n s d\n");
	printf("l_post: %d %d %d\n", n, ls, ld);

	//inv
	assert(!(n <= ls) || ld >= n);
	assert(!(n > ls) || ld == ls);

	/*
	  DIG:
	  11: lambda d,n,s: d >= min(n,s)  ***
	  12: lambda d,n,s: s >= min(d,n)  ***
	*/
	

     */
