public class StrnCopy {
    public static void vtrace1(int q, int r, int a, int b, int x, int y){}
    public static void vtrace2(int q, int r, int a, int b, int x, int y){}
    public static void vtrace3(int x, int y, int q, int r){}

    public static void main (String[] args) {}
     

    public static int mainQ_cohendiv(int n, int siz) {

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
	

    }
