public class PLDI09_Ex6 {
    public static void vtrace1(int n, int m, int i, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ(int n, int m){
	assert (0 <= n);
	assert (0 <= m);
	int i = 0;
	int j = 0;
	int k = 0;
	int tCtr = 0;

	while(i++ < n){
	    //note remove if(nondet)
	    tCtr++;
	    if (i % 2 !=0){//odd
		while(j++ < m){tCtr++;}
	    }
	    else{
		while(k++ < m){tCtr++;}
	    }
	}
	vtrace1(n, m, i, tCtr);
	return 0;
    }

}

