public class PLDI09_Fig4_1 {
    public static void 	vtrace_post(int id, int n, int tCtr){}
    public static void main (String[] args) {
    }

    public static int mainQ(int id, int n){
	assert (id >= 0);
	assert (n > id);
	int tmp = id + 1;
	int tCtr = 0;

	while(tmp != id){
	    if (tmp <= n) {
		tmp = tmp + 1;
	    }else{
		tmp=0;
	    }
	    tCtr++;
	}
	vtrace_post(id, n, tCtr);
	//dig2: n - t + 1 == 0, -id <= 0, id - n <= -1 
	return 0;
    }
}

