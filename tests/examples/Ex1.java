public class Ex1 {
    public static void vtrace1_post(int m, int tCtr){}
    public static void vtrace0(int m, int n){}
    public static void main (String[] args) {}
    public static int mainQ(int m, int n){
	// if (m > 1 && n <= 20 && 2*n*n + 3*m == 62){
	//     vtrace0(m,n);
	// }
	
	int tCtr = 0;
	if (m < 0){
	    tCtr = -10;
	}
	else if (m == 0){
	    tCtr = 5;
	}
	else{ // m > 0
	    tCtr = m  + 7;
	}
	vtrace1_post(m, tCtr);
	    
	return 0;
    }
}

