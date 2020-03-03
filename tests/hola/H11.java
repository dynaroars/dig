public class H11 {

    public static void vtrace(int j, int x, int n){}
    public static void main (String[] args) {}

    public static void mainQ(int n){
	int j = 0;
	int x = 100;
	int i = 0;

	for (i = 0; i < x; i++) {
	    j = j + 2;
	}

	//tvn:  need to add input here otherwise lack of traces
	vtrace(j, x, n);
	//assert(j == 2 * x);	  
    }


}

