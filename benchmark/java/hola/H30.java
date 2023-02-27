
public class H30 {
    public static void vtrace(int n, int i, int c){}
    
    public static void main (String[] args) {}

    public static void mainQ(int n){
	int i = 0;
	int c = 0;

	while (i < 1000) {
	    c = c + i;
	    i = i + 1;
	}

	vtrace(n, i, c);
	//assert(c >= 0);
    }


}

