public class NoInput {
    public static void vtrace1(int x, int y, int z){}
    public static void main (String[] args) {}
    public static int mainQ(){
	int x = 0;
	int y = 0; 
	int z = 0;
	int ctr = 0;
	while(ctr < 20){
	    ctr++;
	    x++;
	    y = 2*x;
	    vtrace1(x, y, z);
	}
	return 0;
    }
}

