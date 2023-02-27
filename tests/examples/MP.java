public class MP {
    public static void vtrace1(int x, int y, int z){}
    public static void main (String[] args) {}
    public static int mainQ(int x, int y){
	int z = 0;
	if (x >= y){
	    z = x;
	}
	else{
	    z = y;
	}

	//if(x>=y, x==z, y==z)
	vtrace1(x, y, z);
	return 0;
    }
}

