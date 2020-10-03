public class H36 {

    public static void vtrace(int w, int z, int a, int b) {}
    public static void main (String[] args) {
	mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]),Integer.parseInt(args[3]));
    }

    public static void mainQ(int flag, int u1, int u2, int u3) {
	assert(u1 > 0 && u2 > 0 && u3 > 0);
	int a = 0;
	int b = 0;
	int j = 0;
	int w = 0;
	int x = 0;
	int y = 0;
	int z = 0;
	int i1 = 0;
	int i2 = 0;
	int i3 = 0;

	int i = 0;
	int k = 0;
	int c = 0;
	int d = 0;

	while (i1 < u1) {
	    i1++;
	    i = z;
	    j = w;
	    k = 0;

	    while (i < j) {
		k++;
		i++;
	    }

	    x = z;
	    y = k;

	    if (x % 2 == 1) {
		x++;
		y--;
	    }

	    i2 = 0;
	    while (i2 < u2) {
		i2++;
		if (x % 2 == 0) {
		    x += 2;
		    y -= 2;
		} else {
		    x--;
		    y--;
		}
	    }

	    z++;
	    w = x + y + 1;
	}

	c = 0;
	d = 0;
	i3 = 0;
	while (i3 < u3) {
	    i3++;
	    c++;
	    d++;
	    if (flag != 0) {
		a++;
		b++;
	    } else {
		a += c;
		b += d;
	    }
	}

	vtrace(w, z, a, b);
	//assert(w >= z && a - b == 0);

    }
}
