public class Oct1 {
    public static void vtrace0(int m, int x, int z){}
    public static void main (String[] args) {}
    public static int mainQ(int m, int n){
	int x = m;
	int y = n+7;
	int z = n;
	if (-5 <= m && -4 <= -x + z && -x + z <= 6){
	    vtrace0(m,x,z);
	}
	
	// int tCtr = 0;
	// if (m < 0){
	//     tCtr = -10;
	// }
	// else if (m == 0){
	//     tCtr = 5;
	// }
	// else{ // m > 0
	//     tCtr = m  + 7;
	// }
	//vtrace1_post(m, tCtr);
	    
	return 0;
    }
}

/*
1. z <= 16  OK
2. x <= 10 OK
3. m <= 10  OK
4. m - z <= 4 OK 
5. m - x <= 0  OK
6. m + z <= 26 OK
7. m + x <= 20 OK
8. -z <= 9 OK
9. -x <= 5 OK
10. -m <= 5
11. -m - z <= 14  OK
12. -m - x <= 10 OK
13. -m + z <= 6 OK
14. -m + x <= 0  OK 



z <= 16
-m + x <= 0
m <= 10
m - x <= 0
-m -z <= 14
m - z <= 4
m + z <= 26
x <= 10
-x <= 5
-z <= 9
m + x <= 20
-m + z <= 6
-m - x <= 10
-m <= 5
*/
