void mainQ(int y) {
     int x = -50;
     int y0 = y;
     int x0 = x;

     while (x < 0) {
	  x = x + y;
	  y++;
     }

     //%%%traces: int y, int y0, int x0, int x
     printf("y %d y0 %d x0 %d x %d\n",y,y0,x0,x);
     //assert(y > 0);
}

int main(int argc, char *argv[]) {
     mainQ(atoi(argv[1]));
     return 0;
}
