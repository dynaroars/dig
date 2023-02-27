public class Fermat1A {
    public static void vtraces1(int A, int R, int u, int v, int r, int i, int j, int k){}
    public static void vtraces2(int A, int R, int u, int v, int r, int i, int j, int k){}
    public static void vtraces3(int A, int R, int u, int v, int r, int i, int j, int k){}
    // public static void vtraces2(int A, int R, int u, int v, int r, int r0, int v0, int c1){}
    // public static void vtraces3(int A, int R, int u, int v, int r, int r1, int u1, int c2){}    
    public static void main (String[] args) {}
    
    public static int mainQ(int A, int R){
        assert((R - 1) * (R - 1) < A);
        //assert(A <= R*R);
        assert(A % 2 ==1); 
        
        int u, v, r;
        u = 2*R + 1;
        v = 1;
        r = R*R - A;
        
        int i =0;
        int j = 0;
        int k = 0;
        // int r0 =0; 
        // int r1 =0;
        // int v0 = 0;
        // int u1 = 0;
        while (true){
            //assert(4*(A+r) == u*u-v*v-2*u+2*v);
            vtraces1(A, R, u, v, r, i, j, k);
            
            if(!(r!=0)) break;
            i++;

            //c1 = 0;
            //r0 = r;
            //v0 = v;
            while (true){
                //assert(4*(A+r) == u*u-v*v-2*u+2*v);
                vtraces2(A, R, u, v, r, i, j, k); 
                //vtraces2(A, R, u, v, r, r0, v0, c1);
                if(!(r>0 )) break;
                j++;
                r=r-v;
                v=v+2;
            }
            
            //c2 = 0;
            //r1 = r;
            //u1 = u;
            while (true){
                //assert(4*(A+r) == u*u-v*v-2*u+2*v);
                vtraces3(A, R, u, v, r, i, j, k);
                //vtraces3(A, R, u, v, r, r1, u1, c2);
                if(!(r<0 )) break;
                k++;
                r=r+u;
                u=u+2;
            }
            
        }
        return (u-v)/2;
    }
}
