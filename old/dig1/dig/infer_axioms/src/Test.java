
import java.util.*;
public class Test{
    public static void main(String args[]){
        System.out.println(f_0_0_0());
System.out.println(f_0_1_0());
     }
     
        private static boolean f_0_0_0(){
            
            try{return (t_0_0_0_0() && t_0_0_0_1() && t_0_0_0_2() && t_0_0_0_3() && t_0_0_0_4() && t_0_0_0_5() && t_0_0_0_6() && t_0_0_0_7() && t_0_0_0_8() && t_0_0_0_9());}
            catch(EmptyStackException e){return false;}
            catch(java.util.NoSuchElementException e){return false;}
            catch(java.lang.IndexOutOfBoundsException e){return false;}
            
        }
        
        
        //testing int_0 = pop(push(Stack_0, int_0))
        @SuppressWarnings("unchecked")
        private static boolean t_0_0_0_0(){
        int int_00 = 11;
    int []Stack_00_col = {};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_01 = 11;
    Stack_00.push(int_01);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_0))
        @SuppressWarnings("unchecked")
        private static boolean t_0_0_0_1(){
        int int_00 = 1;
    int []Stack_00_col = {45};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_01 = 1;
    Stack_00.push(int_01);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_0))
        @SuppressWarnings("unchecked")
        private static boolean t_0_0_0_2(){
        int int_00 = 20;
    int []Stack_00_col = {35,-28,-4};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_01 = 20;
    Stack_00.push(int_01);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_0))
        @SuppressWarnings("unchecked")
        private static boolean t_0_0_0_3(){
        int int_00 = 6;
    int []Stack_00_col = {49,36,44,-3,-39};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_01 = 6;
    Stack_00.push(int_01);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_0))
        @SuppressWarnings("unchecked")
        private static boolean t_0_0_0_4(){
        int int_00 = 0;
    int []Stack_00_col = {15,-37,49,-30,16};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_01 = 0;
    Stack_00.push(int_01);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_0))
        @SuppressWarnings("unchecked")
        private static boolean t_0_0_0_5(){
        int int_00 = -47;
    int []Stack_00_col = {12,43};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_01 = -47;
    Stack_00.push(int_01);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_0))
        @SuppressWarnings("unchecked")
        private static boolean t_0_0_0_6(){
        int int_00 = 28;
    int []Stack_00_col = {-45,-11,40};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_01 = 28;
    Stack_00.push(int_01);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_0))
        @SuppressWarnings("unchecked")
        private static boolean t_0_0_0_7(){
        int int_00 = -29;
    int []Stack_00_col = {24,0,32,-29};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_01 = -29;
    Stack_00.push(int_01);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_0))
        @SuppressWarnings("unchecked")
        private static boolean t_0_0_0_8(){
        int int_00 = 19;
    int []Stack_00_col = {-21,-49,48,-25};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_01 = 19;
    Stack_00.push(int_01);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_0))
        @SuppressWarnings("unchecked")
        private static boolean t_0_0_0_9(){
        int int_00 = 23;
    int []Stack_00_col = {-21,1,15,-6};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_01 = 23;
    Stack_00.push(int_01);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        
        

        private static boolean f_0_1_0(){
            
            try{return (t_0_1_0_0() && t_0_1_0_1() && t_0_1_0_2() && t_0_1_0_3() && t_0_1_0_4() && t_0_1_0_5() && t_0_1_0_6() && t_0_1_0_7() && t_0_1_0_8() && t_0_1_0_9());}
            catch(EmptyStackException e){return false;}
            catch(java.util.NoSuchElementException e){return false;}
            catch(java.lang.IndexOutOfBoundsException e){return false;}
            
        }
        
        
        //testing int_0 = pop(push(Stack_0, int_1))
        @SuppressWarnings("unchecked")
        private static boolean t_0_1_0_0(){
        int int_00 = 8;
    int []Stack_00_col = {};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_10 = -16;
    Stack_00.push(int_10);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_1))
        @SuppressWarnings("unchecked")
        private static boolean t_0_1_0_1(){
        int int_00 = 50;
    int []Stack_00_col = {20,27,43,-50,-1};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_10 = 44;
    Stack_00.push(int_10);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_1))
        @SuppressWarnings("unchecked")
        private static boolean t_0_1_0_2(){
        int int_00 = -24;
    int []Stack_00_col = {-34,16,49,21};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_10 = 4;
    Stack_00.push(int_10);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_1))
        @SuppressWarnings("unchecked")
        private static boolean t_0_1_0_3(){
        int int_00 = 11;
    int []Stack_00_col = {};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_10 = -4;
    Stack_00.push(int_10);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_1))
        @SuppressWarnings("unchecked")
        private static boolean t_0_1_0_4(){
        int int_00 = 12;
    int []Stack_00_col = {20,-25,14,2};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_10 = -5;
    Stack_00.push(int_10);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_1))
        @SuppressWarnings("unchecked")
        private static boolean t_0_1_0_5(){
        int int_00 = 19;
    int []Stack_00_col = {-6,-50,18};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_10 = 29;
    Stack_00.push(int_10);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_1))
        @SuppressWarnings("unchecked")
        private static boolean t_0_1_0_6(){
        int int_00 = -21;
    int []Stack_00_col = {-8,8,26,-47};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_10 = 31;
    Stack_00.push(int_10);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_1))
        @SuppressWarnings("unchecked")
        private static boolean t_0_1_0_7(){
        int int_00 = 24;
    int []Stack_00_col = {20};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_10 = -27;
    Stack_00.push(int_10);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_1))
        @SuppressWarnings("unchecked")
        private static boolean t_0_1_0_8(){
        int int_00 = 20;
    int []Stack_00_col = {};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_10 = -18;
    Stack_00.push(int_10);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        

        //testing int_0 = pop(push(Stack_0, int_1))
        @SuppressWarnings("unchecked")
        private static boolean t_0_1_0_9(){
        int int_00 = 36;
    int []Stack_00_col = {};
Stack Stack_00 = new Stack();
for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    int int_10 = -41;
    Stack_00.push(int_10);
    int pop_ret0 = (int)(Stack_00.pop());
    boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
            return eq_ret0;
        }
        
        
    }