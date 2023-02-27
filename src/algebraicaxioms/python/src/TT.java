import java.util.*;
public class TT{
    public static void main(String args[]){
        System.out.println(f_0_0_0());
	System.out.println(f_1_0_0());
	System.out.println(f_2_0_0());
	System.out.println(f_2_1_0());
    }
     
    private static boolean f_0_0_0(){
            
	try{return (t_0_0_0_0() && t_0_0_0_1() && t_0_0_0_2() && t_0_0_0_3() && t_0_0_0_4() && t_0_0_0_5() && t_0_0_0_6() && t_0_0_0_7() && t_0_0_0_8() && t_0_0_0_9());}
	catch(EmptyStackException e){return false;}
	catch(java.util.NoSuchElementException e){return false;}
	catch(java.lang.IndexOutOfBoundsException e){return false;}
            
    }
        
        
    //testing bool_0 = empty(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_0(){
        boolean bool_00 = false;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = 22;
	Stack_00.push(int_00);
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_1(){
        boolean bool_00 = true;
	int []Stack_00_col = {-16};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = 7;
	Stack_00.push(int_00);
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_2(){
        boolean bool_00 = true;
	int []Stack_00_col = {19,-17,13};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -2;
	Stack_00.push(int_00);
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_3(){
        boolean bool_00 = true;
	int []Stack_00_col = {-17};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -3;
	Stack_00.push(int_00);
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_4(){
        boolean bool_00 = true;
	int []Stack_00_col = {3,41,23,38};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -12;
	Stack_00.push(int_00);
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_5(){
        boolean bool_00 = false;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = 30;
	Stack_00.push(int_00);
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_6(){
        boolean bool_00 = false;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = 36;
	Stack_00.push(int_00);
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_7(){
        boolean bool_00 = false;
	int []Stack_00_col = {-13,-24,43,1,19};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -23;
	Stack_00.push(int_00);
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_8(){
        boolean bool_00 = false;
	int []Stack_00_col = {-1,-38,-29,8};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = 12;
	Stack_00.push(int_00);
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_9(){
        boolean bool_00 = true;
	int []Stack_00_col = {-42,-30,11,-40,32};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -31;
	Stack_00.push(int_00);
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        
        

    private static boolean f_1_0_0(){
            
	try{return (t_1_0_0_0() && t_1_0_0_1() && t_1_0_0_2() && t_1_0_0_3() && t_1_0_0_4() && t_1_0_0_5() && t_1_0_0_6() && t_1_0_0_7() && t_1_0_0_8() && t_1_0_0_9());}
	catch(EmptyStackException e){return false;}
	catch(java.util.NoSuchElementException e){return false;}
	catch(java.lang.IndexOutOfBoundsException e){return false;}
            
    }
        
        
    //testing bool_0 = empty(pop(push(Stack_0, int_0)))
    @SuppressWarnings("unchecked")
    private static boolean t_1_0_0_0(){
        boolean bool_00 = false;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -2;
	Stack_00.push(int_00);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(pop(push(Stack_0, int_0)))
    @SuppressWarnings("unchecked")
    private static boolean t_1_0_0_1(){
        boolean bool_00 = true;
	int []Stack_00_col = {-35,-22};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = 11;
	Stack_00.push(int_00);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(pop(push(Stack_0, int_0)))
    @SuppressWarnings("unchecked")
    private static boolean t_1_0_0_2(){
        boolean bool_00 = true;
	int []Stack_00_col = {-42,44,50};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -21;
	Stack_00.push(int_00);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(pop(push(Stack_0, int_0)))
    @SuppressWarnings("unchecked")
    private static boolean t_1_0_0_3(){
        boolean bool_00 = false;
	int []Stack_00_col = {18,36,-32,23};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -12;
	Stack_00.push(int_00);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(pop(push(Stack_0, int_0)))
    @SuppressWarnings("unchecked")
    private static boolean t_1_0_0_4(){
        boolean bool_00 = true;
	int []Stack_00_col = {-5,-43};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = 45;
	Stack_00.push(int_00);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(pop(push(Stack_0, int_0)))
    @SuppressWarnings("unchecked")
    private static boolean t_1_0_0_5(){
        boolean bool_00 = true;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -11;
	Stack_00.push(int_00);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(pop(push(Stack_0, int_0)))
    @SuppressWarnings("unchecked")
    private static boolean t_1_0_0_6(){
        boolean bool_00 = false;
	int []Stack_00_col = {-41,33,18,-5};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -1;
	Stack_00.push(int_00);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(pop(push(Stack_0, int_0)))
    @SuppressWarnings("unchecked")
    private static boolean t_1_0_0_7(){
        boolean bool_00 = false;
	int []Stack_00_col = {27,20};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -40;
	Stack_00.push(int_00);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(pop(push(Stack_0, int_0)))
    @SuppressWarnings("unchecked")
    private static boolean t_1_0_0_8(){
        boolean bool_00 = false;
	int []Stack_00_col = {16,-27};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = 25;
	Stack_00.push(int_00);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        

    //testing bool_0 = empty(pop(push(Stack_0, int_0)))
    @SuppressWarnings("unchecked")
    private static boolean t_1_0_0_9(){
        boolean bool_00 = true;
	int []Stack_00_col = {-41,-28,-16,14};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_00 = -34;
	Stack_00.push(int_00);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean empty_ret0 = (boolean)(Stack_00.empty());
	boolean eq_ret0 = (boolean)(bool_00 == empty_ret0);
	return eq_ret0;
    }
        
        

    private static boolean f_2_0_0(){
            
	try{return (t_2_0_0_0() && t_2_0_0_1() && t_2_0_0_2() && t_2_0_0_3() && t_2_0_0_4() && t_2_0_0_5() && t_2_0_0_6() && t_2_0_0_7() && t_2_0_0_8() && t_2_0_0_9());}
	catch(EmptyStackException e){return false;}
	catch(java.util.NoSuchElementException e){return false;}
	catch(java.lang.IndexOutOfBoundsException e){return false;}
            
    }
        
        
    //testing int_0 = pop(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_2_0_0_0(){
        int int_00 = -24;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_01 = -24;
	Stack_00.push(int_01);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_2_0_0_1(){
        int int_00 = 32;
	int []Stack_00_col = {26,44,15,-41};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_01 = 32;
	Stack_00.push(int_01);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_2_0_0_2(){
        int int_00 = 19;
	int []Stack_00_col = {-5,20};
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
    private static boolean t_2_0_0_3(){
        int int_00 = -8;
	int []Stack_00_col = {44,-9,49,37,33};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_01 = -8;
	Stack_00.push(int_01);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_2_0_0_4(){
        int int_00 = -15;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_01 = -15;
	Stack_00.push(int_01);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_2_0_0_5(){
        int int_00 = -45;
	int []Stack_00_col = {-33,-14,20,19};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_01 = -45;
	Stack_00.push(int_01);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_2_0_0_6(){
        int int_00 = 16;
	int []Stack_00_col = {37};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_01 = 16;
	Stack_00.push(int_01);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_2_0_0_7(){
        int int_00 = 41;
	int []Stack_00_col = {48,-4,-42,-22};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_01 = 41;
	Stack_00.push(int_01);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_2_0_0_8(){
        int int_00 = 6;
	int []Stack_00_col = {13,-3,-3,-39,48};
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
    private static boolean t_2_0_0_9(){
        int int_00 = -9;
	int []Stack_00_col = {-8,-30};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_01 = -9;
	Stack_00.push(int_01);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        
        

    private static boolean f_2_1_0(){
            
	try{return (t_2_1_0_0() && t_2_1_0_1() && t_2_1_0_2() && t_2_1_0_3() && t_2_1_0_4() && t_2_1_0_5() && t_2_1_0_6() && t_2_1_0_7() && t_2_1_0_8() && t_2_1_0_9());}
	catch(EmptyStackException e){return false;}
	catch(java.util.NoSuchElementException e){return false;}
	catch(java.lang.IndexOutOfBoundsException e){return false;}
            
    }
        
        
    //testing int_0 = pop(push(Stack_0, int_1))
    @SuppressWarnings("unchecked")
    private static boolean t_2_1_0_0(){
        int int_00 = -26;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_10 = 24;
	Stack_00.push(int_10);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_1))
    @SuppressWarnings("unchecked")
    private static boolean t_2_1_0_1(){
        int int_00 = 39;
	int []Stack_00_col = {-28,-3,41};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_10 = 25;
	Stack_00.push(int_10);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_1))
    @SuppressWarnings("unchecked")
    private static boolean t_2_1_0_2(){
        int int_00 = -6;
	int []Stack_00_col = {-8,-48,-31,42};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_10 = 28;
	Stack_00.push(int_10);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_1))
    @SuppressWarnings("unchecked")
    private static boolean t_2_1_0_3(){
        int int_00 = -14;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_10 = 39;
	Stack_00.push(int_10);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_1))
    @SuppressWarnings("unchecked")
    private static boolean t_2_1_0_4(){
        int int_00 = 49;
	int []Stack_00_col = {-16,34};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_10 = -32;
	Stack_00.push(int_10);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_1))
    @SuppressWarnings("unchecked")
    private static boolean t_2_1_0_5(){
        int int_00 = 33;
	int []Stack_00_col = {-9,50,-7,48};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_10 = 42;
	Stack_00.push(int_10);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_1))
    @SuppressWarnings("unchecked")
    private static boolean t_2_1_0_6(){
        int int_00 = 25;
	int []Stack_00_col = {21,0,-41};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_10 = -19;
	Stack_00.push(int_10);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_1))
    @SuppressWarnings("unchecked")
    private static boolean t_2_1_0_7(){
        int int_00 = 37;
	int []Stack_00_col = {-20,-8};
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
    private static boolean t_2_1_0_8(){
        int int_00 = -1;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_10 = -9;
	Stack_00.push(int_10);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_1))
    @SuppressWarnings("unchecked")
    private static boolean t_2_1_0_9(){
        int int_00 = 9;
	int []Stack_00_col = {30,-26,-2,42,37};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_10 = -30;
	Stack_00.push(int_10);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        
        
}
