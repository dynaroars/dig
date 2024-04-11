import java.util.*;

public class TestT{
    public static void main(String args[]){
        System.out.println(f_0_0_0());
	System.out.println(TestT1.f_0_1_0());
    }
     
    private static boolean f_0_0_0(){
            
	try{return (t_0_0_0_0() && t_0_0_0_1());}
	catch(EmptyStackException e){return false;}
	catch(java.util.NoSuchElementException e){return false;}
	catch(java.lang.IndexOutOfBoundsException e){return false;}
            
    }
        
        
    //testing int_0 = pop(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_0(){
        int int_00 = 50;
	int []Stack_00_col = {};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_01 = 50;
	Stack_00.push(int_01);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        

    //testing int_0 = pop(push(Stack_0, int_0))
    @SuppressWarnings("unchecked")
    private static boolean t_0_0_0_1(){
        int int_00 = -34;
	int []Stack_00_col = {3};
	Stack Stack_00 = new Stack();
	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
	int int_01 = -34;
	Stack_00.push(int_01);
	int pop_ret0 = (int)(Stack_00.pop());
	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
	return eq_ret0;
    }
        
        

    // private static boolean f_0_1_0(){
            
    // 	try{return (t_0_1_0_0() && t_0_1_0_1());}
    // 	catch(EmptyStackException e){return false;}
    // 	catch(java.util.NoSuchElementException e){return false;}
    // 	catch(java.lang.IndexOutOfBoundsException e){return false;}
            
    // }
        
        
    // //testing int_0 = pop(push(Stack_0, int_1))
    // @SuppressWarnings("unchecked")
    // private static boolean t_0_1_0_0(){
    //     int int_00 = -32;
    // 	int []Stack_00_col = {};
    // 	Stack Stack_00 = new Stack();
    // 	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    // 	int int_10 = -30;
    // 	Stack_00.push(int_10);
    // 	int pop_ret0 = (int)(Stack_00.pop());
    // 	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
    // 	return eq_ret0;
    // }
        

    // //testing int_0 = pop(push(Stack_0, int_1))
    // @SuppressWarnings("unchecked")
    // private static boolean t_0_1_0_1(){
    //     int int_00 = -38;
    // 	int []Stack_00_col = {32,23,39,23,-28};
    // 	Stack Stack_00 = new Stack();
    // 	for(int i = Stack_00_col.length-1; i>=0 ; --i) Stack_00.push(Stack_00_col[i]);
    // 	int int_10 = -14;
    // 	Stack_00.push(int_10);
    // 	int pop_ret0 = (int)(Stack_00.pop());
    // 	boolean eq_ret0 = (boolean)(int_00 == pop_ret0);
    // 	return eq_ret0;
    // }
        
        
}
