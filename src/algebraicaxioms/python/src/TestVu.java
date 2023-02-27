
import java.util.*;
public class TestVu{
    public static void main(String args[]){
        t_0_2_0_3();
     }
     

    //isEmpty(concat(str_0,str_1)) = isEmpty(str_0)
    @SuppressWarnings("unchecked")
    private static boolean t_0_2_0_3(){
        String str_00 = "";
	String str_10 = "two";
	String new_str = str_00.concat(str_10);
	System.out.println("str_00" + new_str);
	boolean isEmpty_ret0 = (boolean)(str_00.isEmpty());
	System.out.println("isEmpty_ret0 =" + isEmpty_ret0);	
	String str_01 = "";
	boolean isEmpty_ret1 = (boolean)(str_01.isEmpty());
	System.out.println("isEmpty_ret1 =" + isEmpty_ret1);	
	boolean eq_ret0 = (boolean)(isEmpty_ret0 == isEmpty_ret1);
	System.out.println("eq_ret0 =" + eq_ret0);
	return eq_ret0;
    }
    
        
}
