import java.util.*;

public class StackExample{
   public static void main(String args[]){
   // creating stack
   Stack st = new Stack();
   Stack stRef = st;

   st.push("Java");
   st.push("Source");
   stRef.push("code");
      
   // removing top object
   System.out.println("Removed object is: "+st.pop());
      
   // elements after remove
   System.out.println("Elements after remove: "+st);
   }    
}
