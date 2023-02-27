import java.util.*;
public class MyLinkedList{
    @SuppressWarnings("unchecked")
    public static void main(String args[]){
	LinkedList ll = new LinkedList();
	ll.add("F");
	ll.add("B");
	ll.add("D");

	ll.addLast("Z");
	ll.addFirst("A");
	ll.add(1, "A2");

	System.out.println("ll " + ll);

	System.out.println("ll " + ll.removeLast());
	
    }

    
}
