import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import com.google.common.primitives.Ints;
import java.util.HashSet;
import java.util.Set;
import java.util.List;
import java.util.Arrays;
import java.util.ArrayList;
public class T{

    @SuppressWarnings("unchecked")
    public static void main(String args[]){
	System.out.println("HIHI");
	// String [] arr = {"one","two","three"};	
	// Set<String> set = new HashSet<String>(Arrays.asList(arr));
	// System.out.println(set);
	
	int [] arr1 = {1,2,3,};
	Set<Integer>set = new HashSet<Integer>(Ints.asList(arr1));
	System.out.println(set);
	
	// Set<Set<Integer>> sets = Sets.powerSet(set);
	// System.out.println(sets);
	
	// for(Set<Integer> mset: sets){
	//     System.out.println(mset);
	// }


	Set<List<Integer>> sets = Sets.cartesianProduct(set);
	System.out.println(sets);

	List<Set<Integer>> list = new ArrayList<Set<Integer>>();
	list.add(set);
	list.add(set);

	System.out.println(list);
	Set<List<Integer>> sets1 = Sets.cartesianProduct(list);
	System.out.println(sets1);

	
    }
    
}
