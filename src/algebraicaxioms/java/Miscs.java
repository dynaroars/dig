import com.google.common.collect.Collections2;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Sets;
import com.google.common.collect.Sets.SetView;
import com.google.common.collect.Range;
import com.google.common.primitives.Ints;
import java.util.*;
import java.util.stream.IntStream;
import java.util.stream.Collectors;
public class Miscs{

     public static void pause(String msg){
	  try{
	       if (msg != null){
		    System.out.println(msg);
	       }
	       System.in.read();
	  }
	  catch (java.io.IOException e){
	  }
     }
     
     @SuppressWarnings("unchecked")
     public static void main(String args[]){
	  System.out.println(new HashSet<Integer>().hashCode()); 
	  List<List<Set<Integer>>> rs ;
	  ImmutableSet<Integer> nodes;

	  nodes = ImmutableSet.of(0,1);
	  System.out.println(nodes);
	  System.out.println(gen_parts(nodes, 1));
	  //System.out.println(gen_parts(nodes, 3, false).size());
	  
	  // nodes = ImmutableSet.of(0,1,2);
	  // System.out.println(gen_parts(nodes, 2, false).size());
	  // System.out.println(gen_parts(nodes, 3, false).size());
	  // System.out.println(gen_parts(nodes, 3, false));
	  // //System.out.println(gen_parts(nodes, 3, true).size());	  

	  // nodes = ImmutableSet.of(1,2,3,4);	  
	  // System.out.println(gen_parts(nodes, 2, false).size());
	  // int siz = 7;
	  // rs = gen_parts(nodes, siz, false);
	  // System.out.println(rs.size());
	  // rs = gen_parts(nodes, siz, true);
	  // System.out.println(rs.size());

	  // nodes = ImmutableSet.of(1,2,3,4,5);
	  // rs = gen_parts(nodes, 4, false);
	  // System.out.println(rs.size());
	  
	  nodes = ImmutableSet.of(1,2,3,4,5,6,7,8,9,10);
	  rs = gen_parts(nodes, 4);
	  System.out.println(rs.size());
	  
	  //System.out.println(rs);
	  // for (Set<Set<Integer>> set : rs){
	  //      System.out.println(set);
	  // }

	  //ImmutableMap
	  
     }

     public static List<Integer> range(int start, int end){
	  return IntStream.range(start, end).boxed().collect(Collectors.toList());
     }

     public static List<Integer> range(int end){
	  return IntStream.range(0, end).boxed().collect(Collectors.toList());
     }

     private static Set<List<Integer>> cartesianProduct(Set<Integer> set, int repeat){
	  assert (repeat > 0);
	  List<Set<Integer>> list = new ArrayList<Set<Integer>>();
	  for (int i: range(repeat)) list.add(set);
	  return Sets.cartesianProduct(list);
     }

     public static Set<List<Integer>> gen_args(int n){
	  assert(n >= 0);

	  Set<List<Integer>> rs = new HashSet<List<Integer>>();
	  if (n <= 0) return rs;

	  List<Integer> myrange = range(n);
	  Set<List<Integer>> combs =
	       cartesianProduct(myrange.
				stream().
				collect(Collectors.toSet()), n);
	
	  List<List<Integer>> perms =
	       Collections2.orderedPermutations(myrange)
	       .stream()
	       .filter(perm -> !perm.equals(myrange))  //ignore 0,1,2,..
	       .collect(Collectors.toList());
	    
	  List<Integer> zeros =
	       new ArrayList<Integer>(Collections.nCopies(n, 0));
	  
	  rs.add(zeros);
	
	  Set<List<Integer>> cache = new HashSet<List<Integer>>();
	  for (List<Integer> comb : combs){
	       //comb with similar elemes, e.g., 1 1 1 is redued to 0 0 0 
	       if (Sets.newHashSet(comb).size() == 1) continue;
	    
	       if (!cache.contains(comb)){
		    rs.add(comb); cache.add(comb);
		
		    for (List<Integer> perm: perms){
			 /* permutate((0,1,2,3),(0,2,3,1)) == (0, 2, 3, 1)
			    permutate((2,2,1), (0,2,1)) == (1, 1, 2)
			    permutate((2,3,1,3,3), (3,4,1,0,2)) == (1, 0, 4, 0, 0)   
			 */
			 List<Integer> p = comb
			      .stream()
			      .map(e -> perm.get(e))
			      .collect(Collectors.toList());
			 cache.add(p);
		    }
	       }
	  }
	  return rs;
     }


     public static List<List<Set<Integer>>>gen_parts_rec(
	  Set<Integer> nodes, int k,
	  Map<List<Integer>, List<List<Set<Integer>>>>cache){

	  assert (k >= 0);

	  //System.out.println(String.format("%s, %s, %s",nodes,k,is_commute));
	  List<Integer> key = new ArrayList<Integer>(nodes);
	  Collections.sort(key);
	  key.add(k); 

	  if (cache.containsKey(key)){
	       return cache.get(key);
	  }
	  
	  List<List<Set<Integer>>> rs = new ArrayList<List<Set<Integer>>>();
	  if (nodes.isEmpty()) {
	       List<Set<Integer>>emptyl = new ArrayList<Set<Integer>>();
	       for (int dk : range(k)) emptyl.add(new HashSet<Integer>());
	       rs.add(emptyl);
	       return rs;
	  }
	  if (k == 0){ //return Empty List
	  }
	  else{
	       for (Set<Integer> g: Sets.powerSet(nodes)){

		    Set<Integer> rest = nodes.stream()
			 .filter(node -> !g.contains(node))
			 .collect(Collectors.toSet());
		    
		    List<List<Set<Integer>>> prest =
			 gen_parts_rec(rest, k-1, cache);
		    
		    for (List<Set<Integer>>p : prest){
			 List<Set<Integer>>union = new ArrayList<Set<Integer>>();
			 union.add(g); union.addAll(p);
			 rs.add(union);
		    }
	       }
	  }

	  cache.put(key, rs);
	  return cache.get(key);
     }

     public static List<List<Set<Integer>>>
     gen_parts(Set<Integer> nodes, int k){
     	  if (nodes.isEmpty() && k==0 ){
     	       return new ArrayList<List<Set<Integer>>>();
     	  }else{
	       Map<List<Integer>, List<List<Set<Integer>>>> mcache =
		    new HashMap<List<Integer>, List<List<Set<Integer>>>>();
	       List<List<Set<Integer>>> rs = gen_parts_rec(nodes, k, mcache);
	       return rs;
	  }
     }
	  
}
