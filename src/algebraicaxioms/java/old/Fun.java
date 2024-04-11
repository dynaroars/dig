import com.google.common.collect.Sets;
import java.util.*;
import java.util.stream.Collectors;

public class Fun extends Term{
     String name;
     List<String> ityps;     
     List<Term> children;
     List<Integer> se_idxs;
     
     Fun(String mname,
	 List<String> typs,
	 List<Term> mchildren,
	 List<Integer> mse_idxs){
	  
	  super(typs);

	  assert(typs.size() >= 1);
	  assert(mchildren.size() == typs.size()-1);

	  name = mname;
	  children = mchildren;
	  se_idxs = mse_idxs;
	       
	  ityps = new ArrayList<String>();
	  for(int i = 0; i < children.size(); ++i){
	       ityps.add(typs.get(i));
	  }
     }
     //copy constructor
     Fun (Fun f){
	  this(f.name,
	       new ArrayList<String>(f.typs),
	       new ArrayList<Term>(f.children),  //todo: is this correct ?
	       new ArrayList<Integer>(f.se_idxs));
     }


     public String toString(){
	  String s = children.stream()
	       .map(c -> c.toString())
	       .collect(Collectors.joining(", "));
	  
	  return String.format("%s(%s)", name, s);
     }

     boolean is_instantiated(){
	  for(Term c : children){if (!(c.is_instantiated()))return false;}
	  return true;
     }

     private void construct(List<Term> mchildren){
	  assert (mchildren.size() == this.children.size());

	  List<Term> children = new ArrayList<Term>();
	  for (int i = 0; i < mchildren.size(); ++i){
	       Term c = mchildren.get(i);
	       
	       if (c instanceof Arg){
		    Arg myc = (Arg)c;
		    int id = myc.get_id();
		    
		    List<String>typs = new ArrayList<String>();
		    String otyp = myc.get_otyp();
		    
		    if (otyp == null) typs.add(this.ityps.get(i));
		    else typs.add(otyp);
		    
		    children.add(new Arg(id, typs));
	       }else{
		    children.add(new Fun((Fun)c));
	       }
	       
	  }
     }

     public static Set<Integer> gen_trees(Set<Integer> treeIdxs, List<Fun> trees){
	  Set<Integer> rs = new HashSet<Integer>();

	  if (!trees.isEmpty()){
	       for (int root: treeIdxs){
                    Set<Integer> rest = treeIdxs.stream()
			 .filter(idx -> idx != root)
			 .collect(Collectors.toSet());
		    List<ArrayList<Set<Integer>>> parts =
			 Miscs.gen_parts(rest, trees.get(root).children.size());

		    for (List<Set<Integer>> part: parts){
			 
			 List<Set<Integer>> ctrees =
			      new ArrayList<Set<Integer>>();
			 
			 for (Set<Integer> p: part){
			      Set<Integer> ctrees_ = gen_trees(p, trees);
			      ctrees.add(ctrees_);
			 }
			 Set<List<Integer>> cprods = Sets.cartesianProduct(ctrees);
			 
			 
		    }
	       }
	  }
	  
	  return rs;
	  
     }


}



