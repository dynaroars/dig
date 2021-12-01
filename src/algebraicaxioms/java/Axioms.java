import com.google.common.collect.Sets;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

abstract class Term{
     String name;     
     private String otyp = null;
     private Set<Term> _terms = null;
     private Set<Arg> _args = null;
     private Set<Fun> _funs = null;
     private Map<String, Integer> _atCount = null; //argument typ counter
     private List<Map<String, List<Integer>>> _argMaps = null;
     void setOtyp(String otyp){this.otyp = otyp;}
     String getOtyp(){return this.otyp;}
     abstract boolean is_instantiated();

     //recursion utils
     private void _add(Term t, Set<Term> s){
	  s.add(t);
	  if (!(t instanceof Arg)){
	       for(Term c: ((Fun) t).getChildren()) _add(c, s);
	  }
     }
     private Set<Term> getTerms(){
	  if (this._terms == null){
	       Set<Term> s = new HashSet<Term>();
	       _add(this, s);
	       this._terms = s;
	  }
	  return this._terms;
     }
     
     private Set<Arg> getArgs(){
	  if (this._args == null){
	       this._args = getTerms().stream()
		    .filter(t -> t instanceof Arg)
		    .map(t-> (Arg)t)
		    .collect(Collectors.toSet());
	  }
	  return this._args;
     }
     private Set<Fun> getFuns(){
	  if (this._funs == null){
	       this._funs =  getTerms().stream()
		    .filter(t -> !(t instanceof Arg))
		    .map(t-> (Fun)t)
		    .collect(Collectors.toSet());
	  }
	  return this._funs;
     }

     private Map<String, Integer> getArgTypsCount(){
	  if (this._atCount == null){
	       Map<String, Integer> hm = new HashMap<String, Integer>();
	       for (Arg c : getArgs()){
		    String typ = c.getOtyp();
		    if (hm.containsKey(typ))
			 hm.put(typ, hm.get(typ) + 1);
		    else
			 hm.put(typ, 1);
	       }
	       this._atCount = hm;
	  }
	  return this._atCount;
     }

     List<Map<String, List<Integer>>> genArgs(){
	  if (this._argMaps == null){
	       Map<String, Integer> thm = this.getArgTypsCount();
	       List<String> keys = new ArrayList<String>(thm.keySet());
	       List<Set<List<Integer>>> values = keys.stream()
		    .map(typ -> Miscs.gen_args(thm.get(typ)))
		    .collect(Collectors.toList());
	       
	       Set<List<List<Integer>>> combs = Sets.cartesianProduct(values);
	       
	       List<Map<String, List<Integer>>> ms =
		    new ArrayList<Map<String, List<Integer>>>();
	       
	       for (List<List<Integer>> comb: combs){
		    Map<String, List<Integer>> m =
			 IntStream.range(0, keys.size()).boxed()
			 .collect(Collectors.toMap(i -> keys.get(i), i -> comb.get(i)));
		    ms.add(m);
	       }

	       this._argMaps = ms;
	  }
	  
	  return this._argMaps;
     }

     abstract Term instantiate(Map<String, Integer> ctrMap,
			       Map<String, List<Integer>> typMap);

     /*
       Instantiate leaf to real arguments, e.g., 
       f(int,int) to  f(int_0, int_1) or f(int_0, int_0)
     */
     public Term instantiate(Map<String, List<Integer>> argMap){
	  assert(!is_instantiated());
	  Map<String, Integer> m =
	       argMap.keySet().stream()
	       .collect(Collectors.toMap(typ -> typ, typ -> 0));
	  return this.instantiate(m, argMap);
     }

     
}

class Arg extends Term{
     
     private int id = -1;
     Arg(String otyp, int id){
	  setOtyp(otyp);
	  setId(id);
     }
     Arg(String otyp){
	  setOtyp(otyp);
	  setId(-1);
     }

     public String toString(){
	  String s = getOtyp();
          if (id != -1) s = s + "_" + id;
	  return s;
     }

     @Override
     public int hashCode() {
     	  return Objects.hash(getOtyp(), getId());
     }

     @Override
     public boolean equals(Object o) {
	  if (o == this) {return true;}
	  if (!(o instanceof Arg)) {return false;}
	  Arg a = (Arg) o;
	  return getOtyp() == a.getOtyp() && getId() == a.getId();
     }

     public void setId(int id){this.id = id;}
     public int getId(){return this.id;}
     boolean is_instantiated(){return id >= 0;}

     Arg instantiate(Map<String, Integer> ctrMap,
		      Map<String, List<Integer>> typMap){
	  String otyp = this.getOtyp();
	  int idx = ctrMap.get(otyp);
	  ctrMap.put(otyp, idx+1);
	  int val = typMap.get(otyp).get(idx);
	  return new Arg(otyp, val);
     }
}

class Fun extends Term{
     List<String> ityps = null;     
     private List<Term> children = null;
     
     Fun(String name){this.name = name;}
     public String getName(){return this.name;}

     //@Override
     public int hashCode1(){
	  final int prime = 31;
	  int result = 1;

	  if (getChildren() != null){
	       for( String s : strings ){
		    result = result * prime + s.hashCode();
	       }
	  }
	       
	  return Objects.hash(getName(), getId());
     }

     @Override
     public boolean equals(Object o){
     	  if (o == this) {return true;}
     	  if (!(o instanceof Fun)) {return false;}
     	  Fun a = (Fun) o;
     	  if (getName() != a.getName()){return false;}
     	  /*(a == null => b == null) && (a!= null => b!=null)
     	    (a != null or b==null) && (a==null or b !=null)
     	   */
     	  if (!((getItyps() != null || a.getItyps() == null)
     		&& (getItyps() == null || a.getItyps() != null))){
	       System.out.println("ne0");
	       return false;
	  }
	  
     	  if (!((getChildren() != null || a.getChildren() == null)
     		&& (getChildren() == null || a.getChildren() != null))){
	       System.out.println("ne1");	       
	       return false;
	  }

	  if (getItyps() != null){
	       if (getItyps().size() != a.getItyps().size()) return false;
	       for (int i = 0 ; i < getItyps().size() ; ++i){
		    if (getItyps().get(i) != a.getItyps().get(i)) {
			 System.out.println("ne2");	       			 
			 return false;
		    }
	       }
	  }

	  if (getChildren() != null){
	       if (getChildren().size() != a.getChildren().size()) return false;
	       for (int i = 0 ; i < getChildren().size() ; ++i){
		    if (getChildren().get(i).equals(a.getChildren().get(i))){
			 System.out.println("ne3");
			 return false;
		    }
	       }
	  }
	  
	  return true;
     }
     Fun instantiate(Map<String, Integer> ctrMap,
		     Map<String, List<Integer>> typMap){
	  List<Term> mchildren = new ArrayList<Term>();

	  Fun f = new Fun(this.name);
	  for (Term t : this.getChildren()){
	       Term c = t.instantiate(ctrMap, typMap);
	       f.addChild(c);
	  }
	  return f;
     }
     
     public List<String> getItyps(){return ityps;}
     public List<Term> getChildren(){return children;}
     
     //setters
     public void addItyp(String typ){
	  if (ityps == null) ityps = new ArrayList<String>();
	  ityps.add(typ);
     }

     public void addChild(Term child){
	  if (children == null)children = new ArrayList<Term>();
	  children.add(child);
     }

     //helpers
     public Fun construct(List<Fun> children){
	  List<Term> mchildren = new ArrayList<Term>();
	  for (int i = 0 ; i < children.size() ; ++i){
	       Term c = children.get(i);
	       if (c == null){mchildren.add(new Arg(this.ityps.get(i)));}
	       else{mchildren.add(c);}
	  }

	  Fun f = new Fun(this.name);
	  for (Term mc : mchildren) f.addChild(mc);
	  return f;
     }

     public String str_of_decl(){
          String s = ityps == null ? "" : MyUtils.str_of(ityps);
	  return String.format("%s %s(%s)", getOtyp(), name, s);
     }

     public String toString(){
          String s = children == null ? "" : MyUtils.str_of(children);
	  return String.format("%s(%s)", name, s);
     }

     //trees
     private static Set<Integer> gt(List<Fun> trees, Set<Integer> idxs,
				    Map<Set<Integer>, Set<Integer>> hm){
	  if (hm.containsKey(idxs)){
	       return hm.get(idxs);
	  }
	  Set<Integer> rs = new HashSet<Integer>();
	  if (idxs.isEmpty()){
	       rs.add(-1);
	  }
	  else{
	       for(int root: idxs){
		    Set<Integer> rest = idxs.stream()
			 .filter(idx -> idx != root)
			 .collect(Collectors.toSet());
		    
		    List<List<Set<Integer>>> parts = 
			 Miscs.gen_parts(rest, trees.get(root).ityps.size());
		    
		    for(List<Set<Integer>> part : parts){
			 List<Set<Integer>> ctrees =
			      part.stream()
			      .map(p -> gt(trees, p, hm))
			      .collect(Collectors.toList());
			 
			 Set<List<Integer>> prod = Sets.cartesianProduct(ctrees);
			 for (List<Integer> cidxs:prod){
			      
			      List<Fun> children = 
				   cidxs.stream()
				   .map(idx -> idx == -1 ? null : trees.get(idx))
				   .collect(Collectors.toList());
			      
			      Fun tree = trees.get(root).construct(children);
			      rs.add(trees.size()); trees.add(tree);
			 }
		    }
	       }
	  }
	  assert (!hm.containsKey(idxs));
	  hm.put(idxs, rs);
	  return rs;
     }
     
     /*Enumerate all possible tree structures from trees.
       I.e., each structure consist of exactly |trees| trees*/
     public static Set<Fun> gen_trees(Set<Fun> trees){

	  List<Fun> ltrees = trees.stream().collect(Collectors.toList());
	  
	  Set<Integer> idxs =
	       Miscs.range(ltrees.size()).stream().collect(Collectors.toSet());
	  
	  Fun.gt(ltrees, idxs, new HashMap <Set<Integer>, Set<Integer>>());
	  
	  Set<Fun> rs = Miscs.range(ltrees.size()).stream()
	       .filter(i -> !idxs.contains(i))
	       .map(i -> ltrees.get(i)).collect(Collectors.toSet());
	  return rs;
     }

     /*Enumerate all possible tree structures from trees by calling 
       gen_trees on each subset of trees of size 1 to |trees|*/
     public static Set<Fun> gen_trees_all(Set<Fun> funs){
	  Set<Fun> eqfuns = new HashSet<Fun>();
	  for(Set<Fun> ps : Sets.powerSet(funs)){
	       if (ps.size() == 0) continue;
	       Set<Fun> ts = gen_trees(ps);
	       eqfuns.addAll(ts);
	  }
	  return eqfuns;
     }
     //trees

     boolean is_instantiated(){
	  return children == null ? false:
	       children.stream().allMatch(c -> c.is_instantiated());
     }

     Set<Fun> instantiate(){
	  assert (!is_instantiated());
	  Set<Fun> axioms = genArgs().stream()
	       .map(args -> (Fun)instantiate(args))
	       .collect(Collectors.toSet());
	  return axioms;
     }
}

class EqFun extends Fun{
     static final String name = "eq";
     EqFun(){super(name);}
     
     Term lhs(){return this.getChildren().get(0);}
     Term rhs(){return this.getChildren().get(1);}     

     static Set<Fun> generate(Set<Fun> funs){
	  Set<Fun> mfuns;
	  mfuns = gen_trees_all(funs);
	  
	  
	  return mfuns;
     }

}


public class Axioms{
     public static void main(String args[]){
	  Arg a1 = new Arg("string", 0);
	  Arg a2 = new Arg("string", 0);
	  Arg a3 = new Arg("string", 1);	  
	  System.out.println(a1.equals(a2));
	  System.out.println(a1.equals(a3));	  
	  System.out.println(a1.hashCode() + " " + a2.hashCode() + " " + a3.hashCode());
	  System.out.println(Objects.hash(a1) + " " + Objects.hash(a2)
			     + " " + Objects.hash(a3));
	  Set<Arg> margs = new HashSet<Arg>();
	  margs.add(a1);
	  margs.add(a2);
	  margs.add(a3);	  
	  System.out.println(margs);
		  
	  Fun pop = new Fun("pop");
	  pop.setOtyp("int");
	  pop.addItyp("array");
	  System.out.println(pop.str_of_decl());

	  Fun pop1 = new Fun("pop");
	  pop1.setOtyp("int");
	  pop1.addItyp("array");
	  System.out.println(pop.str_of_decl());

	  Fun push = new Fun("push");
	  push.setOtyp("void");
	  push.addItyp("array");
	  push.addItyp("int");
	  System.out.println(push.str_of_decl());

	  System.out.println(pop.equals(pop1));
	  Miscs.pause("hi");
	  System.out.println(pop.equals(push));	  
	  System.out.println(pop.hashCode() + " " + pop1.hashCode()
			     + " " + push.hashCode());
	  System.out.println(Objects.hash(pop) + " " + Objects.hash(pop1)
			     + " " + Objects.hash(push));
	  
	  Set<Fun> funs = new HashSet<Fun>();
	  funs.add(pop);
	  funs.add(push);
	  funs.add(pop1);
	  System.out.println(funs);

	  //search(funs, 10, 5);

	  // Arg arr1 = new Arg("array");
	  // List<Term> children = new ArrayList<Term>();
	  // children.add(arr1);
	  // Fun pop1 = pop.construct(children);
	  // System.out.println(pop1);
     }

     static void search(Set<Fun> funs, int ntests, int max_nfuns){
	  Set<Fun> mfuns = funs;
	  
	  System.out.println(mfuns.size() + " funs");
	  System.out.println(MyUtils.str_of(mfuns, "\n"));

	  //generate equations
	  mfuns = EqFun.generate(mfuns);
	  System.out.println(mfuns.size() + " eqfuns");
	  System.out.println(MyUtils.str_of(mfuns, "\n"));	  
	  
	  //instantiate
	  // Set<Fun> ifuns = new HashSet<Fun>();
	  // for (Fun f: mfuns) ifuns.addAll(f.instantiate());
	  // System.out.println(ifuns.size() + " instantiated funs");
	  // System.out.println(MyUtils.str_of(ifuns, "\n"));	  

	  
	  
     }
}


class MyUtils{
     static String str_of(Collection c, String delim){
	  String s = (String)c.stream()
	       .map(t -> t.toString())
	       .collect(Collectors.joining(delim));
	  return s;
     }

     static String str_of(Collection c){
	  return str_of(c, ", ");
     }
     
}
