import java.util.*;

public class Arg extends Term{
     int id;
     
     Arg(int mid,  List<String> typs){
	  super(typs);
	  assert(id >= 0);
	  id = mid;
     }

     Arg(List<String> typs){this(-1, typs);}

     //copy ctor
     Arg(Arg a){this(a.id, new ArrayList<String>(a.typs));}
     
     
     public String toString(){
	  String s = get_otyp();
	  if (is_instantiated()) s += "_" + id;
	  return s;
     }
     public boolean is_instantiated(){return id > -1;}

     public int get_id(){return id;}
     
     
}
