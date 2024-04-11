import java.util.*;

public abstract class Term{

     List<String>typs;
     
     Term(List<String> mtyps){
	  assert(typs.size() >= 1);
	  typs = mtyps;
     }

     public String get_otyp(){return typs.get(typs.size() - 1);}
     abstract boolean is_instantiated();
}




