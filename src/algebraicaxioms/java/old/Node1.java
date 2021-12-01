import java.util.*;
public class Node{
     private String name = null;
     private List<String> typs = null; //typs
     private List<Node> children = null; //children
     
     //ctors
     Node(String name){
	  this.name = name;
     }

     //setters
     public void addTyp(String typ){
	  if (typs  == null){
	       typs = new ArrayList<String>();
	  }
	  typs.add(typ);
     }

     public void addChild(Node child){
	  if (children == null){
	       children = new ArrayList<Node>();
	  }
	  children.add(child);
     }

     //getters
     public int get_oTyp(){
	  return typs.get(typs.size() - 1);
     }

     //public
     public String toString(){
	  String s =  this.name;
	  if (children != null){
	       String cs = "";
	       for (Node c : children){
		    cs += c + ", ";
	       }
	       s = s + "(" + cs + ")";
	  }
	  return s;
     }


}
