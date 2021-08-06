import java.util.List;
import java.util.HashMap;
//import java.util.Map;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;

import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Label;
import org.objectweb.asm.Type;

import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.LocalVariableNode;
import org.objectweb.asm.tree.LabelNode;

class CollectClassVisitor extends ClassVisitor implements Opcodes{
     HashMap<String, MethodNode> hm;
     HashMap<String, HashMap<String, MethodNode>> hmm;     
     
     public CollectClassVisitor(
	  final ClassVisitor cv,
	  HashMap<String, HashMap<String, MethodNode>> hmm){
	  
	  super(ASM5, cv);
	  this.hmm = hmm;
     }
     @Override
     public void visit(int version, int access, String name,
		       String sig, String superName, String[] interfaces){
	  assert(!this.hmm.containsKey(name));
	  this.hm = new HashMap<String, MethodNode>();
	  this.hmm.put(name, this.hm);
	  super.visit(version, access, name, sig, superName, interfaces);
     }
     
     @Override
     public MethodVisitor visitMethod(final int access, final String name,
				      final String desc, final String sig,
				      final String[] exs){

	  assert(!this.hm.containsKey(name));
	  this.hm.put(name, new MethodNode(access, name, desc, sig, exs));

	  MethodVisitor mv = super.visitMethod(access, name, desc, sig, exs);
	  return  mv == null ? null : new CollectMethodVisitor(mv, name, this.hm);
     }

     @SuppressWarnings("unchecked")
     @Override     
     public void visitEnd(){
	  super.visitEnd();

	  for(HashMap.Entry<String, HashMap<String, MethodNode>> e1:
		   hmm.entrySet()){
	       HashMap<String, MethodNode> hm = e1.getValue();

	       for(HashMap.Entry<String, MethodNode> e2: hm.entrySet()){
		    String methodName = e2.getKey();
		    MethodNode mn = e2.getValue();
		    if(methodName.startsWith("vtrace")){
			 String s = methodName + "; ";
			 for(Object v: mn.localVariables){
			      LocalVariableNode v_ = (LocalVariableNode)v;
			      s += v_.desc + " " + v_.name + "; ";
			 }
			 System.out.println(s);
		    }
		    else if (methodName.contains("mainQ")){
			 //hackish way to get the param names of mainQ
			 String s = methodName + "; ";
			 Type[] typs = Type.getArgumentTypes(mn.desc);
			 List<LocalVariableNode> vs = mn.localVariables;
			 assert(typs.length <= vs.size());
			 for(int i = 0; i < typs.length; ++i){
			      s += vs.get(i).desc + " " + vs.get(i).name + "; ";
			 }
			 System.out.println(s);
		    }
		    
	       }
	  }
     }
}

class CollectMethodVisitor extends MethodVisitor implements Opcodes{
     String mname;
     HashMap<String, MethodNode> hm;
     
     public CollectMethodVisitor(final MethodVisitor mv,
				 String mname,
				 HashMap<String, MethodNode> hm){
	  super(ASM5, mv);
	  this.mname = mname;	  
	  this.hm = hm;
     }
     
     @SuppressWarnings("unchecked")
     @Override
     public void visitLocalVariable(String name, String desc, String sig,
				    Label start, Label end, int index){
	  LocalVariableNode n = new LocalVariableNode(
	       name, desc, sig, new LabelNode(start), new LabelNode(end), index);
	  List<LocalVariableNode> l = this.hm.get(this.mname).localVariables;
	  l.add(n);
     }
}



