import java.util.List;
import java.util.HashMap;
import java.util.Map;

import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Label;
import org.objectweb.asm.Type;

import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.LocalVariableNode;
import org.objectweb.asm.tree.LabelNode;


class JPFClassVisitor extends ClassVisitor implements Opcodes{
     HashMap<String, MethodNode> hm;     
     HashMap<String, HashMap<String, MethodNode>> hmm;          
     String cname;
     public JPFClassVisitor(final ClassVisitor cv,
			      HashMap<String, HashMap<String, MethodNode>> hmm
			      ){
	  super(ASM5, cv);
	  this.hmm = hmm;
     }

     @Override
     public void visit(int version, int access, String name,
		       String sig, String superName, String[] interfaces){
	  this.cname = name;
	  assert(this.hmm.containsKey(name));
	  this.hm = this.hmm.get(name);
	  super.visit(version, access, name, sig, superName, interfaces);
     }
     
     @Override
     public MethodVisitor visitMethod(final int access, final String name,
				      final String desc, final String sig,
				      final String[] exs){

	  MethodVisitor mv = cv.visitMethod(access, name, desc, sig, exs);
	  if(name.equals("main")){
	       MethodNode mainQ = null;
	       for (Map.Entry<String, MethodNode> e: this.hm.entrySet()){
		    if (e.getKey().startsWith("mainQ")){
			 mainQ = e.getValue();
			 break;
		    }
	       }
	       assert(mainQ != null);
	       Type[] typs = Type.getArgumentTypes(mainQ.desc);
	       for (Type t : typs){
		    if (t.equals(Type.INT_TYPE)){
			 mv.visitInsn(ICONST_1);
		    }
		    else if (t.equals(Type.DOUBLE_TYPE)){
			 mv.visitInsn(DCONST_1);
		    }
		    else if (t.equals(Type.FLOAT_TYPE)){
			 mv.visitInsn(FCONST_1);
		    }

		    else{
			 System.out.println("Didn't consider " + t);
		    }
		    
	       }
	       mv.visitMethodInsn(INVOKESTATIC, this.cname, 
				  mainQ.name, mainQ.desc, false);
	       Type rtyp = Type.getReturnType(mainQ.desc);
	       if (!rtyp.equals(Type.VOID_TYPE)){
		    mv.visitInsn(POP);
	       }
	       
	  }
	  return mv;
     }
}

