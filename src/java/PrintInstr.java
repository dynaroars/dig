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


class PrintClassVisitor extends ClassVisitor implements Opcodes{
     HashMap<String, MethodNode> hm;     
     HashMap<String, HashMap<String, MethodNode>> hmm;          
     String cname;
     public PrintClassVisitor(final ClassVisitor cv,
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
	  
	  if (name.startsWith("vtrace")){
	       /*add System.out.println(methodname + " " + x + " " + y ... )
		 to trace(T x, T y, ..)
	       */
	       mv.visitFieldInsn(
	       	    GETSTATIC,
	       	    "java/lang/System", "out", "Ljava/io/PrintStream;");
		    
	       mv.visitTypeInsn(NEW, MyConst.jlStringBuilder);
	       mv.visitInsn(DUP);
	       mv.visitMethodInsn(
	       	    INVOKESPECIAL,
	       	    MyConst.jlStringBuilder, "<init>", "()V", false);
		    
	       mv.visitLdcInsn(name + ": ");
	       mv.visitMethodInsn(
	       	    INVOKEVIRTUAL, MyConst.jlStringBuilder, "append",
	       	    "(Ljava/lang/String;)L"+MyConst.jlStringBuilder+";", false);
	       
	       MethodNode m = this.hm.get(name);
	       
	       Type[] typs = Type.getArgumentTypes(m.desc);
	       int idx = 0;
	       for (int i = 0; i < typs.length; ++i){
		    Type t = typs[i];

		    if (t.equals(Type.INT_TYPE)){
			 mv.visitVarInsn(ILOAD, idx);
			 idx += 1;
			 mv.visitMethodInsn(
			      INVOKEVIRTUAL, MyConst.jlStringBuilder, "append",
			      "(I)L"+MyConst.jlStringBuilder+";", false);
		    }
		    else if(t.equals(Type.DOUBLE_TYPE)){
			 mv.visitVarInsn(DLOAD, idx);
			 idx += 2;
			 mv.visitMethodInsn(
			      INVOKEVIRTUAL, MyConst.jlStringBuilder, "append",
			      "(D)L"+MyConst.jlStringBuilder+";", false);
		    }
		    else if(t.equals(Type.FLOAT_TYPE)){
			 mv.visitVarInsn(FLOAD, idx);
			 idx += 1;
			 mv.visitMethodInsn(
			      INVOKEVIRTUAL, MyConst.jlStringBuilder, "append",
			      "(F)L"+MyConst.jlStringBuilder+";", false);
		    }
		    else{
			 System.out.println("Didn't consider " + t);
		    }
		    mv.visitLdcInsn(" ");
		    mv.visitMethodInsn(
			 INVOKEVIRTUAL, MyConst.jlStringBuilder, "append",
			 "(Ljava/lang/String;)L"+MyConst.jlStringBuilder+";", false);
		    
	       }
	       
	       mv.visitMethodInsn(
	       	    INVOKEVIRTUAL,
	       	    MyConst.jlStringBuilder, "toString",
	       	    "()Ljava/lang/String;", false);
	       mv.visitMethodInsn(
	       	    INVOKEVIRTUAL,
	       	    "java/io/PrintStream", "println",
	       	    "(Ljava/lang/String;)V", false);
	  }
	  else if(name.equals("main")){
	       MethodNode mainQ = null;
	       for (Map.Entry<String, MethodNode> e: this.hm.entrySet()){
	       	    if (e.getKey().startsWith("mainQ")){
	       		 mainQ = e.getValue();
	       		 break;
	       	    }
	       }
	       assert(mainQ != null);
	       Type[] typs = Type.getArgumentTypes(mainQ.desc);
	       for (int i = 0 ; i < typs.length; ++i){
	       	    mv.visitVarInsn(ALOAD, 0);
	       	    switch(i){
	       	    case 0: mv.visitInsn(ICONST_0); break;
	       	    case 1: mv.visitInsn(ICONST_1); break;
	       	    case 2: mv.visitInsn(ICONST_2); break;
	       	    case 3: mv.visitInsn(ICONST_3); break;
	       	    case 4: mv.visitInsn(ICONST_4); break;
	       	    default:
	       		 System.out.println("Didn't consider " + typs.length + "args");
	       	    }
	       	    mv.visitInsn(AALOAD);

		    Type t = typs[i];
		    
		    if (t.equals(Type.INT_TYPE)){
			 mv.visitMethodInsn(
			      INVOKESTATIC, MyConst.jlInteger, "parseInt",
			      "(Ljava/lang/String;)I", false);
		    }
		    else if (t.equals(Type.DOUBLE_TYPE)){
			 mv.visitMethodInsn(
			      INVOKESTATIC, MyConst.jlDouble, "parseDouble",
			      "(Ljava/lang/String;)D", false);
		    }
		    else if (t.equals(Type.FLOAT_TYPE)){
			 mv.visitMethodInsn(
			      INVOKESTATIC, MyConst.jlFloat, "parseFloat",
			      "(Ljava/lang/String;)F", false);
		    }
		    
		    else{
			 System.out.println("Didn't consider " + t);
		    }
		    
	       }
	       mv.visitMethodInsn(INVOKESTATIC, this.cname, mainQ.name,
	       			  mainQ.desc, false);
	       Type rtyp = Type.getReturnType(mainQ.desc);
	       if (!rtyp.equals(Type.VOID_TYPE)){
		    mv.visitInsn(POP);
	       }
	       
	  }
	  
	  return mv;
     }

}


