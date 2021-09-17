import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.util.List;
import java.util.HashMap;
import java.util.Map;

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

public class Instrument {
     public static void main(final String args[]) throws Exception {
	  FileInputStream is = new FileInputStream(args[0]);
	  
	  ClassReader cr;
	  ClassWriter cw;
	  ClassVisitor cv;

	  /*Collect Info*/
	  HashMap<String, HashMap<String, MethodNode>> hmm =
	       new HashMap<String, HashMap<String, MethodNode>>();

	  cr = new ClassReader(is);
	  cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES);
	  cv = new CollectClassVisitor(cw, hmm);
	  cr.accept(cv, 0);

	  
	  /*Do Instrumentation*/
	  FileOutputStream of;
	       
	  /*Add print statements*/
	  cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES);
	  cv = new PrintClassVisitor(cw, hmm);
	  cr.accept(cv, 0);
	  of = new FileOutputStream(args[1]);
	  of.write(cw.toByteArray());
	  of.close();
	 
	  /*JPF instrumentation*/
	  cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES);
	  cv = new JPFClassVisitor(cw, hmm);
	  cr.accept(cv, 0);
	  of = new FileOutputStream(args[2]);
	  of.write(cw.toByteArray());
	  of.close();
     }
}
