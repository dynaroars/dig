import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;

import java.io.FileInputStream;

public class JParser{
     
     public static void main(String[] args) throws Exception{
	  if (args.length < 1){
	       System.err.println("Enter Java filename ..");
	       System.exit(1);
	  }
	  String javaFile = args[0];
	  
	  System.out.println("Parsing " + javaFile);
	  FileInputStream in = new FileInputStream(javaFile);
	  CompilationUnit cu = JavaParser.parse(in);
	  System.out.println(cu.toString());
    }
}
