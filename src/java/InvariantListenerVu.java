package gov.nasa.jpf.symbc;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.DynamicElementInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.LocalVarInfo;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Types;
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.report.Publisher;
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;

import java.io.PrintWriter;
import static java.lang.System.out;
import java.util.stream.Collectors;


public class InvariantListenerVu
     extends PropertyListenerAdapter implements PublisherExtension {

     public InvariantListenerVu (Config conf, JPF jpf) {}

     private ChoiceGenerator<?>  findPCChoiceGenerator(VM vm){
	  ChoiceGenerator <?>cg = vm.getChoiceGenerator();
	  if (!(cg instanceof PCChoiceGenerator)){
	       ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();
	       while(!(prev_cg == null ||  prev_cg instanceof PCChoiceGenerator)){
		    prev_cg = prev_cg.getPreviousChoiceGenerator();
	       }
	       cg = prev_cg;
	  }
	  return cg;
     }

     private  PathCondition getPC(ChoiceGenerator<?> cg){
	  if ((cg instanceof PCChoiceGenerator) &&
	      ((PCChoiceGenerator) cg).getCurrentPC() != null){
	       return ((PCChoiceGenerator) cg).getCurrentPC();
	  }else{
	       return null;
	  }
     }

     @Override
     public void propertyViolated (Search search){
	  VM vm = search.getVM();
	  ChoiceGenerator<?> cg = findPCChoiceGenerator(vm);
	  PathCondition pc = getPC(cg);
	  if (pc == null) return;
	  String loc = vm.getInstruction().getFilePos();
	  out.printf("%s: Assertion Violated\n%s",loc, pc.toString());
     }

     @Override
     public void instructionExecuted(
	  VM vm, ThreadInfo currentThread,
	  Instruction nextInstruction,
	  Instruction executedInstruction){

	  if (!vm.getSystemState().isIgnored()) {
	       Instruction insn = executedInstruction;
	       ThreadInfo ti = currentThread;
	       Config conf = vm.getConfig();

	       if (insn instanceof JVMInvokeInstruction) {
		    JVMInvokeInstruction md = (JVMInvokeInstruction) insn;
		    String methodName = md.getInvokedMethodName();
		    Object[] argsValues = md.getArgumentValues(ti);
		    int numberOfArgs = argsValues.length;

		    MethodInfo mi = md.getInvokedMethod();
		    ClassInfo ci = mi.getClassInfo();
		    String className = ci.getName();

		    //String shortName = methodName;
		    //String longName = mi.getLongName();

		    if(methodName.contains("vtrace")){
			 //int loc = (Integer) md.getArgumentValue("loc", ti);
			 StackFrame sf = ti.getTopFrame();
			 out.printf("********** START **********\n");
			 out.printf("loc: %s\n", methodName);
			 printPCs(conf, vm, mi);
			 printLocals(mi, sf);
			 out.printf("********** END **********\n");
		    }
		    
	       }
	       
	  }
     }

     private void printLocals(MethodInfo mi, StackFrame sf){
	  StackFrame mysf = sf.getPrevious();
	  LocalVarInfo[] lvi = mysf.getLocalVars();
	       
	  String lvs = "";
	  for (LocalVarInfo lv: lvi){
	       lvs = lvs +  lv.getType() + " " + lv.getName() + ", ";
	  }
	  out.printf("vars: %s\n", lvs);

	  for (int i = 0; i < lvi.length; ++i){
	       Expression exp = (Expression)mysf.getLocalAttr(i);	       
	       if (exp != null){
	  	    out.printf("SYM: %s = %s\n", lvi[i].getName(), exp.toString());
	       }
	       else{
	  	    int slotIdx = lvi[i].getSlotIndex();
		    
	  	    String val = "CON: " + lvi[i].getName() + " = ";
	  	    if (lvi[i].getType() == "int"){
	  		 val = val + mysf.getSlot(slotIdx);
	  	    }
	  	    else if (lvi[i].getType() == "float"){
	  		 val = val + mysf.getFloatLocalVariable(slotIdx);
	  	    }
	  	    else{
	  		 out.printf("I don't know how to deal with type %s\n", lvi[i].getType());
	  	    }
	  	    out.printf("%s\n", val);
	       }
		    
	  }
     }

     private void printPCs(Config conf, VM vm, MethodInfo mi){
	  Object[] argsValues = mi.getArgumentLocalVars();
	  if (argsValues == null) return;

	  ChoiceGenerator<?> cg = findPCChoiceGenerator(vm);
	  PathCondition pc = getPC(cg);
	  if (pc != null){
	       out.printf("pc: %s\n", pc.toString());
	  }
     }

     @Override
     public void publishFinished (Publisher publisher) {
	  PrintWriter pw = publisher.getOut();
	  publisher.publishTopicStart("Summary");
     }
}

