JFLAGS = -cp asm-all-5.2.jar

default:
	javac $(JFLAGS) MyConst.java PrintInstr.java JPFInstr.java Instrument.java CollectInfo.java 	


classes: $(CLASSES:.java=.class)

clean:
	$(RM) *.class

