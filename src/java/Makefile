JFLAGS = -cp asm-all-5.2.jar
JAVAC = /home/SHARED/Devel/JAVA/java8/bin/javac
default:
	$(JAVAC) $(JFLAGS) MyConst.java PrintInstr.java JPFInstr.java Instrument.java CollectInfo.java 	

classes: $(CLASSES:.java=.class)

clean:
	$(RM) *.class

