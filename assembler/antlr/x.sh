java -jar ~/Development/tools/antlr/antlr-4.4-complete.jar -o java/gen/za/co/twyst/GA144/assembler/antlr -package za.co.twyst.GA144.assembler.antlr F18A.g4 
javac -d java/bin java/gen/za/co/twyst/GA144/assembler/antlr/*.java
cd java/bin
java -classpath .:$CLASSPATH org.antlr.v4.runtime.misc.TestRig za.co.twyst.GA144.assembler.antlr.F18A prog -gui ../../ANTLR.asm
cd -
