java -jar antlr-4.4-complete.jar -o java/gen/za/co/twyst/GA144/assembler/antlr -package za.co.twyst.GA144.assembler.antlr F18A.g4 
javac -classpath antlr-4.4-complete.jar -d java/bin java/gen/za/co/twyst/GA144/assembler/antlr/*.java
cd java/bin
java -classpath .:../../antlr-4.4-complete.jar org.antlr.v4.runtime.misc.TestRig za.co.twyst.GA144.assembler.antlr.F18A program ../../ANTLR.asm
cd -
