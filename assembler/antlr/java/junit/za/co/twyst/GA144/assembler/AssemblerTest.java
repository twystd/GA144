package za.co.twyst.GA144.assembler;

import static org.junit.Assert.*;

public class AssemblerTest {
	// UNIT TESTS 

    protected void test(String program,int[] assembly,int[] mask,boolean debug) throws Exception {
        test(new TestVector(program,assembly,mask),
             debug);
    }

    protected void test(TestVector vector) throws Exception {
        test(vector,false);
    }

	protected void test(TestVector[] vectors) throws Exception {
		test(vectors,false);
	}
	
	protected void test(TestVector[] vectors,boolean debug) throws Exception {
		for (TestVector vector: vectors) {
		    test(vector,debug);
		}
	}
    
    protected void test(TestVector vector,boolean debug) throws Exception {
        Assembler assembler = new Assembler(debug);
        F18A      f18A      = assembler.assemble(vector.src);
        int[]     ram       = f18A.ram();
        int[]     ref       = vector.ram;
        int[]     mask      = vector.mask;
            
        if (debug) {
            for (int i=0; i<vector.ram.length; i++) {
                System.err.println(String.format("%2d:  %08X  %08X",i,ref[i],ram[i]));
            }
        }

        for (int i=0; i<vector.ram.length; i++) {
            assertEquals("Invalid RAM[" + i + "]",ref[i] & mask[i],ram[i] & mask[i]);
        }
    }

    // INNER CLASSES
    
    protected static class TestVector {
        protected final String src;
        protected final int[]  ram;
        protected final int[]  mask;
        
        protected TestVector(String src,int[] ram,int[] mask) {
            this.src  = src;
            this.ram  = ram;
            this.mask = mask;
        }
        
        protected TestVector(String[] src,int[] ram,int[] mask) {
            StringBuilder string = new StringBuilder();
            
            for (String line: src) {
                string.append(line);
                string.append("\n");
            }
            
            this.src  = string.toString();
            this.ram  = ram;
            this.mask = mask;
        }
        
    }
}
