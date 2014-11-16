package za.co.twyst.GA144.assembler;

import static org.junit.Assert.*;

public class AssemblerTest {
	// UNIT TESTS 

	protected void test(TestVector[] vectors) throws Exception {
		test(vectors,false);
	}
	
	protected void test(TestVector[] vectors,boolean debug) throws Exception {
		for (TestVector vector: vectors) {
	        Assembler assembler = new Assembler(0x00,debug);
	        int[]     ram       = assembler.assemble(vector.src);
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
	}

    // INNER CLASSES
    
    protected static class TestVector {
        private final String src;
        private final int[]  ram;
        private final int[]  mask;
        
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
