package za.co.twyst.GA144.assembler;

import static org.junit.Assert.*;

import org.junit.Test;

public class TestWRITE {
	private static final String PROG = "antlr 0 org\n"
			                         + "      right b! 678 !b\n";

    private static final TestVector[] WRITE = { new TestVector(PROG,new int[] { 0x04b02,0x001d5,0x089b2,0x002a6 },new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff } ), 
                                             };

	// UNIT TESTS 
	
	@Test
	public void testREAD() throws Exception {
		for (TestVector vector: WRITE) {
	        Assembler assembler = new Assembler();
	        int[]     ram       = assembler.assemble(vector.src);
            int[]     ref       = vector.ram;
            int[]     mask      = vector.mask;
	        
	        for (int i=0; i<vector.ram.length; i++) {
	            assertEquals("Invalid RAM[" + i + "]",ref[i] & mask[i],ram[i] & mask[i]);
	        }
		}
	}

    // INNER CLASSES
    
    private static class TestVector {
        private final String src;
        private final int[]  ram;
        private final int[]  mask;
        
        private TestVector(String src,int[] ram,int[] mask) {
            this.src  = src;
            this.ram  = ram;
            this.mask = mask;
        }
    }
}