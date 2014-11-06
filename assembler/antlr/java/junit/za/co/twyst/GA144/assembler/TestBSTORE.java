package za.co.twyst.GA144.assembler;

import static org.junit.Assert.*;

import org.junit.Test;

public class TestBSTORE {
	private static final String BSTORE0 = "antlr 0 org\n"
			                            + "      b!\n";

	private static final String BSTORE1 = "antlr 0 org\n"
                                        + "      b!\n"
                                        + "      b!\n";

    private static final String BSTORE2 = "antlr 0 org\n"
                                        + "      b!\n"
                                        + "      b!\n"
                                        + "      b!\n";

    private static final String BSTORE3 = "antlr 0 org\n"
                                        + "      b!\n"
                                        + "      b!\n"
                                        + "      b!\n"
                                        + "      b!\n";

    private static final TestVector[] BSTORE = { new TestVector(BSTORE0,new int[] { 0x289b2 },new int[] { 0x3e000 } ), 
                                                 new TestVector(BSTORE1,new int[] { 0x28bb2 },new int[] { 0x3ff00 } ), 
                                                 new TestVector(BSTORE2,new int[] { 0x28ba2 },new int[] { 0x3fff8 } ), 
                                                 new TestVector(BSTORE3,new int[] { 0x28ba2,0x289b2 },new int[] { 0x3ffff,0x3e000 } ) 
                                               };

	// UNIT TESTS 
	
	@Test
	public void testBSTORE() throws Exception {
		for (TestVector vector: BSTORE) {
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
