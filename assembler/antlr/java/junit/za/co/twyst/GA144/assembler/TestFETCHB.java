package za.co.twyst.GA144.assembler;

import static org.junit.Assert.*;

import org.junit.Test;

public class TestFETCHB {
	private static final String FETCHB0 = "antlr 0 org\n"
			                            + "      @b\n";

	private static final String FETCHB1 = "antlr 0 org\n"
                                        + "      @b\n"
                                        + "      @b\n";

    private static final String FETCHB2 = "antlr 0 org\n"
                                        + "      @b\n"
                                        + "      @b\n"
                                        + "      @b\n";

    private static final String FETCHB3 = "antlr 0 org\n"
                                        + "      @b\n"
                                        + "      @b\n"
                                        + "      @b\n"
                                        + "      @b\n";

    private static final TestVector[] FETCHB = { new TestVector(FETCHB0,new int[] { 0x009b2 },new int[] { 0x3e000 } ), 
                                                 new TestVector(FETCHB1,new int[] { 0x01fb2 },new int[] { 0x3ff00 } ), 
                                                 new TestVector(FETCHB2,new int[] { 0x01f02 },new int[] { 0x3fff8 } ), 
                                                 new TestVector(FETCHB3,new int[] { 0x01f02,0x009b2 },new int[] { 0x3ffff,0x3e000 } ) 
                                               };

	// UNIT TESTS 
	
	@Test
	public void testFETCHB() throws Exception {
		for (TestVector vector: FETCHB) {
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
