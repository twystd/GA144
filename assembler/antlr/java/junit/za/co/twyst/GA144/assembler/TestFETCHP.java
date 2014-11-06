package za.co.twyst.GA144.assembler;

import static org.junit.Assert.*;

import org.junit.Test;

public class TestFETCHP {
	private static final String FETCHP0 = "antlr 0 org\n"
			                            + "      @p\n";

	private static final String FETCHP1 = "antlr 0 org\n"
                                        + "      @p\n"
                                        + "      @p\n";

    private static final String FETCHP2 = "antlr 0 org\n"
                                        + "      @p\n"
                                        + "      @p\n"
                                        + "      @p\n";

    private static final String FETCHP3 = "antlr 0 org\n"
                                        + "      @p\n"
                                        + "      @p\n"
                                        + "      @p\n"
                                        + "      @p\n";

    private static final TestVector[] FETCHP = { new TestVector(FETCHP0,new int[] { 0x049b2 },new int[] { 0x3e000 } ), 
                                                 new TestVector(FETCHP1,new int[] { 0x05db2 },new int[] { 0x3ff00 } ), 
                                                 new TestVector(FETCHP2,new int[] { 0x05d12 },new int[] { 0x3fff8 } ), 
                                                 new TestVector(FETCHP3,new int[] { 0x05d17 },new int[] { 0x3ffff } ) 
                                               };

	// UNIT TESTS 
	
	@Test
	public void testFETCHP() throws Exception {
		for (TestVector vector: FETCHP) {
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
