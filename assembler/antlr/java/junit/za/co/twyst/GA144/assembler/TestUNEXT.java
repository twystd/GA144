package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestUNEXT extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String UNEXT0 = "antlr 0 org\n"
			                           + "      unext\n";

	private static final String UNEXT1 = "antlr 0 org\n"
                                       + "      nop\n"
                                       + "      unext\n";

    private static final String UNEXT2 = "antlr 0 org\n"
                                       + "      nop\n"
                                       + "      nop\n"
                                       + "      unext\n";

    private static final String UNEXT3 = "antlr 0 org\n"
                                       + "      nop\n"
                                       + "      nop\n"
                                       + "      nop\n"
                                       + "      unext\n";

    // UNIT TESTS 
	
	@Test
	public void testUNEXT0() throws Exception {
		test(UNEXT0,new int[] { 0x1c9b5 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testUNEXT1() throws Exception {
        test(UNEXT1,new int[] { 0x2d1b2 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testUNEXT2() throws Exception {
        test(UNEXT2,new int[] { 0x2c972 },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testUNEXT3() throws Exception {
        test(UNEXT3,new int[] { 0x2c9b4 },new int[] { 0x3ffff },DEBUG);
    }
}
