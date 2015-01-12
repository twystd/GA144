package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestFETCHPLUS extends AssemblerTest {
    private static final boolean DEBUG = false;

    private static final String FETCHPLUS0 = "antlr 0 org\n"
			                               + "      @+\n";

	private static final String FETCHPLUS1 = "antlr 0 org\n"
                                           + "      nop\n"
                                           + "      @+\n";

    private static final String FETCHPLUS2 = "antlr 0 org\n"
                                           + "      nop\n"
                                           + "      nop\n"
                                           + "      @+\n";

    private static final String FETCHPLUS3 = "antlr 0 org\n"
                                           + "      nop\n"
                                           + "      nop\n"
                                           + "      nop\n"
                                           + "      @+\n";

	// UNIT TESTS 
	
    @Test
    public void testFETCHPLUS0() throws Exception {
        test(FETCHPLUS0,new int[] { 0x069b2 },new int[] { 0x3e000 },DEBUG);
    }
    
    @Test
    public void testFETCHPLUS1() throws Exception {
        test(FETCHPLUS1,new int[] { 0x2dcb2 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testFETCHPLUS2() throws Exception {
        test(FETCHPLUS2,new int[] { 0x2c91a },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testFETCHPLUS3() throws Exception {
        test(FETCHPLUS3,new int[] { 0x2c9b2,0x069b2 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
