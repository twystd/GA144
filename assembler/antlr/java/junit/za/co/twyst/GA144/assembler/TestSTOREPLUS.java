package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestSTOREPLUS extends AssemblerTest {
    private static final boolean DEBUG = false;

    private static final String STOREPLUS0 = "antlr 0 org\n"
			                               + "      !+\n";

	private static final String STOREPLUS1 = "antlr 0 org\n"
                                           + "      nop\n"
                                           + "      !+\n";

    private static final String STOREPLUS2 = "antlr 0 org\n"
                                           + "      nop\n"
                                           + "      nop\n"
                                           + "      !+\n";

    private static final String STOREPLUS3 = "antlr 0 org\n"
                                           + "      nop\n"
                                           + "      nop\n"
                                           + "      nop\n"
                                           + "      !+\n";

	// UNIT TESTS 
    
    @Test
    public void testSTOREPLUS0() throws Exception {
        test(STOREPLUS0,new int[] { 0x0e9b2 },new int[] { 0x3e000 },DEBUG);
    }
    
    @Test
    public void testSTOREPLUS1() throws Exception {
        test(STOREPLUS1,new int[] { 0x2d8b2 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testSTOREPLUS2() throws Exception {
        test(STOREPLUS2,new int[] { 0x2c93a },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testSTOREPLUS3() throws Exception {
        test(STOREPLUS3,new int[] { 0x2c9b2,0x0e9b2 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
