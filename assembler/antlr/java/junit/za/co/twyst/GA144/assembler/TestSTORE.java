package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestSTORE extends AssemblerTest {
    private static final boolean DEBUG = false;

    private static final String STORE0 = "antlr 0 org\n"
			                           + "      !\n";

	private static final String STORE1 = "antlr 0 org\n"
                                       + "      nop\n"
                                       + "      !\n";

    private static final String STORE2 = "antlr 0 org\n"
                                       + "      nop\n"
                                       + "      nop\n"
                                       + "      !\n";

    private static final String STORE3 = "antlr 0 org\n"
                                       + "      nop\n"
                                       + "      nop\n"
                                       + "      nop\n"
                                       + "      !\n";

	// UNIT TESTS 
    
    @Test
    public void testSTORE0() throws Exception {
        test(STORE0,new int[] { 0x0a9b2 },new int[] { 0x3e000 },DEBUG);
    }
    
    @Test
    public void testSTORE1() throws Exception {
        test(STORE1,new int[] { 0x2dab2 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testSTORE2() throws Exception {
        test(STORE2,new int[] { 0x2c92a },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testSTORE3() throws Exception {
        test(STORE3,new int[] { 0x2c9b2,0x0a9b2 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
