package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestASTORE extends AssemblerTest {
    private static final boolean DEBUG = false;

    private static final String ASTORE0 = "antlr 0 org\n"
			                            + "      a!\n";

	private static final String ASTORE1 = "antlr 0 org\n"
                                        + "      nop\n"
                                        + "      a!\n";

    private static final String ASTORE2 = "antlr 0 org\n"
                                        + "      nop\n"
                                        + "      nop\n"
                                        + "      a!\n";

    private static final String ASTORE3 = "antlr 0 org\n"
                                        + "      nop\n"
                                        + "      nop\n"
                                        + "      nop\n"
                                        + "      a!\n";

	// UNIT TESTS 
    
    @Test
    public void testASTORE0() throws Exception {
        test(ASTORE0,new int[] { 0x2a9b2 },new int[] { 0x3e000 },DEBUG);
    }
    
    @Test
    public void testASTORE1() throws Exception {
        test(ASTORE1,new int[] { 0x2cab2 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testASTORE2() throws Exception {
        test(ASTORE2,new int[] { 0x2c9aa },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testASTORE3() throws Exception {
        test(ASTORE3,new int[] { 0x2c9b2,0x2a9b2 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
