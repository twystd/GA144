package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestPLUS extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String PLUS0 = "antlr 0 org\n"
			                          + "      +\n";

	private static final String PLUS1 = "antlr 0 org\n"
                                      + "      nop\n"
                                      + "      +\n";

    private static final String PLUS2 = "antlr 0 org\n"
                                      + "      nop\n"
                                      + "      nop\n"
                                      + "      +\n";

    private static final String PLUS3 = "antlr 0 org\n"
                                      + "      nop\n"
                                      + "      nop\n"
                                      + "      nop\n"
                                      + "      +\n";

    // UNIT TESTS 
	
	@Test
	public void testPLUS0() throws Exception {
		test(PLUS0,new int[] { 0x3d455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testPLUS1() throws Exception {
        test(PLUS1,new int[] { 0x2c155 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testPLUS2() throws Exception {
        test(PLUS2,new int[] { 0x2c9f5 },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testPLUS3() throws Exception {
        test(PLUS3,new int[] { 0x2c9b0 },new int[] { 0x3ffff },DEBUG);
    }
}
