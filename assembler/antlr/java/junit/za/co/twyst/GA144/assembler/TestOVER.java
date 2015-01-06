package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestOVER extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String OVER0 = "antlr 0 org\n"
			                          + "      over\n";

	private static final String OVER1 = "antlr 0 org\n"
                                      + "      nop\n"
                                      + "      over\n";

    private static final String OVER2 = "antlr 0 org\n"
                                      + "      nop\n"
                                      + "      nop\n"
                                      + "      over\n";

    private static final String OVER3 = "antlr 0 org\n"
                                      + "      nop\n"
                                      + "      nop\n"
                                      + "      nop\n"
                                      + "      over\n";

    // UNIT TESTS 
	
	@Test
	public void testOVER0() throws Exception {
		test(OVER0,new int[] { 0x21455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testOVER1() throws Exception {
        test(OVER1,new int[] { 0x2cf55 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testOVER2() throws Exception {
        test(OVER2,new int[] { 0x2c985 },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testOVER3() throws Exception {
        test(OVER3,new int[] { 0x2c9b2,0x21455 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
