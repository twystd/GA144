package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestMULTIPLY extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String MULTIPLY0 = "antlr 0 org\n"
			                              + "      +*\n";

	private static final String MULTIPLY1 = "antlr 0 org\n"
                                          + "      nop\n"
                                          + "      +*\n";

    private static final String MULTIPLY2 = "antlr 0 org\n"
                                          + "      nop\n"
                                          + "      nop\n"
                                          + "      +*\n";

    private static final String MULTIPLY3 = "antlr 0 org\n"
                                          + "      nop\n"
                                          + "      nop\n"
                                          + "      nop\n"
                                          + "      +*\n";

    // UNIT TESTS 
	
	@Test
	public void testMULTIPLY0() throws Exception {
		test(MULTIPLY0,new int[] { 0x35455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testMULTIPLY1() throws Exception {
        test(MULTIPLY1,new int[] { 0x2c555 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testMULTIPLY2() throws Exception {
        test(MULTIPLY2,new int[] { 0x2c9d5 },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testMULTIPLY3() throws Exception {
        test(MULTIPLY3,new int[] { 0x2c9b1 },new int[] { 0x3ffff },DEBUG);
    }
}
