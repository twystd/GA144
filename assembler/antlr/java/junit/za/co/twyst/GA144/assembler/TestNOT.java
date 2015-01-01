package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestNOT extends AssemblerTest {
    private static final boolean DEBUG = true;
    
	private static final String NOT0 = "antlr 0 org\n"
			                         + "      -\n";

	private static final String NOT1 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      -\n";

    private static final String NOT2 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      -\n";

    private static final String NOT3 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      -\n";

    // UNIT TESTS 
	
	@Test
	public void testNOT0() throws Exception {
		test(NOT0,new int[] { 0x33455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testNOT1() throws Exception {
        test(NOT1,new int[] { 0x2c655 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testNOT2() throws Exception {
        test(NOT2,new int[] { 0x2c9cd },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testNOT3() throws Exception {
        test(NOT3,new int[] { 0x2c9b2,0x33455 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
