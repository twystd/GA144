package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestDROP extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String DROP0 = "antlr 0 org\n"
			                         + "      drop\n";

	private static final String DROP1 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      drop\n";

    private static final String DROP2 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      drop\n";

    private static final String DROP3 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      drop\n";

    // UNIT TESTS 
	
	@Test
	public void testDROP0() throws Exception {
		test(DROP0,new int[] { 0x3b455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testDROP1() throws Exception {
        test(DROP1,new int[] { 0x2c255 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testDROP2() throws Exception {
        test(DROP2,new int[] { 0x2c9ed },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testDROP3() throws Exception {
        test(DROP3,new int[] { 0x2c9b2,0x3b455 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
