package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestPOP extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String POP0 = "antlr 0 org\n"
			                         + "      pop\n";

	private static final String POP1 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      pop\n";

    private static final String POP2 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      pop\n";

    private static final String POP3 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      pop\n";

    // UNIT TESTS 
	
	@Test
	public void testPOP0() throws Exception {
		test(POP0,new int[] { 0x27455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testPOP1() throws Exception {
        test(POP1,new int[] { 0x2cc55 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testPOP2() throws Exception {
        test(POP2,new int[] { 0x2c99d },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testPOP3() throws Exception {
        test(POP3,new int[] { 0x2c9b2,0x27455 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
