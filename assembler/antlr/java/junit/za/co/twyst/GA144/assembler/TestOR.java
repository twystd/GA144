package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestOR extends AssemblerTest {
    private static final boolean DEBUG = true;
    
	private static final String OR0 = "antlr 0 org\n"
			                        + "      or\n";

	private static final String OR1 = "antlr 0 org\n"
                                    + "      nop\n"
                                    + "      or\n";

    private static final String OR2 = "antlr 0 org\n"
                                    + "      nop\n"
                                    + "      nop\n"
                                    + "      or\n";

    private static final String OR3 = "antlr 0 org\n"
                                    + "      nop\n"
                                    + "      nop\n"
                                    + "      nop\n"
                                    + "      or\n";

    // UNIT TESTS 
	
	@Test
	public void testOR0() throws Exception {
		test(OR0,new int[] { 0x39455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testOR1() throws Exception {
        test(OR1,new int[] { 0x2c355 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testOR2() throws Exception {
        test(OR2,new int[] { 0x2c9e5 },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testOR3() throws Exception {
        test(OR3,new int[] { 0x2c9b2,0x39455 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
