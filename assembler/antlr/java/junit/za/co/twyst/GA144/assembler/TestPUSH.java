package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestPUSH extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String PUSH0 = "antlr 0 org\n"
			                          + "      push\n";

	private static final String PUSH1 = "antlr 0 org\n"
                                      + "      nop\n"
                                      + "      push\n";

    private static final String PUSH2 = "antlr 0 org\n"
                                      + "      nop\n"
                                      + "      nop\n"
                                      + "      push\n";

    private static final String PUSH3 = "antlr 0 org\n"
                                      + "      nop\n"
                                      + "      nop\n"
                                      + "      nop\n"
                                      + "      push\n";

    // UNIT TESTS 
	
	@Test
	public void testPUSH0() throws Exception {
		test(PUSH0,new int[] { 0x2f455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testPUSH1() throws Exception {
        test(PUSH1,new int[] { 0x2c855 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testPUSH2() throws Exception {
        test(PUSH2,new int[] { 0x2c9bd },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testPUSH3() throws Exception {
        test(PUSH3,new int[] { 0x2c9b2,0x2f455 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
