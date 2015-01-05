package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestDUP extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String DUP0 = "antlr 0 org\n"
			                         + "      dup\n";

	private static final String DUP1 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      dup\n";

    private static final String DUP2 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      dup\n";

    private static final String DUP3 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      dup\n";

    // UNIT TESTS 
	
	@Test
	public void testDUP0() throws Exception {
		test(DUP0,new int[] { 0x25455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testDUP1() throws Exception {
        test(DUP1,new int[] { 0x2cd55 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testDUP2() throws Exception {
        test(DUP2,new int[] { 0x2c995 },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testDUP3() throws Exception {
        test(DUP3,new int[] { 0x2c9b3 },new int[] { 0x3ffff },DEBUG);
    }
}
