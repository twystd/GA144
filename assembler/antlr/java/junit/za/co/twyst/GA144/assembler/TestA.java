package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestA extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String A0 = "antlr 0 org\n"
                                   + "      a\n";

	private static final String A1 = "antlr 0 org\n"
                                   + "      nop\n"
                                   + "      a\n";

    private static final String A2 = "antlr 0 org\n"
                                   + "      nop\n"
                                   + "      nop\n"
                                   + "      a\n";

    private static final String A3 = "antlr 0 org\n"
                                   + "      nop\n"
                                   + "      nop\n"
                                   + "      nop\n"
                                   + "      a\n";

    // UNIT TESTS 
	
	@Test
	public void testA0() throws Exception {
		test(A0,new int[] { 0x23455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testA1() throws Exception {
        test(A1,new int[] { 0x2ce55 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testA2() throws Exception {
        test(A2,new int[] { 0x2c98d },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testA3() throws Exception {
        test(A3,new int[] { 0x2c9b2,0x23455 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
