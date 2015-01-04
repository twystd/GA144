package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestSHR extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String SHR0 = "antlr 0 org\n"
			                         + "      2/\n";

	private static final String SHR1 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      2/\n";

    private static final String SHR2 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      2/\n";

    private static final String SHR3 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      2/\n";

    // UNIT TESTS 
	
	@Test
	public void testSHR0() throws Exception {
		test(SHR0,new int[] { 0x31455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testSHR1() throws Exception {
        test(SHR1,new int[] { 0x2c755 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testSHR2() throws Exception {
        test(SHR2,new int[] { 0x2c9c5 },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testSHR3() throws Exception {
        test(SHR3,new int[] { 0x2c9b2,0x31455 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
