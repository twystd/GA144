package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestSHL extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String SHL0 = "antlr 0 org\n"
			                         + "      2*\n";

	private static final String SHL1 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      2*\n";

    private static final String SHL2 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      2*\n";

    private static final String SHL3 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      2*\n";

    // UNIT TESTS 
	
	@Test
	public void testSHL0() throws Exception {
		test(SHL0,new int[] { 0x37455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testSHL1() throws Exception {
        test(SHL1,new int[] { 0x2c455 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testSHL2() throws Exception {
        test(SHL2,new int[] { 0x2c9dd },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testSHL3() throws Exception {
        test(SHL3,new int[] { 0x2c9b2,0x37455 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
