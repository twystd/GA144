package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestRET extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String RET0 = "antlr 0 org\n"
			                         + "      ;\n";

	private static final String RET1 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      ;\n";

    private static final String RET2 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      ;\n";

    private static final String RET3 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      ;\n";

    // UNIT TESTS 
	
	@Test
	public void testRET0() throws Exception {
		test(RET0,new int[] { 0x149b5 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testRET1() throws Exception {
        test(RET1,new int[] { 0x2d5b2 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testRET2() throws Exception {
        test(RET2,new int[] { 0x2c952 },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testRET3() throws Exception {
        test(RET3,new int[] { 0x2c9b5 },new int[] { 0x3ffff },DEBUG);
    }
}
