package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestSTOREP extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String STOREP0 = "antlr 0 org\n"
			                            + "      !p\n";

	private static final String STOREP1 = "antlr 0 org\n"
                                        + "      nop\n"
                                        + "      !p\n";

    private static final String STOREP2 = "antlr 0 org\n"
                                        + "      nop\n"
                                        + "      nop\n"
                                        + "      !p\n";

    private static final String STOREP3 = "antlr 0 org\n"
                                        + "      nop\n"
                                        + "      nop\n"
                                        + "      nop\n"
                                        + "      !p\n";

    // UNIT TESTS 
	
	@Test
	public void testSTOREP0() throws Exception {
		test(STOREP0,new int[] { 0x0d455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testSTOREP1() throws Exception {
        test(STOREP1,new int[] { 0x2d955 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testSTOREP2() throws Exception {
        test(STOREP2,new int[] { 0x2c935 },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testSTOREP3() throws Exception {
        test(STOREP3,new int[] { 0x2c9b6 },new int[] { 0x3ffff },DEBUG);
    }
}
