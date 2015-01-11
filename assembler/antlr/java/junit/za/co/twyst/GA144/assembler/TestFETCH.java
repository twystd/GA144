package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestFETCH extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String FETCH0 = "antlr 0 org\n"
			                            + "      @\n";

	private static final String FETCH1 = "antlr 0 org\n"
                                        + "      nop\n"
                                        + "      @\n";

    private static final String FETCH2 = "antlr 0 org\n"
                                        + "      nop\n"
                                        + "      nop\n"
                                        + "      @\n";

    private static final String FETCH3 = "antlr 0 org\n"
                                        + "      nop\n"
                                        + "      nop\n"
                                        + "      nop\n"
                                        + "      @\n";

    // UNIT TESTS 
	
	@Test
	public void testFETCH0() throws Exception {
		test(FETCH0,new int[] { 0x029b2 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testFETCH1() throws Exception {
        test(FETCH1,new int[] { 0x2deb2 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testFETCH2() throws Exception {
        test(FETCH2,new int[] { 0x2c90a },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testFETCH3() throws Exception {
        test(FETCH3,new int[] { 0x2c9b2,0x029b2 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
