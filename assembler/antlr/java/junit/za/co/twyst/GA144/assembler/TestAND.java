package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestAND extends AssemblerTest {
    private static final boolean DEBUG = true;
    
	private static final String AND0 = "antlr 0 org\n"
			                         + "      and\n";

	private static final String AND1 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      and\n";

    private static final String AND2 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      and\n";

    private static final String AND3 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      and\n";

    // UNIT TESTS 
	
	@Test
	public void testAND0() throws Exception {
		test(AND0,new int[] { 0x3f455 },new int[] { 0x3e000 },DEBUG);
	}
    
    @Test
    public void testAND1() throws Exception {
        test(AND1,new int[] { 0x2c055 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testAND2() throws Exception {
        test(AND2,new int[] { 0x2c9fd },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testAND3() throws Exception {
        test(AND3,new int[] { 0x2c9b2,0x3f455 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
