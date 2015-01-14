package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestEX extends AssemblerTest {
    private static final boolean DEBUG = false;

    private static final String EX0 = "antlr 0 org\n"
			                        + "      ex\n";

	private static final String EX1 = "antlr 0 org\n"
                                    + "      nop\n"
                                    + "      ex\n";

    private static final String EX2 = "antlr 0 org\n"
                                    + "      nop\n"
                                    + "      nop\n"
                                    + "      ex\n";

    private static final String EX3 = "antlr 0 org\n"
                                    + "      nop\n"
                                    + "      nop\n"
                                    + "      nop\n"
                                    + "      ex\n";

	// UNIT TESTS 
	
    @Test
    public void testEX0() throws Exception {
        test(EX0,new int[] { 0x169b2 },new int[] { 0x3e000 },DEBUG);
    }
    
    @Test
    public void testEX1() throws Exception {
        test(EX1,new int[] { 0x2d4b2 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testEX2() throws Exception {
        test(EX2,new int[] { 0x2c95a },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testEX3() throws Exception {
        test(EX3,new int[] { 0x2c9b2,0x169b2 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
