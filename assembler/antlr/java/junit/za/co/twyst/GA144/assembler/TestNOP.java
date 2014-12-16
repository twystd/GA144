package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestNOP extends AssemblerTest {
    private static final boolean DEBUG = false;
    
	private static final String NOP0 = "antlr 0 org\n"
			                         + "      nop\n";

	private static final String NOP1 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n";

    private static final String NOP2 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n";

    private static final String NOP3 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n";

    private static final String NOP4 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n";
    
    // UNIT TESTS 
    
    @Test
    public void testNOP0() throws Exception {
        test(NOP0,new int[] { 0x2d555 },new int[] { 0x3e000 },DEBUG);
    }
    
    @Test
    public void testNOP1() throws Exception {
        test(NOP1,new int[] { 0x2c955 },new int[] { 0x3ff00 },DEBUG);
    }
    
    @Test
    public void testNOP2() throws Exception {
        test(NOP2,new int[] { 0x2c9b5 },new int[] { 0x3fff8 },DEBUG);
    }
    
    @Test
    public void testNOP3() throws Exception {
        test(NOP3,new int[] { 0x2c9b2 },new int[] { 0x3ffff },DEBUG);
    }
    
    @Test
    public void testNOP4() throws Exception {
        test(NOP4,new int[] { 0x2c9b2,0x2d555 },new int[] { 0x3ffff,0x3e000 },DEBUG);
    }
}
