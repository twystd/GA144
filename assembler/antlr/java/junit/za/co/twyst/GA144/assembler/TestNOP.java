package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestNOP extends AssemblerTest {
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

    private static final String NOPX = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n";
    
    private static final TestVector[] NOP = { new TestVector(NOP0,new int[] { 0x2d555 },new int[] { 0x3e000 } ), 
                                              new TestVector(NOP1,new int[] { 0x2c955 },new int[] { 0x3ff00 } ), 
                                              new TestVector(NOP2,new int[] { 0x2c9b5 },new int[] { 0x3fff8 } ), 
                                              new TestVector(NOP3,new int[] { 0x2c9b2 },new int[] { 0x3ffff } ), 
                                              new TestVector(NOPX,new int[] { 0x2c9b2,0x2d555 },new int[] { 0x3ffff,0x3e000  } ), 
                                            };

    // UNIT TESTS 
	
	@Test
	public void testNOP() throws Exception {
		test(NOP);
	}
}
