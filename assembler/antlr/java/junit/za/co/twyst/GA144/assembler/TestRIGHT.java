package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestRIGHT extends AssemblerTest {
	private static final String RIGHT0 = "antlr 0 org\n"
			                           + "      right\n";

	private static final String RIGHT1 = "antlr 0 org\n"
                                       + "      nop\n"
                                       + "      right\n";

    private static final String RIGHT2 = "antlr 0 org\n"
                                       + "      nop\n"
                                       + "      nop\n"
                                       + "      right\n";

    private static final String RIGHT3 = "antlr 0 org\n"
                                       + "      nop\n"
                                       + "      nop\n"
                                       + "      nop\n"
                                       + "      right\n";

    private static final TestVector[] RIGHT = { new TestVector(RIGHT0,new int[] { 0x04000,0x001d5 },new int[] { 0x3e000,0x3ffff } ), 
                                                new TestVector(RIGHT1,new int[] { 0x2ddb2,0x001d5 },new int[] { 0x3ff00,0x3ffff } ), 
                                                new TestVector(RIGHT2,new int[] { 0x2c912,0x001d5 },new int[] { 0x3fff8,0x3ffff } ), 
                                                new TestVector(RIGHT3,new int[] { 0x2c9b7,0x001d5 },new int[] { 0x3ffff,0x3ffff } ) 
                                            };

	// UNIT TESTS 
	
	@Test
	public void testRIGHT() throws Exception {
		test(RIGHT);
	}
}
