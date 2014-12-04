package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestWRITE extends AssemblerTest {
	private static final String PROG = "antlr 0 org\n"
			                         + "      right b! 678 !b\n";

    private static final TestVector[] WRITE = { new TestVector(PROG,
                                                               new int[] { 0x04b12,0x001d5,0x002a6,0x09600 },
                                                               new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3e000 }), 
                                             };

	// UNIT TESTS 
	
	@Test
	public void testWrite() throws Exception {
		test(WRITE,true);
	}
}
