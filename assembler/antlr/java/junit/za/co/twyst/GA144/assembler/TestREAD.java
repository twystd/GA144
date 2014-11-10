package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestREAD extends AssemblerTest {
	private static final String PROG = "antlr 0 org\n"
			                         + "      right b! @b\n";

    private static final TestVector[] READ = { new TestVector(PROG,new int[] { 0x04b02,0x001d5 },new int[] { 0x3ffe0,0x3ffff } ), 
                                             };

	// UNIT TESTS 
	
	@Test
	public void testREAD() throws Exception {
		test(READ);
	}
}
