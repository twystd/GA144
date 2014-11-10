package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestBSTORE extends AssemblerTest {
	private static final String BSTORE0 = "antlr 0 org\n"
			                            + "      b!\n";

	private static final String BSTORE1 = "antlr 0 org\n"
                                        + "      b!\n"
                                        + "      b!\n";

    private static final String BSTORE2 = "antlr 0 org\n"
                                        + "      b!\n"
                                        + "      b!\n"
                                        + "      b!\n";

    private static final String BSTORE3 = "antlr 0 org\n"
                                        + "      b!\n"
                                        + "      b!\n"
                                        + "      b!\n"
                                        + "      b!\n";

    private static final TestVector[] BSTORE = { new TestVector(BSTORE0,new int[] { 0x289b2 },new int[] { 0x3e000 } ), 
                                                 new TestVector(BSTORE1,new int[] { 0x28bb2 },new int[] { 0x3ff00 } ), 
                                                 new TestVector(BSTORE2,new int[] { 0x28ba2 },new int[] { 0x3fff8 } ), 
                                                 new TestVector(BSTORE3,new int[] { 0x28ba2,0x289b2 },new int[] { 0x3ffff,0x3e000 } ) 
                                               };

	// UNIT TESTS 
	
	@Test
	public void testBSTORE() throws Exception {
		test(BSTORE);
	}
}
