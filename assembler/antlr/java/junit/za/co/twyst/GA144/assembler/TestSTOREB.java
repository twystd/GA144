package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestSTOREB extends AssemblerTest {
	private static final String STOREB0 = "antlr 0 org\n"
			                            + "      !b\n";

	private static final String STOREB1 = "antlr 0 org\n"
                                        + "      !b\n"
                                        + "      !b\n";

    private static final String STOREB2 = "antlr 0 org\n"
                                        + "      !b\n"
                                        + "      !b\n"
                                        + "      !b\n";

    private static final String STOREB3 = "antlr 0 org\n"
                                        + "      !b\n"
                                        + "      !b\n"
                                        + "      !b\n"
                                        + "      !b\n";

    private static final TestVector[] STOREB = { new TestVector(STOREB0,new int[] { 0x089b2 },new int[] { 0x3e000 } ), 
                                                 new TestVector(STOREB1,new int[] { 0x09bb2 },new int[] { 0x3ff00 } ), 
                                                 new TestVector(STOREB2,new int[] { 0x09b22 },new int[] { 0x3fff8 } ), 
                                                 new TestVector(STOREB3,new int[] { 0x09b22,0x089b2 },new int[] { 0x3ffff,0x3e000 } ) 
                                               };

	// UNIT TESTS 
	
	@Test
	public void testSTOREB() throws Exception {
		test(STOREB);
	}
}
