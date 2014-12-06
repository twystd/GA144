package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestCALL extends AssemblerTest {
	private static final String CALL0 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      start\n";
	
	private static final String CALL1 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop start\n";
	
	private static final String CALL2 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop nop start\n";
	
	private static final String CALL3 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop nop nop start\n";
	
	private static final String CALLF = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      end\n"
                                      + "      nop nop nop nop\n"
                                      + "end   start\n";
	
    private static final TestVector[] CALL = { 
    	                                       new TestVector(CALL0,
                                                              new int[] { 0x2c9b2,0x13400 },
                                                              new int[] { 0x3ffff,0x3ffff }),
                                                              
                                               new TestVector(CALL1,
                                                              new int[] { 0x2c9b2,0x2d600 },
                                                              new int[] { 0x3ffff,0x3ffff }), 
                                                              
                                               new TestVector(CALL2,
                                                              new int[] { 0x2c9b2,0x2c948 },
                                                              new int[] { 0x3ffff,0x3ffff }), 
                                                              
                                               new TestVector(CALL3,
                                                              new int[] { 0x2c9b2,0x2c9b2,0x13400 },
                                                              new int[] { 0x3ffff,0x3ffff,0x3ffff }), 
                                                              
                                               new TestVector(CALLF,
                                                              new int[] { 0x2c9b2,0x13403,0x2c9b2,0x13400 },
                                                              new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff }), 
                                             };

	// UNIT TESTS 
	
	@Test
	public void testCALL() throws Exception {
		test(CALL,true);
	}
}
