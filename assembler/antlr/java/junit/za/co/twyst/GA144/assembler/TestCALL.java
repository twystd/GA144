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
    
    private static final String CALLF0 = "antlr 0 org\n"
                                       + "      L0\n"
                                       + "      L1\n"
                                       + "      L2\n"
                                       + "      L3\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n"
                                       + "L3    nop nop nop nop\n";
    
    private static final String CALLF1 = "antlr 0 org\n"
                                       + "      nop L0\n"
                                       + "      nop L1\n"
                                       + "      nop L2\n"
                                       + "      nop L3\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n"
                                       + "L3    nop nop nop nop\n";
    
    private static final String CALLF2 = "antlr 0 org\n"
                                       + "      nop nop L0\n"
                                       + "      nop nop L1\n"
                                       + "      nop nop L2\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n";
	
	// UNIT TESTS 
	
    @Test
    public void testCALL0() throws Exception {
        test(new TestVector(CALL0,
                            new int[] { 0x2c9b2,0x13400 },
                            new int[] { 0x3ffff,0x3ffff }));
    }

    @Test
    public void testCALL1() throws Exception {
        test(new TestVector(CALL1,
                            new int[] { 0x2c9b2,0x2d600 },
                            new int[] { 0x3ffff,0x3ffff })); 
    }

    @Test
    public void testCALL2() throws Exception {
        test(new TestVector(CALL2,
                            new int[] { 0x2c9b2,0x2c948 },
                            new int[] { 0x3ffff,0x3ffff })); 
    }

    @Test
    public void testCALL3() throws Exception {
        test(new TestVector(CALL3,
                            new int[] { 0x2c9b2,0x2c9b2,0x13400 },
                            new int[] { 0x3ffff,0x3ffff,0x3ffff })); 
    }

    @Test
    public void testCALLF() throws Exception {
        test(new TestVector(CALLF,
                            new int[] { 0x2c9b2,0x13403,0x2c9b2,0x13400 },
                            new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff })); 
    }

	@Test
    public void testCALLF0() throws Exception {
        test( new TestVector(CALLF0,
                             new int[] { 0x13404,0x13405,0x13406,0x13407,0x2c9b2,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }

    @Test
    public void testCALLF1() throws Exception {
        test( new TestVector(CALLF1,
                             new int[] { 0x2d604,0x2d605,0x2d606,0x2d607,0x2c9b2,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }

    @Test
    public void testCALLF2() throws Exception {
        test( new TestVector(CALLF2,
                             new int[] { 0x2c94b,0x2c94c,0x2c94d,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }
}
