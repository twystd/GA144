package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestNEXT extends AssemblerTest {
	private static final String NEXT0 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      next start\n";
	
	private static final String NEXT1 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop next start\n";
	
	private static final String NEXT2 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop nop next start\n";
	
	private static final String NEXT3 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop nop nop next start\n";
	
	private static final String NEXTF = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      next end\n"
                                      + "      nop nop nop nop\n"
                                      + "end   next start\n";
    
    private static final String NEXTF0 = "antlr 0 org\n"
                                       + "      next L0\n"
                                       + "      next L1\n"
                                       + "      next L2\n"
                                       + "      next L3\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n"
                                       + "L3    nop nop nop nop\n";
    
    private static final String NEXTF1 = "antlr 0 org\n"
                                       + "      nop next L0\n"
                                       + "      nop next L1\n"
                                       + "      nop next L2\n"
                                       + "      nop next L3\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n"
                                       + "L3    nop nop nop nop\n";
    
    private static final String NEXTF2 = "antlr 0 org\n"
                                       + "      nop nop next L0\n"
                                       + "      nop nop next L1\n"
                                       + "      nop nop next L2\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n";
	
	// UNIT TESTS 
	
    @Test
    public void testNEXT0() throws Exception {
        test(new TestVector(NEXT0,
                            new int[] { 0x2c9b2,0x1f400 },
                            new int[] { 0x3ffff,0x3e3ff }));
    }

    @Test
    public void testNEXT1() throws Exception {
        test(new TestVector(NEXT1,
                            new int[] { 0x2c9b2,0x2d000 },
                            new int[] { 0x3ffff,0x3ffff })); 
    }

    @Test
    public void testNEXT2() throws Exception {
        test(new TestVector(NEXT2,
                            new int[] { 0x2c9b2,0x2c978 },
                            new int[] { 0x3ffff,0x3ffff })); 
    }

    @Test
    public void testNEXT3() throws Exception {
        test(new TestVector(NEXT3,
                            new int[] { 0x2c9b2,0x2c9b2,0x1f400 },
                            new int[] { 0x3ffff,0x3ffff,0x3e3ff })); 
    }

    @Test
    public void testNEXTF() throws Exception {
        test(new TestVector(NEXTF,
                            new int[] { 0x2c9b2,0x1f403,0x2c9b2,0x1f400 },
                            new int[] { 0x3ffff,0x3e3ff,0x3ffff,0x3e3ff })); 
    }

	@Test
    public void testNEXTF0() throws Exception {
        test( new TestVector(NEXTF0,
                             new int[] { 0x1f404,0x1f405,0x1f406,0x1f407,0x2c9b2,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff }));
    }

    @Test
    public void testNEXTF1() throws Exception {
        test( new TestVector(NEXTF1,
                             new int[] { 0x2d004,0x2d005,0x2d006,0x2d007,0x2c9b2,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }

    @Test
    public void testNEXTF2() throws Exception {
        test( new TestVector(NEXTF2,
                             new int[] { 0x2c97b,0x2c97c,0x2c97d,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }
}
