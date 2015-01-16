package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestMINUSIF extends AssemblerTest {
	private static final String MINUS_IF0 = "antlr 0 org\n"
                                          + "start nop nop nop nop\n"
                                          + "      -if start\n";
	
	private static final String MINUS_IF1 = "antlr 0 org\n"
                                          + "start nop nop nop nop\n"
                                          + "      nop -if start\n";
	
	private static final String MINUS_IF2 = "antlr 0 org\n"
                                          + "start nop nop nop nop\n"
                                          + "      nop nop -if start\n";
	
	private static final String MINUS_IF3 = "antlr 0 org\n"
                                          + "start nop nop nop nop\n"
                                          + "      nop nop nop -if start\n";
	
	private static final String MINUS_IFX = "antlr 0 org\n"
                                          + "start nop nop nop nop\n"
                                          + "      -if end\n"
                                          + "      nop nop nop nop\n"
                                          + "end   -if start\n";
    
    private static final String MINUS_IFX0 = "antlr 0 org\n"
                                           + "      -if L0\n"
                                           + "      -if L1\n"
                                           + "      -if L2\n"
                                           + "      -if L3\n"
                                           + "L0    nop nop nop nop\n"
                                           + "L1    nop nop nop nop\n"
                                           + "L2    nop nop nop nop\n"
                                           + "L3    nop nop nop nop\n";
    
    private static final String MINUS_IFX1 = "antlr 0 org\n"
                                           + "      nop -if L0\n"
                                           + "      nop -if L1\n"
                                           + "      nop -if L2\n"
                                           + "      nop -if L3\n"
                                           + "L0    nop nop nop nop\n"
                                           + "L1    nop nop nop nop\n"
                                           + "L2    nop nop nop nop\n"
                                           + "L3    nop nop nop nop\n";

    private static final String MINUS_IFX2 = "antlr 0 org\n"
                                           + "      nop nop -if L0\n"
                                           + "      nop nop -if L1\n"
                                           + "      nop nop -if L2\n"
                                           + "L0    nop nop nop nop\n"
                                           + "L1    nop nop nop nop\n"
                                           + "L2    nop nop nop nop\n";

	// UNIT TESTS 
	
    @Test
    public void testMINUS_IF0() throws Exception {
        test(new TestVector(MINUS_IF0,
                            new int[] { 0x2c9b2,0x1a400 },
                            new int[] { 0x3ffff,0x3e3ff }));
    }

    @Test
    public void testMINUS_IF1() throws Exception {
        test(new TestVector(MINUS_IF1,
                            new int[] { 0x2c9b2,0x2d200 },
                            new int[] { 0x3ffff,0x3ffff })); 
    }

    @Test
    public void testMINUS_IF2() throws Exception {
        test(new TestVector(MINUS_IF2,
                            new int[] { 0x2c9b2,0x2c968 },
                            new int[] { 0x3ffff,0x3ffff })); 
    }

    @Test
    public void testMINUS_IF3() throws Exception {
        test(new TestVector(MINUS_IF3,
                            new int[] { 0x2c9b2,0x2c9b2,0x1a400 },
                            new int[] { 0x3ffff,0x3ffff,0x3e3ff })); 
    }

    @Test
    public void testMINUS_IFX() throws Exception {
        test(new TestVector(MINUS_IFX,
                            new int[] { 0x2c9b2,0x1a403,0x2c9b2,0x1a400 },
                            new int[] { 0x3ffff,0x3e3ff,0x3ffff,0x3e3ff })); 
    }

	@Test
    public void testMINUS_IFX0() throws Exception {
        test( new TestVector(MINUS_IFX0,
                             new int[] { 0x1a404,0x1a405,0x1a406,0x1a407,0x2c9b2,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff }));
    }

    @Test
    public void testMINUS_IFX1() throws Exception {
        test( new TestVector(MINUS_IFX1,
                             new int[] { 0x2d204,0x2d205,0x2d206,0x2d207,0x2c9b2,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }

    @Test
    public void testMINUS_IFX2() throws Exception {
        test( new TestVector(MINUS_IFX2,
                             new int[] { 0x2c96b,0x2c96c,0x2c96d,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }
}
