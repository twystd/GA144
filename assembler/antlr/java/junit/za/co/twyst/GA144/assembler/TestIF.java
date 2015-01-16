package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestIF extends AssemblerTest {
	private static final String IF0 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      if start\n";
	
	private static final String IF1 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop if start\n";
	
	private static final String IF2 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop nop if start\n";
	
	private static final String IF3 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop nop nop if start\n";
	
	private static final String IFX = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      if end\n"
                                      + "      nop nop nop nop\n"
                                      + "end   if start\n";
    
    private static final String IFX0 = "antlr 0 org\n"
                                       + "      if L0\n"
                                       + "      if L1\n"
                                       + "      if L2\n"
                                       + "      if L3\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n"
                                       + "L3    nop nop nop nop\n";
    
    private static final String IFX1 = "antlr 0 org\n"
                                       + "      nop if L0\n"
                                       + "      nop if L1\n"
                                       + "      nop if L2\n"
                                       + "      nop if L3\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n"
                                       + "L3    nop nop nop nop\n";
    
    private static final String IFX2 = "antlr 0 org\n"
                                       + "      nop nop if L0\n"
                                       + "      nop nop if L1\n"
                                       + "      nop nop if L2\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n";
	
	// UNIT TESTS 
	
    @Test
    public void testIF0() throws Exception {
        test(new TestVector(IF0,
                            new int[] { 0x2c9b2,0x18400 },
                            new int[] { 0x3ffff,0x3e3ff }));
    }

    @Test
    public void testIF1() throws Exception {
        test(new TestVector(IF1,
                            new int[] { 0x2c9b2,0x2d300 },
                            new int[] { 0x3ffff,0x3ffff })); 
    }

    @Test
    public void testIF2() throws Exception {
        test(new TestVector(IF2,
                            new int[] { 0x2c9b2,0x2c960 },
                            new int[] { 0x3ffff,0x3ffff })); 
    }

    @Test
    public void testIF3() throws Exception {
        test(new TestVector(IF3,
                            new int[] { 0x2c9b2,0x2c9b2,0x18400 },
                            new int[] { 0x3ffff,0x3ffff,0x3e3ff })); 
    }

    @Test
    public void testIFX() throws Exception {
        test(new TestVector(IFX,
                            new int[] { 0x2c9b2,0x18403,0x2c9b2,0x18400 },
                            new int[] { 0x3ffff,0x3e3ff,0x3ffff,0x3e3ff })); 
    }

	@Test
    public void testIFX0() throws Exception {
        test( new TestVector(IFX0,
                             new int[] { 0x18404,0x18405,0x18406,0x18407,0x2c9b2,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff,0x3e3ff }));
    }

    @Test
    public void testIFX1() throws Exception {
        test( new TestVector(IFX1,
                             new int[] { 0x2d304,0x2d305,0x2d306,0x2d307,0x2c9b2,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }

    @Test
    public void testIFX2() throws Exception {
        test( new TestVector(IFX2,
                             new int[] { 0x2c963,0x2c964,0x2c965,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }
}
