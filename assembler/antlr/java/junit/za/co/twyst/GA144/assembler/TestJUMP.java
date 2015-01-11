package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestJUMP extends AssemblerTest {
	private static final String JUMP0 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      start ;\n";
	
	private static final String JUMP1 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop start ;\n";
	
	private static final String JUMP2 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop nop start ;\n";
	
	private static final String JUMP3 = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      nop nop nop start ;\n";
	
	private static final String JUMPF = "antlr 0 org\n"
                                      + "start nop nop nop nop\n"
                                      + "      end\n"
                                      + "      nop nop nop nop\n"
                                      + "end   start ;\n";
    
    private static final String JUMPF0 = "antlr 0 org\n"
                                       + "      L0 ;\n"
                                       + "      L1 ;\n"
                                       + "      L2 ;\n"
                                       + "      L3 ;\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n"
                                       + "L3    nop nop nop nop\n";
    
    private static final String JUMPF1 = "antlr 0 org\n"
                                       + "      nop L0 ;\n"
                                       + "      nop L1 ;\n"
                                       + "      nop L2 ;\n"
                                       + "      nop L3 ;\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n"
                                       + "L3    nop nop nop nop\n";
    
    private static final String JUMPF2 = "antlr 0 org\n"
                                       + "      nop nop L0 ;\n"
                                       + "      nop nop L1 ;\n"
                                       + "      nop nop L2 ;\n"
                                       + "L0    nop nop nop nop\n"
                                       + "L1    nop nop nop nop\n"
                                       + "L2    nop nop nop nop\n";
	
	// UNIT TESTS 
	
    @Test
    public void testJUMP0() throws Exception {
        test(new TestVector(JUMP0,
                            new int[] { 0x2c9b2,0x11400 },
                            new int[] { 0x3ffff,0x3ffff }));
    }

    @Test
    public void testJUMP1() throws Exception {
        test(new TestVector(JUMP1,
                            new int[] { 0x2c9b2,0x2d700 },
                            new int[] { 0x3ffff,0x3ffff })); 
    }

    @Test
    public void testJUMP2() throws Exception {
        test(new TestVector(JUMP2,
                            new int[] { 0x2c9b2,0x2c940 },
                            new int[] { 0x3ffff,0x3ffff })); 
    }

    @Test
    public void testJUMP3() throws Exception {
        test(new TestVector(JUMP3,
                            new int[] { 0x2c9b2,0x2c9b2,0x11400 },
                            new int[] { 0x3ffff,0x3ffff,0x3ffff })); 
    }

    @Test
    public void testJUMPF() throws Exception {
        test(new TestVector(JUMPF,
                            new int[] { 0x2c9b2,0x13403,0x2c9b2,0x11400 },
                            new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff })); 
    }

	@Test
    public void testJUMPF0() throws Exception {
        test( new TestVector(JUMPF0,
                             new int[] { 0x11404,0x11405,0x11406,0x11407,0x2c9b2,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }

    @Test
    public void testJUMPF1() throws Exception {
        test( new TestVector(JUMPF1,
                             new int[] { 0x2d704,0x2d705,0x2d706,0x2d707,0x2c9b2,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }

    @Test
    public void testJUMPF2() throws Exception {
        test( new TestVector(JUMPF2,
                             new int[] { 0x2c943,0x2c944,0x2c945,0x2c9b2,0x2c9b2,0x2c9b2 },
                             new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }));
    }
}
