package za.co.twyst.GA144.assembler;

import static org.junit.Assert.*;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

public class TestNOP {
	private static final String NOP1 = "antlr 0 org\n"
			                         + "      nop\n";

	private static final String NOP2 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n";

    private static final String NOP3 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n";

    private static final String NOP4 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n";

    private static final String NOP5 = "antlr 0 org\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n"
                                     + "      nop\n";
    
    private static final TestVector[] NOP = { new TestVector(NOP1,new int[] { 0x2d555 },new int[] { 0x3e000 } ), 
                                              new TestVector(NOP2,new int[] { 0x2c955 },new int[] { 0x3ff00 } ), 
                                              new TestVector(NOP3,new int[] { 0x2c9b5 },new int[] { 0x3fff8 } ), 
                                              new TestVector(NOP4,new int[] { 0x2c9b2 },new int[] { 0x3ffff } ), 
                                              new TestVector(NOP5,new int[] { 0x2c9b2,0x2d555 },new int[] { 0x3ffff,0x3e000  } ), 
                                            };

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	// UNIT TESTS 
	
	@Test
	public void testNOP() throws Exception {
		for (TestVector vector: NOP) {
	        Assembler assembler = new Assembler();
	        int[]     ram       = assembler.assemble(vector.src);
            int[]     ref       = vector.ram;
            int[]     mask      = vector.mask;
	        
	        for (int i=0; i<vector.ram.length; i++) {
	            assertEquals("Invalid RAM[" + i + "]",ref[i] & mask[i],ram[i] & mask[i]);
	        }
		}
	}

    // INNER CLASSES
    
    private static class TestVector {
        private final String src;
        private final int[]  ram;
        private final int[]  mask;
        
        private TestVector(String src,int[] ram,int[] mask) {
            this.src  = src;
            this.ram  = ram;
            this.mask = mask;
        }
    }
}