package za.co.twyst.GA144.assembler;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

public class TestN404 extends AssemblerTest {
	private static final boolean  DEBUG = true;
	private static final String[] PROG = { "calc1 0 org",
	                                       "",
			                               "calc  3 . + dup + ;",
	                                       "main  1 . + dup calc !b main ;",
			                           	   "init  right b!",
	                                       "      -1 main ;",
	                                       "",
	                                       "      a9H org init ;"
	                                     };
	
    private static final TestVector N404 = new TestVector(PROG,
                                                          new int[] { 0x049f3,0x00003,0x3d555,0x049f3,0x00001,0x13400,0x09703,0x04b12,0x001d5,0x3ffff,0x11403 },
                                                          new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }); 

	// UNIT TESTS 
	
	@Test
	public void testN404() throws Exception {
        Assembler assembler = new Assembler(DEBUG);
        F18A      f18A      = assembler.assemble(N404.src);
        int[]     ram       = f18A.ram();
        int[]     rom       = f18A.rom();
        int[]     ref       = N404.ram;
        int[]     mask      = N404.mask;
            
        if (DEBUG) {
            for (int i=0; i<N404.ram.length; i++) {
                System.err.println(String.format("%2d:  %08X  %08X",i,ref[i],ram[i]));
            }
        }

        for (int i=0; i<N404.ram.length; i++) {
            assertEquals("Invalid RAM[" + i + "]",ref[i] & mask[i],ram[i] & mask[i]);
        }
        
        // ... verify ROM
        
        int address = 0xA9 - F18A.ROM_BASE;

        assertEquals("Invalid ROM[A9]",0x11407,rom[address]);
        
	}
}
