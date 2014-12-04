package za.co.twyst.GA144.assembler;

import org.junit.Test;

public class TestN404 extends AssemblerTest {
	private static final String[] PROG = { "calc1 0 org",
	                                       "",
			                               "calc  3 . + dup + ;",
	                                       "main  1 . + dup calc !b main ;"
	                                     };

    private static final TestVector[] N404 = { new TestVector(PROG,
                                                              new int[] { 0x049f3,0x00003,0x3d555,0x049f3,0x00001,0x13400,0x09703 },
                                                              new int[] { 0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff,0x3ffff }) 
                                             };

	// UNIT TESTS 
	
	@Test
	public void testN404() throws Exception {
		test(N404,true);
	}
}
