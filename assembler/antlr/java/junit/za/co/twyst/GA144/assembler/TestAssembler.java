package za.co.twyst.GA144.assembler;

import static org.junit.Assert.*;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

public class TestAssembler {
	private static final String NOP = "antlr 0 org\n"
			                        + ""
			                        + "start nop\n";

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

	@Test
	public void test() throws Exception {
		Assembler assembler = new Assembler();
		int[]     ram       = assembler.assemble(NOP);
		int[]     RAM       = { 0x2d555 };
		int[]     MASK      = { 0x3e000 };
		
		System.err.println(String.format("%08X",ram[0]));
		
		for (int i=0; i<RAM.length; i++) {
			assertEquals("Invalid RAM[" + i + "]",RAM[i] & MASK[i],ram[i] & MASK[i]);
		}
	}

}
