package za.co.twyst.GA144.assembler;

import java.util.Arrays;

public class F18A {
	// INSTANCE VARIABLES
	
	public final int[] ROM = new int[64];
	public final int[] RAM = new int[64];

	// CONSTRUCTOR
	
	public F18A() {
		Arrays.fill(ROM,0x00);
		Arrays.fill(RAM,0x00);
	}
}
