package za.co.twyst.GA144.assembler;

import java.util.Arrays;

public class F18A {
	// CONSTANTS
	
	public static final int RAM_BASE = 0x00;
	public static final int ROM_BASE = 0x80;
	public static final int IO_BASE  = 0x100;
	
	// INSTANCE VARIABLES
	
	private final int[] ROM = new int[64];
	private final int[] RAM = new int[64];

	// CONSTRUCTOR
	
	public F18A() {
		initialise();
	}
	
	// INSTANCE METHODS

	public void initialise() {
		Arrays.fill(ROM,0x00);
		Arrays.fill(RAM,0x00);
	}
	
	public int[] rom() {
		return ROM.clone();
	}
	
	public int[] ram() {
		return RAM.clone();
	}

	public void store(int location,int constant) {
		if (location < ROM_BASE) {
			RAM[location & 0x7f] |= constant;
		} else if (location < IO_BASE) {
				ROM[location & 0x7f] = constant;
		}
	}

	public void or(int location,int instruction) {
		if (location < ROM_BASE)
			RAM[location & 0x7f] |= instruction;
		else if (location < IO_BASE) {
			ROM[location & 0x7f] |= instruction;
		}
	}

}
