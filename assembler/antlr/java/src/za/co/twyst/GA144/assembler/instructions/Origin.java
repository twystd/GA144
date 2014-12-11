package za.co.twyst.GA144.assembler.instructions;

public class Origin extends Instruction {
	// CONSTANTS
	
	// INSTANCE VARIABLES
	
	public final int address;
	
	// CONSTRUCTOR
	
	public Origin(int address) {
		this.address = address;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return "ORG:" + address;
	}
}
