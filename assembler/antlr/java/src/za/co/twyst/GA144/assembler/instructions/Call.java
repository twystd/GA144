package za.co.twyst.GA144.assembler.instructions;

public class Call extends Instruction {
	// INSTANCE VARIABLES

	public final int address;
	
	// CONSTRUCTOR
	
	public Call(int address) {
		super(OPCODE.CALL);
		
		this.address = address;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return String.format("%s %x",opcode.string,address);
	}

}
