package za.co.twyst.GA144.assembler.instructions;

public class If extends OpCode {
	// INSTANCE VARIABLES

	public final String label;
	
	// CONSTRUCTOR
	
	public If(String label) {
		super(OPCODE.IF);
		
		this.label = label;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return String.format("%s %s",opcode.string,label);
	}

}
