package za.co.twyst.GA144.assembler.instructions;

public class Call extends OpCode {
	// INSTANCE VARIABLES

	public final String label;
	
	// CONSTRUCTOR
	
	public Call(String label) {
		super(OPCODE.CALL);
		
		this.label = label;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return String.format("%s %s",opcode.string,label);
	}

}
