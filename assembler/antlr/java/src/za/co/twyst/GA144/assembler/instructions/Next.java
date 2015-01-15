package za.co.twyst.GA144.assembler.instructions;

public class Next extends OpCode {
	// INSTANCE VARIABLES

	public final String label;
	
	// CONSTRUCTOR
	
	public Next(String label) {
		super(OPCODE.NEXT);
		
		this.label = label;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return String.format("%s %s",opcode.string,label);
	}

}
