package za.co.twyst.GA144.assembler.instructions;

public class MinusIf extends OpCode {
	// INSTANCE VARIABLES

	public final String label;
	
	// CONSTRUCTOR
	
	public MinusIf(String label) {
		super(OPCODE.MINUSIF);
		
		this.label = label;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return String.format("%s %s",opcode.string,label);
	}

}
