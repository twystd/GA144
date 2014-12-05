package za.co.twyst.GA144.assembler.instructions;

public class Right extends OpCode {
	// INSTANCE VARIABLES

	public final int word;
	
	// CONSTRUCTOR
	
	public Right() {
		super(OPCODE.FETCHP);
		
		this.word = 0x1d5;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return String.format("%s %x",opcode.string,word);
	}

}
