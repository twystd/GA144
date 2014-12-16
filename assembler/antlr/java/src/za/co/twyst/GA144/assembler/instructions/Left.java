package za.co.twyst.GA144.assembler.instructions;

public class Left extends OpCode {
	// INSTANCE VARIABLES

	public final int word;
	
	// CONSTRUCTOR
	
	public Left() {
		super(OPCODE.FETCHP);
		
		this.word = 0x175;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return String.format("%s %x",opcode.string,word);
	}

}
