package za.co.twyst.GA144.assembler.instructions;

public class Down extends OpCode {
	// INSTANCE VARIABLES

	public final int word;
	
	// CONSTRUCTOR
	
	public Down() {
		super(OPCODE.FETCHP);
		
		this.word = 0x115;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return String.format("%s %x",opcode.string,word);
	}

}
