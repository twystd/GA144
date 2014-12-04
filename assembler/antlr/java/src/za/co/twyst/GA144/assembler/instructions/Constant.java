package za.co.twyst.GA144.assembler.instructions;

public class Constant extends Instruction {
	// INSTANCE VARIABLES

	public final int word;
	
	// CONSTRUCTOR
	
	public Constant(int word) {
		super(OPCODE.FETCHP);
		
		this.word = word & 0x3ffff;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return String.format("%s %x",opcode.string,word);
	}

}
