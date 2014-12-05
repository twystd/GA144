package za.co.twyst.GA144.assembler.instructions;

public class Label extends Instruction {
	// CONSTANTS
	
	private static final String BLANK = "\\s*";
	
	// INSTANCE VARIABLES
	
	public final String name;
	
	// CONSTRUCTOR
	
	public Label(String name) {
		// ... validate 
		
		if ((name == null) || name.matches(BLANK)) {
			throw new IllegalArgumentException("Invalid LABEL");
		}
		
		// ... initialise
		
		this.name = name.trim();
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return "<" + name + ">";
	}

}
