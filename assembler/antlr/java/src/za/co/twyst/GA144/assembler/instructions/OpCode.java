package za.co.twyst.GA144.assembler.instructions;

public class OpCode extends Instruction {
	// CONSTANTS
	
	public enum OPCODE { RET   (0x00,"ret",     ";","ret"),
	                     JUMP  (0x02,"jump",    "jump"),
	                     CALL  (0x03,"call",    "call"),
	                     FETCHP(0x08,"fetch-p", "@p"),
	                     FETCHB(0x0a,"fetch-b", "@b"),
	                     STOREB(0x0e,"store-b", "!b"),
	                     STORE (0x0f,"store",   "!"),
	                     SHL   (0x11,"shl",     "2*","shl"),
	                     SHR   (0x12,"shr",     "2/","shr"),
	                     NOT   (0x13,"not",     "-"),
	                     PLUS  (0x14,"plus",    "+"),
	                     AND   (0x15,"and",     "and"),
	                     OR    (0x16,"xor",     "or","xor"),
	                     DROP  (0x17,"drop",    "drop"),
	                     DUP   (0x18,"dup",     "dup"),
	                     POP   (0x19,"pop",     "pop"),
	                     OVER  (0x1a,"over",    "over"),
	                     A     (0x1b,"a",       "a"),
	                     NOP   (0x1c,"nop",     ".","nop"),
	                     PUSH  (0x1d,"push",    "push"),
	                     BSTORE(0x1e,"b-store", "b!"),
	                     ASTORE(0x1f,"a-store", "a!");
	                    
	                     public final int      code;
	                     public final String[] mnemonic;
	                     public final String   string;
	                     
	                     private OPCODE(int code,String string,String...mnemonic) {
	                    	 this.code     = code;
	                    	 this.mnemonic = mnemonic;
	                    	 this.string   = string;
	                     }
	}
	
	// INSTANCE VARIABLES
	
	public final OPCODE opcode;
	
	// CONSTRUCTOR
	
	public OpCode(OPCODE opcode) {
		// ... validate 
		
		if (opcode == null) {
			throw new IllegalArgumentException("Invalid OPCODE");
		}
		
		// ... initialise
		
		this.opcode = opcode;
	}
	                     
	// *** Object ***
	
	@Override
	public String toString() {
		return opcode.string;
	}

}
