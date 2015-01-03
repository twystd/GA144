package za.co.twyst.GA144.assembler.instructions;

public class OpCode extends Instruction {
	// CONSTANTS
	
	public enum OPCODE { RET   (0x00,";",   "ret"),
                         JUMP  (0x02,"jump","jump"),
    	                 CALL  (0x03,"call","call"),
    	                 FETCHP(0x08,"@p",  "fetch-p"),
    	                 FETCHB(0x0a,"@b",  "fetch-b"),
    	                 STOREB(0x0e,"!b",   "store-b"),
                         STORE (0x0f,"!",    "store"),
                         SHL   (0x11,"2*",   "left-shift"),
                         NOT   (0x13,"-",    "not"),
    	                 PLUS  (0x14,"+",    "plus"),
                         AND   (0x15,"and",  "and"),
                         OR    (0x16,"or",   "xor"),
    	                 DUP   (0x18,"dup",  "dup"),
    	                 NOP   (0x1c,".",    "nop"),
    	                 BSTORE(0x1e,"b!",   "b-store"),
                         ASTORE(0x1f,"a!",   "a-store");
	                    
	                     public final int    code;
	                     public final String mnemonic;
	                     public final String string;
	                     
	                     private OPCODE(int code,String mnemonic,String string) {
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
