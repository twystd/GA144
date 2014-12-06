package za.co.twyst.GA144.assembler;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.antlr.v4.runtime.tree.TerminalNode;

import za.co.twyst.GA144.assembler.antlr.F18ABaseListener;
import za.co.twyst.GA144.assembler.antlr.F18ALexer;
import za.co.twyst.GA144.assembler.antlr.F18AParser;
import za.co.twyst.GA144.assembler.antlr.F18AParser.CommentContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.ConstantContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.LabelContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.CallContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.OpcodeContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.OriginContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.ProgramContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.WordContext;
import za.co.twyst.GA144.assembler.instructions.Call;
import za.co.twyst.GA144.assembler.instructions.Constant;
import za.co.twyst.GA144.assembler.instructions.Instruction;
import za.co.twyst.GA144.assembler.instructions.Label;
import za.co.twyst.GA144.assembler.instructions.Right;
import za.co.twyst.GA144.assembler.instructions.OpCode;
import za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE;

import static za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE.BSTORE;
import static za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE.CALL;
import static za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE.DUP;
import static za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE.FETCHB;
import static za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE.FETCHP;
import static za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE.JUMP;
import static za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE.NOP;
import static za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE.PLUS;
import static za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE.RET;
import static za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE.STOREB;

public class Assembler extends F18ABaseListener {
	// CONSTANTS
	
    private static final OPCODE  PAD    = RET; // opcode used to pad an instruction after a RET
    private static final Pattern CONSTANT = Pattern.compile("([\\-]?[0-9]+)"); 

    private static final int[]   RSHIFT = { 0,5,10,15 };
    private static final int     XOR    = 0x15555;
    private static final int[]   MASK   = { 0x3e000,0x01f00,0x000f8,0x00007 };

    private static final OPCODE[]   SLOT3  = { RET,FETCHP,PLUS,DUP,NOP };
    private static final int        MAXINT = 262144;

	// INSTANCE VARIABLES
	
    private final boolean debug;
    private final OPCODE  pad;
    
	private int   origin;
    private int   location;
    private int   slot;
    
	private int               P;
	private int[]             ram          = new int[64];
	private List<Instruction> instructions = new ArrayList<Instruction>();
	
	// ENTRY POINT
	
	public static void main(String[] args) {
		// ... parse command line arguments
		
		File    in    = null;
		File    out   = null;
		boolean debug = false;
		OPCODE  pad   = RET;
		int     ix    = 0;
		
		while(ix < args.length) {
			String arg = args[ix++];
			
			switch(arg) {
				case "--in":
					if (ix < args.length) {
						in = new File(args[ix++]);
					}
					break;
					
				case "--out":
					if (ix < args.length) {
						out = new File(args[ix++]);
					}
					break;
                    
                case "--pad":
                    if (ix < args.length) {
                        if (args[ix++].equalsIgnoreCase("nop")) {
                            pad = NOP;
                        }
                    }
                    break;
                    
                case "--debug":
                    debug = true;
                    break;
			}
		}
		
		// ... validate

		if (in == null) {
			System.out.println("Usage: java -jar assembler.jar --in <filename> --out <filename> [--pad nop] [--debug]");
			System.exit(-1);
		}
		
		if (out == null) {
            System.out.println("Usage: java -jar assembler.jar --in <filename> --out <filename> [--pad nop] [--debug]");
			System.exit(-1);
		}

		if (!in.exists()) {
			System.out.println("Source file '" + in.getPath() + "' does not exist");
			System.exit(-1);
		}
		
		if (!in.isFile()) {
			System.out.println("Source file '" + in.getPath() + "' is not a file");
			System.exit(-1);
		}
		
		// ... parse

        Assembler assembler = new Assembler(pad,debug);

		try {
            assembler.assemble(in,out);
		} catch(Throwable x) {
			System.err.println("ERROR: " + x);
		}
	}
	
	// CLASS METHODS
	
	private static boolean contains(OPCODE[] array,OPCODE value) {
		for (OPCODE item: array) {
			if (item == value) {
				return true;
			}
		}
		
		return false;
	}
	
	// CONSTRUCTOR
    
    protected Assembler() {
        this.pad   = PAD;
        this.debug = false;
    }
	
	protected Assembler(OPCODE pad,boolean debug) {
	    this.pad   = pad;
	    this.debug = debug;
	}

	// INSTANCE METHODS

	protected int[] assemble(String src) throws Exception {
        return assemble(new ANTLRInputStream(src));
	}

    protected void assemble(File src,File bin) throws Exception {
        // ... assemble
        
        try (InputStream istream = new FileInputStream (src)) {
            assemble(new ANTLRInputStream(istream));
        }
        
        // ... write to file
        
        try (PrintWriter writer = new PrintWriter(bin)) {
            writer.println(String.format("%-8s org %d","xx",origin));
            writer.println();
            
            for (int i=0; i<ram.length; i++) {
                writer.println(String.format("%04X  %04X",i,ram[i]));
            }
        }
    }

	private int[] assemble(ANTLRInputStream input) throws Exception {
        // ... parse

		F18ALexer         lexer     = new F18ALexer(input);
		CommonTokenStream tokens    = new CommonTokenStream(lexer);
		F18AParser        parser    = new F18AParser(tokens);
		ParseTree         tree      = parser.program(); 
		ParseTreeWalker   walker    = new ParseTreeWalker();

		walker.walk(this,tree); 
		
		if (debug) {
			System.out.println("---");
			System.out.println(instructions);
			System.out.println("---");
		}
		
		Map<String,Integer>   labels = new HashMap<String, Integer>();
		Iterator<Instruction> ix;
		boolean               resolved;
		
		do { Arrays.fill(ram,0);
		
		     resolved = true;
		     location = 0;
		     slot     = 0;
		     P        = 0;
		     ix       = instructions.iterator();
			    
		     while(ix.hasNext()) {
				 Instruction instruction = ix.next();
				 
				 if (instruction instanceof Label) {
					 labels.put(((Label) instruction).name,P);
					 continue;
				 }
			
				 if (instruction instanceof Call) {
					 String label   = ((Call) instruction).label;
					 int    address;
				
					 if (!labels.containsKey(label)) {
						 resolved = false;
						 address  = 0x3ff;
					 } else {
						 address = labels.get(label);
					 }
					 
					 if (ix.hasNext()) {
						 Instruction next = ix.next();
				
						 if ((next instanceof OpCode) && ((OpCode) next).opcode == RET) {
							 encodeJump(address);
						 } else {
							 encodeCall(address);

							 // FIXME: what if next is a call/jump ??
							 if (next instanceof OpCode) {
								 encode((OpCode) next);
							 }
						 } 
					 } else {
						 encodeCall(address);
					 }
				 } else { 
					 if (instruction instanceof OpCode) {
						 encode((OpCode) instruction);
					 }
				 }
				 
			 }  
		} while (!resolved);
		
		return ram;
	}
	
	// *** F18ABaseListener ***

	@Override
	public void enterProgram(ProgramContext ctx) {
	}

	@Override
	public void exitProgram(ProgramContext ctx) {
	}

	@Override
	public void enterOrigin(OriginContext ctx) {
		int address = Integer.parseInt(ctx.address().NUMBER().getText());
		
		this.origin   = address;
		this.P        = address;
		this.location = address;
		this.slot     = 0;
	}

	@Override
	public void enterComment(CommentContext ctx) {
	}

	@Override
	public void enterLabel(LabelContext ctx) {
    	instructions.add(new Label(ctx.getText()));
	}

	@Override
	public void enterOpcode(OpcodeContext ctx) {
        TerminalNode node;
        
        // ... opcode ?
        
	    if ((node = ctx.OPCODE()) != null) {
	        if (debug) {
	            System.out.println("OPCODE:   " + node.getText());
	        }
	        
	        switch(node.getText()) {
	            case "ret":
                case ";":
                	instructions.add(new OpCode(RET));
                    break;
                     
			    case "@p":
                	instructions.add(new OpCode(FETCHP));
		        	break;
			        
			    case "@b":                  
                	instructions.add(new OpCode(FETCHB));
		        	break;
			        
			    case "!b":                  
                	instructions.add(new OpCode(STOREB));
		        	break;
                    
                case "+":                  
                	instructions.add(new OpCode(PLUS));
                    break;
                    
                case "dup":                  
                	instructions.add(new OpCode(DUP));
                    break;

			    case "nop":
                case ".":
            	    instructions.add(new OpCode(NOP));
			        break;

			    case "b!":
                	instructions.add(new OpCode(BSTORE));
		        	break;
	        }
	    }
	}

	@Override
	public void enterWord(WordContext ctx) {
        TerminalNode node;
        
        if ((node = ctx.WORD()) != null) {
	        if (debug) {
	            System.out.println("WORD:     " + node.getText());
	        }

	        switch(node.getText()) {
                case "right":
                	instructions.add(new Right());
                    break;
            }
        }
	}
	
	@Override
	public void enterConstant(ConstantContext ctx) {
        TerminalNode node;
        
        if ((node = ctx.NUMBER()) != null) {
	        if (debug) {
	            System.out.println("CONSTANT: " + node.getText());
	        }

	        String  text    = node.getText();
        	Matcher matcher = CONSTANT.matcher(text);
        	
        	if (matcher.matches()) {
            	int constant  = Integer.parseInt(matcher.group(1));
            	
            	if (constant > MAXINT) {
            		System.err.println("WARNING: invalid constant '" + text + "' (will be truncated to 18 bits)");
            	}
            	
            	instructions.add(new Constant(constant));
        	}
        }
	}

    @Override
    public void enterCall(CallContext ctx) {
        TerminalNode node;
        
        if ((node = ctx.NAME()) != null) {
            if (debug) {
                System.out.println("OPCODE:   call " + node.getText());
            }

            instructions.add(new Call(node.getText()));
        }
    }

	// INTERNAL
	
	
	private void encode(OpCode opcode) {
		// ... pad current instruction with NOP ?
		
	    if (slot == 3) {
	    	if (!contains(SLOT3, opcode.opcode)) {
	    		encode(NOP);
	    	}
	    }

	    // ... Word ?
	    
	    if (opcode instanceof Right) {
	    	encode(FETCHP,((Right) opcode).word);
	    	return;
	    }

	    // ... Constant ?
	    
	    if (opcode instanceof Constant) {
	    	encode(FETCHP,((Constant) opcode).word);
	    	return;
	    }

	    // ... encode into current instruction
	    
	    int rsh  = RSHIFT[slot];
	    int mask = MASK[slot];
	    
	    ram[location] |= (((opcode.opcode.code << 13) >>> rsh) ^ XOR) & mask;
	    slot           = (slot + 1) % 4;

	    //  ... 'k, done
	    
	    if (slot == 0) {
	    	location = ++P;
	    	return;
	    } 
	    
	    // ... pad after a RET

	    if (opcode.opcode == RET) {
	        while(slot != 0) {
	            encode(pad);
		    } 
	    }
	}

	private void encode(OPCODE opcode) {
		// ... pad current instruction with NOP ?
		
	    if (slot == 3) {
	    	if (!contains(SLOT3, opcode)) {
	    		encode(NOP);
	    	}
	    }

	    // ... encode into current instruction
	    
	    int rsh  = RSHIFT[slot];
	    int mask = MASK[slot];
	    
	    ram[location] |= (((opcode.code << 13) >>> rsh) ^ XOR) & mask;
	    slot           = (slot + 1) % 4;

	    //  ... 'k, done
	    
	    if (slot == 0) {
	    	location = ++P;
	    	return;
	    } 
	    
	    // ... pad after a RET

	    if (opcode == RET) {
	        while(slot != 0) {
	            encode(pad);
		    } 
	    }
	}
	        
    private void encode(OPCODE opcode,int constant) {
        int rsh  = RSHIFT[slot];
        int mask = MASK[slot];
	        
        ram[location] |= (((opcode.code << 13) >>> rsh) ^ XOR) & mask;
        ram[++P]      |= constant;
        slot           = (slot + 1) % 4;

        if (slot == 0) {
            location = ++P;
        }
    }
    
    private void encodeJump(int address) {
    	// ... pad ?
    	
        if ((slot == 3) || ((slot == 2) && (address > 0x007)) || ((slot == 1) && (address > 0x0ff))) {
	        while (slot != 0) {
	            encode(NOP);
		    } 
        }

        // ... encode
        
    	OPCODE opcode  = JUMP;
        int    rsh     = RSHIFT[slot];
        int    mask    = MASK[slot];

        ram[location] |= (((opcode.code << 13) >>> rsh) ^ XOR) & mask;
            
        if (slot == 0) {
        	ram[location] |= 0x01C00 & XOR;
            ram[location] |= (address & 0x03ff);
        } else if (slot == 1) {
            ram[location] |= (address & 0x0ff);
        } else if (slot == 2) {
            ram[location] |= (address & 0x007);
        }

        location = ++P;
        slot     = 0;
    }

    private void encodeCall(int address) {
    	// ... pad ?
    	
        if ((slot == 3) || ((slot == 2) && (address > 0x007)) || ((slot == 1) && (address > 0x0ff))) {
	        while (slot != 0) {
	            encode(NOP);
		    } 
        }

        // ... encode
        
    	OPCODE opcode  = CALL;
        int    rsh     = RSHIFT[slot];
        int    mask    = MASK[slot];

        if ((slot == 3) || ((slot == 2) && (address > 0x007)) || ((slot == 1) && (address > 0x0ff))) {
	        while(slot != 0) {
	            encode(NOP);
		    } 
        }

        ram[location] |= (((opcode.code << 13) >>> rsh) ^ XOR) & mask;
            
        if (slot == 0) {
        	ram[location] |= 0x01C00 & XOR; 
            ram[location] |= (address & 0x03ff);
        } else if (slot == 1) {
            ram[location] |= (address & 0x0ff);
        } else if (slot == 2) {
            ram[location] |= (address & 0x007);
        }
            
        location = ++P;
        slot     = 0;
    }

}


