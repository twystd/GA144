package za.co.twyst.GA144.assembler;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.PrintWriter;
import java.util.Arrays;
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
import za.co.twyst.GA144.assembler.antlr.F18AParser.OpcodeContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.OriginContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.ProgramContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.WordContext;

public class Assembler extends F18ABaseListener {
	// CONSTANTS
	
    private static final int     FETCHP = 0x08;
    private static final int     FETCHB = 0x0a;
    private static final int     STOREB = 0x0e;
    private static final int     NOP    = 0x1c;
    private static final int     BSTORE = 0x1e;
    
    private static final int     RIGHT  = 0x01d5;
    private static final Pattern CONSTANT = Pattern.compile("([0-9]+)"); 

    private static final int[]   RSHIFT = { 0,5,10,15 };
    private static final int     XOR    = 0x15555;
    private static final int[]   MASK   = { 0x3e000,0x01f00,0x000f8,0x00007 };

    private static final int[]   SLOT3  = { FETCHP,NOP };
    private static final int     MAXINT = 262144;
    
	// INSTANCE VARIABLES
	
    private final boolean debug;
    
	private int   origin;
    private int   location;
    private int   slot;
    
	private int   P;
	private int[] ram = new int[64];
	
	// ENTRY POINT
	
	public static void main(String[] args) {
		// ... parse command line arguments
		
		File    in    = null;
		File    out   = null;
		boolean debug = false;
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
                    
                case "--debug":
                    if (ix < args.length) {
                        debug = true;
                    }
                    break;
			}
		}
		
		// ... validate

		if (in == null) {
			System.out.println("Usage: java -jar assembler.jar --in <filename> --out <filename>");
			System.exit(-1);
		}
		
		if (out == null) {
			System.out.println("Usage: java -jar assembler.jar --in <filename> --out <filename>");
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

        Assembler assembler = new Assembler(debug);

		try {
            assembler.assemble(in,out);
		} catch(Throwable x) {
			System.err.println("ERROR: " + x);
		}
	}
	
	// CLASS METHODS
	
	private static boolean contains(int[] array,int value) {
		for (int item: array) {
			if (item == value) {
				return true;
			}
		}
		
		return false;
	}
	
	// CONSTRUCTOR
    
    protected Assembler() {
        this.debug = false;
    }
	
	protected Assembler(boolean debug) {
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
	    // ... initialise
	    
        location = 0;
        slot     = 0;
        
        P = 0;
        Arrays.fill(ram,0);

        // ... parse

		F18ALexer         lexer     = new F18ALexer(input);
		CommonTokenStream tokens    = new CommonTokenStream(lexer);
		F18AParser        parser    = new F18AParser(tokens);
		ParseTree         tree      = parser.program(); 
		ParseTreeWalker   walker    = new ParseTreeWalker();

		walker.walk(this,tree); 
		
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
			    case "@p":
			        encode(FETCHP);
		        	break;
			        
			    case "@b":                  
			        encode(FETCHB);
		        	break;
			        
			    case "!b":                  
			        encode(STOREB);
		        	break;

			    case "nop":
			        encode(NOP);
			        break;

			    case "b!":
			        encode(BSTORE);
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
                    encode(FETCHP,RIGHT);
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
            	
                encode(FETCHP,constant & 0x3ffff);
        	}
        }
	}
	
	// INTERNAL
	
	private void encode(int opcode) {
		// ... pad current instruction with NOP ?
		
	    if (slot == 3) {
	    	if (!contains(SLOT3, opcode)) {
	    		encode(NOP);
	    	}
	    }

	    // ... encode into current instruction
	    
	    int rsh  = RSHIFT[slot];
	    int mask = MASK[slot];
	    
	    ram[location] |= (((opcode << 13) >>> rsh) ^ XOR) & mask;
	    slot           = (slot + 1) % 4;
	                    
	    if (slot == 0) {
	    	location = ++P;
	    }
	}
	        
    private void encode(int opcode,int constant) {
        int rsh  = RSHIFT[slot];
        int mask = MASK[slot];
	        
        ram[location] |= (((opcode << 13) >>> rsh) ^ XOR) & mask;
        ram[++P]      |= constant;
        slot           = (slot + 1) % 4;
	                    
        if (slot == 0) {
            location = ++P;
        }
    }

}


