package za.co.twyst.GA144.assembler;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.antlr.v4.runtime.tree.TerminalNode;

import za.co.twyst.GA144.assembler.antlr.F18ABaseListener;
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
import za.co.twyst.GA144.assembler.instructions.Down;
import za.co.twyst.GA144.assembler.instructions.Instruction;
import za.co.twyst.GA144.assembler.instructions.Label;
import za.co.twyst.GA144.assembler.instructions.Left;
import za.co.twyst.GA144.assembler.instructions.Origin;
import za.co.twyst.GA144.assembler.instructions.Right;
import za.co.twyst.GA144.assembler.instructions.OpCode;
import za.co.twyst.GA144.assembler.instructions.OpCode.OPCODE;

public class F18AListener extends F18ABaseListener {
	// CONSTANTS
	
    private static final Pattern CONSTANT = Pattern.compile("([\\-]?[0-9]+)"); 
    private static final Pattern HEX      = Pattern.compile("([a-fA-F0-9]+)H"); 
    private static final int     MAXINT   = 262144;

	// INSTANCE VARIABLES
	
    private final boolean           debug;
	private final List<Instruction> instructions = new ArrayList<Instruction>();
	
	// CONSTRUCTOR
    
    protected F18AListener(boolean debug) {
        this.debug = debug;
    }

    // PROPERTIES
    
    public List<Instruction> instructions() {
    	return instructions;
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
		String  address = ctx.address().NUMBER().getText();
		Matcher matcher;
		
		if ((matcher = HEX.matcher(address)).matches()) {
			instructions.add(new Origin(Integer.parseInt(matcher.group(1),16)));
		} else {
			instructions.add(new Origin(Integer.parseInt(address)));
		}
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
	        
	        lookup:
	        for (OPCODE opcode: OpCode.OPCODE.values()) {
	        	for (String mnemonic: opcode.mnemonic) {
	        		if (mnemonic.equals(node.getText())) {
	        			instructions.add(new OpCode(opcode));
	        			break lookup;
	        		}
	        	}
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
                    
                case "left":
                    instructions.add(new Left());
                    break;
                    
                case "down":
                    instructions.add(new Down());
                    break;
                    
                default:
                    System.err.println("WARNING: unrecognised word '" + node.getText() + "'");
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
}


