package za.co.twyst.GA144.assembler;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.PrintWriter;
import java.util.Arrays;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import za.co.twyst.GA144.assembler.antlr.F18ABaseListener;
import za.co.twyst.GA144.assembler.antlr.F18ALexer;
import za.co.twyst.GA144.assembler.antlr.F18AParser;
import za.co.twyst.GA144.assembler.antlr.F18AParser.CommentContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.LabelContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.OpcodeContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.OriginContext;
import za.co.twyst.GA144.assembler.antlr.F18AParser.ProgramContext;

public class Assembler extends F18ABaseListener {
	// CONSTANTS
	
	// INSTANCE VARIABLES
	
	private int   origin;
	private int   pc;
	private int[] ram = new int[64];
	
	// ENTRY POINT
	
	public static void main(String[] args) {
		// ... parse command line arguments
		
		File in  = null;
		File out = null;
		int  ix  = 0;
		
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
		
		try (InputStream istream = new FileInputStream (in)) {
			ANTLRInputStream  input     = new ANTLRInputStream(istream);
			F18ALexer         lexer     = new F18ALexer(input);
			CommonTokenStream tokens    = new CommonTokenStream(lexer);
			F18AParser        parser    = new F18AParser(tokens);
			ParseTree         tree      = parser.program(); 
			ParseTreeWalker   walker    = new ParseTreeWalker();
			Assembler         assembler = new Assembler();

			walker.walk       (assembler,tree); 
			assembler.assemble(out);
			
		} catch(Throwable x) {
			System.err.println("ERROR: " + x);
		}
	}
	
	// CONSTRUCTOR
	
	private Assembler() {
		Arrays.fill(ram,0);
	}

	// INSTANCE METHODS
	
	private void assemble(File file) throws Exception {
		try (PrintWriter writer = new PrintWriter(file)) {
			writer.println(String.format("%-8s org %d","xx",origin));
			writer.println();
			
			for (int i=0; i<ram.length; i++) {
				writer.println(String.format("%04X  %04X",i,ram[i]));
			}
		}
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
		this.origin = Integer.parseInt(ctx.ORIGIN().getText());
		this.pc     = Integer.parseInt(ctx.ORIGIN().getText());
	}

	@Override
	public void exitOrigin(OriginContext ctx) {
	}

	@Override
	public void enterComment(CommentContext ctx) {
	}

	@Override
	public void exitComment(CommentContext ctx) {
	}

	@Override
	public void enterLabel(LabelContext ctx) {
	}

	@Override
	public void exitLabel(LabelContext ctx) {
	}

	@Override
	public void enterOpcode(OpcodeContext ctx) {
		String opcode = ctx.OPCODE().getText();
		
		switch(opcode) {
			case "nop":
				ram[pc++] = 0x8888;
				break;
		}
	}

	@Override
	public void exitOpcode(OpcodeContext ctx) {
	}
}
