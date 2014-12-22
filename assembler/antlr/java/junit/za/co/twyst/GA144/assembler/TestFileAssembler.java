package za.co.twyst.GA144.assembler;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;

public class TestFileAssembler extends AssemblerTest {
	// CONSTANTS
	
	private static final boolean DEBUG   = true;
	private static final File    BASEDIR = new File("./runtime");
    private static final File    ASM     = new File(BASEDIR,"asm");
    private static final File    BIN     = new File(BASEDIR,"bin");
    private static final File    REF     = new File(BASEDIR,"ref");

	// UNIT TESTS 
	
    @Ignore
	@Test
	public void testN404() throws Exception {
	    verify("N404",DEBUG);
	}
    
    @Ignore
    @Test
    public void testN406() throws Exception {
        verify("N406",DEBUG);
    }

    @Test
    public void testN405() throws Exception {
        verify("N405",DEBUG);
    }

    private void verify(String filename,boolean debug) throws Exception {
        Assembler assembler = new Assembler(debug);
        File      asm       = new File(ASM,filename + ".asm");
        File      bin       = new File(BIN,filename + ".bin");
        File      ref       = new File(REF,filename + ".ref");
        
        bin.delete ();
        assertFalse("Failed to remove '" + bin.getPath() + "'",bin.exists());
        
        assembler.assemble(asm,bin);

        fc(bin,ref);
    }

	// UTILITY FUNCTIONS
	
	private void fc(File fbin,File fref) throws Exception {
		List<String> bin = new ArrayList<String>();
		List<String> ref = new ArrayList<String>();
		
		// .. read into array
		
		try (BufferedReader reader = new BufferedReader(new FileReader(fbin))) {
			String         line;
			
			while((line = reader.readLine()) != null) {
				bin.add(line);
			}
		}
		
		try (BufferedReader reader = new BufferedReader(new FileReader(fref))) {
			String         line;
			
			while((line = reader.readLine()) != null) {
				ref.add(line);
			}
		}
		
		assertEquals("Invalid BIN file size", ref.size(),bin.size());
		
		Iterator<String> ix   = bin.iterator();
		Iterator<String> jx   = ref.iterator();
		int              line = 1;
		
		while(ix.hasNext() && jx.hasNext()) {
			String x = ix.next();
			String y = jx.next();
			
			assertEquals("Error on line " + line,y,x);
			
			line++;
		}
	}
}
