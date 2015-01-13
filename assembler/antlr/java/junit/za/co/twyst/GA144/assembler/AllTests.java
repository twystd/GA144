package za.co.twyst.GA144.assembler;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)

@SuiteClasses({ TestRET.class,        // 0x00 
                TestEX.class,         // 0x01 
                TestJUMP.class,       // 0x02 
                TestCALL.class,       // 0x03
                TestFETCHP.class,     // 0x08
                TestFETCHPLUS.class,  // 0x09
                
                TestFETCHB.class,     // 0x0a
                TestFETCH.class,      // 0x0b
                TestSTOREP.class,     // 0x0c
                TestSTOREPLUS.class,  // 0x0d
                TestSTOREB.class,     // 0x0e
                TestSTORE.class,      // 0x0f
                
                TestMULTIPLY.class,   // 0x10
                TestSHL.class,        // 0x11
                TestSHR.class,        // 0x12
                TestNOT.class,        // 0x13
                TestPLUS.class,       // 0x14
                TestAND.class,        // 0x15
                TestOR.class,         // 0x16
                TestDROP.class,       // 0x17
                TestDUP.class,        // 0x18
                TestPOP.class,        // 0x19
                TestOVER.class,       // 0x1a
                TestA.class,          // 0x1b
                TestNOP.class,        // 0x1c
                TestPUSH.class,       // 0x1d
                TestBSTORE.class,     // 0x1e
                TestASTORE.class,     // 0x1f
                
	            TestRIGHT.class,
	            TestREAD.class,
	            TestWRITE.class,
	            TestN404.class,
	            TestHCCForth.class
	          })

public class AllTests {
}
