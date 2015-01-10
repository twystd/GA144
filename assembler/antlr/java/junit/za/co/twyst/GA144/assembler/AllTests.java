package za.co.twyst.GA144.assembler;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)

@SuiteClasses({ TestRET.class, 
                TestCALL.class, 
                TestFETCHP.class,
                TestFETCHB.class,
                TestSTOREP.class,
                TestSTOREPLUS.class,
                TestSTOREB.class,
                TestSTORE.class,
                TestMULTIPLY.class,
                TestSHL.class,
                TestSHR.class,
                TestNOT.class,
                TestPLUS.class,
                TestAND.class,
                TestOR.class,
                TestDROP.class, 
                TestDUP.class, 
                TestPOP.class, 
                TestOVER.class, 
                TestA.class, 
                TestNOP.class, 
                TestPUSH.class, 
                TestBSTORE.class,
                TestASTORE.class,
                
	            TestRIGHT.class,
	            TestREAD.class,
	            TestWRITE.class,
	            TestN404.class,
	            TestHCCForth.class
	          })

public class AllTests {
}
