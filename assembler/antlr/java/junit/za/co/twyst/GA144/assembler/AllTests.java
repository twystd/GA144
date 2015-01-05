package za.co.twyst.GA144.assembler;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)

@SuiteClasses({ TestCALL.class, 
                TestFETCHP.class,
                TestFETCHB.class,
                TestBSTORE.class,
                TestSHL.class,
                TestSHR.class,
                TestNOT.class,
                TestAND.class,
                TestOR.class,
                TestNOP.class, 
                TestDROP.class, 
                TestDUP.class, 
                TestSTOREB.class,
	            TestRIGHT.class,
	            TestREAD.class,
	            TestWRITE.class,
	            TestN404.class,
	            TestHCCForth.class
	          })

public class AllTests {
}
