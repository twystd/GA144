package za.co.twyst.GA144.assembler;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)

@SuiteClasses({ TestNOP.class, 
                TestFETCHP.class,
                TestFETCHB.class,
                TestBSTORE.class,
                TestSTOREB.class,
	            TestRIGHT.class
	          })

public class AllTests {
}
