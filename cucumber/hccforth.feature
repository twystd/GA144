Feature: HCC!Forth
   Runs the demo program from the HCC!Forth ColorForth tutorial

Scenario: Run node 404 program only
   Given  Node 404 initialised with cucumber/N404.bin
     And  Node 404 is reset
     And  Node 404 is stepped 5 times
    Then  Trace should match cucumber/traces/N404.trace 


Scenario: Run node 406 program only
   Given  Node 406 initialised with cucumber/N406.bin
     And  Node 406 is reset
     And  Node 406 is stepped 5 times
    Then  Trace should match cucumber/traces/N406.trace 

