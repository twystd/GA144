Feature: HCC!Forth
   Runs the demo program from the HCC!Forth ColorForth tutorial
   
Scenario: Run node 404 program only
   Given  Node 404 is initialised from ../cucumber/N404.bin
   And    Node XXX listening on RIGHT
   And    Node 404 is reset
   And    Node 404 is stepped 32 times
   Then   Node XXX should have received 6,8
   
Scenario: Run node 406 program only
   Given  Node 406 is initialised from ../cucumber/N406.bin
   And    Node XXX listening on LEFT
   And    Node 406 is reset
   And    Node 406 is stepped 33 times
   Then   Node XXX should have received 15,18

