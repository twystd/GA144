Feature: HCC!Forth
   Runs the demo program from the HCC!Forth ColorForth tutorial

   @ignore   
   Scenario: Run node 404 program only
      Given  Node 404 is initialised from ../cucumber/404.bin
      And    Node XXX listening on RIGHT
      And    Node 404 is reset
      And    Node 404 is stepped 32 times
      Then   Node XXX should have received [6,8]

   @ignore
   Scenario: Run node 406 program only
      Given  Node 406 is initialised from ../cucumber/406.bin
      And    Node XXX listening on LEFT
      And    Node 406 is reset
      And    Node 406 is stepped 33 times
      Then   Node XXX should have received [15,18]

   @ignore
   Scenario: Run node 405 program only
      Given  Node 405 is initialised from ../cucumber/405.bin
      And    Node 405 is reset
      And    Node XXX writes [6,8,10,12,14] to RIGHT
      And    Node XXX writes [15,18,21,24,27] to LEFT
      And    Node XXX listening on DOWN
      And    Node 405 is stepped 21 times
      And    Node 405 is stepped 17 times
      And    Node 405 is stepped 17 times
      And    Node 405 is stepped 17 times
      And    Node 405 is stepped 17 times
      Then   Node XXX should have received [21,26,31,36,41]

   Scenario: Run node 505 program only
      Given  Node 505 is initialised from ../cucumber/505.bin
      And    Node 505 is reset
      And    Node XXX writes [21,26,31,36,41] to DOWN
      And    Node 505 is stepped 1 time
      Then   Node 505 DS should be [21,26,31,36,41]

