------------------------------- MODULE opcode -------------------------------
EXTENDS Integers

VARIABLES opcode,T

TIsValid == (T \in -8..7) 

Init == \/ /\ opcode = "nop"
           /\ T \in -8..7
        \/ /\ opcode = "shl"
           /\ T\in -8..7

Next == \/ /\ opcode  = "nop"
           /\ opcode' = "?"
           /\ UNCHANGED << T >>
           
        \/ /\ opcode  = "shl"
           /\ opcode' = "?"
           /\ T'      = (T * 2) % 8
           
        \/ /\ opcode  = "?"
           /\ UNCHANGED << opcode,T >>

=============================================================================
\* Modification History
\* Last modified Tue Jan 06 13:59:14 SAST 2015 by tonyseebregts
\* Created Tue Jan 06 12:42:48 SAST 2015 by tonyseebregts
