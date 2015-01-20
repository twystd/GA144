------------------------------- MODULE opcode -------------------------------
EXTENDS Integers

VARIABLES opcode,T

CPU     == << T >>
OPCODES == { "nop",
             "shl" 
           }

TIsValid == (T \in -8..7)
OpCodeIsValid == (opcode \in OPCODES) \/ (opcode = "?") 

nop == /\ opcode = "nop"
       /\ opcode' = "?"
       /\ UNCHANGED << T >>

shl == /\ opcode  = "shl"
       /\ opcode' = "?"
       /\ T'      = (T * 2) % 8
       
Init == \/ /\ opcode = "nop"
           /\ T \in -8..7
        \/ /\ opcode = "shl"
           /\ T\in -8..7

Next == \/ nop
        \/ shl
        \/ /\ opcode  = "?"
           /\ UNCHANGED << opcode,CPU >>

=============================================================================
\* Modification History
\* Last modified Tue Jan 20 15:26:45 SAST 2015 by tonyseebregts
\* Created Tue Jan 06 12:42:48 SAST 2015 by tonyseebregts
