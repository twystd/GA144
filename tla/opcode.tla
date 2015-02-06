------------------------------- MODULE opcode -------------------------------
EXTENDS Integers

VARIABLES opcode,T

RANGE      == -8..7
EDGE_CASES == {-8,-1,0,1,7}
CPU        == << T >>

SHL     == "2*"
SHR     == "2/"
NOT     == "-"
NOP     == "."
UNKNOWN == "?"

OPCODES == { SHL,
             SHR,
             NOT,
             NOP
           }

TIsValid == (T \in RANGE)
OpCodeIsValid == (opcode \in OPCODES) \/ (opcode = "?") 

shl == /\ opcode' = UNKNOWN
       /\ T'      = (T * 2) % 8

shr == /\ opcode' = UNKNOWN
       /\ T'      = T \div 2

not == /\ opcode' = UNKNOWN
       /\ \/ /\ T < 0
             /\ T'= -T - 1
          \/ /\ T = 0
             /\ T'= -1
          \/ /\ T > 0
             /\ T'= -T + 1

nop == /\ opcode' = UNKNOWN
       /\ UNCHANGED << T >>

       
Init == \/ /\ opcode = SHL
           /\ T \in EDGE_CASES
        \/ /\ opcode = SHR
           /\ T \in EDGE_CASES
        \/ /\ opcode = NOT
           /\ T \in EDGE_CASES
        \/ /\ opcode = NOP
           /\ T \in EDGE_CASES
        

Next == \/ /\ opcode = SHL /\ shl
        \/ /\ opcode = SHR /\ shr
        \/ /\ opcode = NOT /\ not
        \/ /\ opcode = NOP /\ nop
        \/ /\ opcode  = UNKNOWN
           /\ UNCHANGED << opcode,CPU >>

=============================================================================
\* Modification History
\* Last modified Fri Feb 06 12:49:42 SAST 2015 by tonyseebregts
\* Created Tue Jan 06 12:42:48 SAST 2015 by tonyseebregts
