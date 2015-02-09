------------------------------- MODULE opcode -------------------------------
EXTENDS Integers

VARIABLES opcode,T

RANGE      == -131072..131071
EDGE_CASES == {-131072,-1,0,1,131071}
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

limit(X) == 1

shl == /\ opcode' = UNKNOWN
       /\ T'      = limit(T * 2)

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
\* Last modified Mon Feb 09 13:03:01 SAST 2015 by tonyseebregts
\* Created Tue Jan 06 12:42:48 SAST 2015 by tonyseebregts
