------------------------------- MODULE opcode -------------------------------
EXTENDS Integers,TLC

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

\% "%05X" % ((-(-0x20001 * 2) & 0x1ffff) + 0x20000)
band(a,b) == a % b 

shl == /\ opcode' = UNKNOWN
       /\ T'      = band((T * 2),131071)
       /\ PrintT(T) 
       /\ PrintT(T')

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
\* Last modified Mon Feb 09 20:30:36 SAST 2015 by tonyseebregts
\* Created Tue Jan 06 12:42:48 SAST 2015 by tonyseebregts
