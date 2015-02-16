------------------------------- MODULE opcode -------------------------------
EXTENDS Integers,TLC

VARIABLES opcode,T

RANGE      == -131072..131071
EDGE_CASES == {-131072,-131071,-1,0,1,131071}
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

\* Bitwise AND with sign bit retention 
band (a,b) == IF (a < 0) THEN -bandx(-a,b)  ELSE bandx(a,b)
bandx(a,b) == IF (a > b) THEN a-(b+1) ELSE a

shl == /\ opcode' = UNKNOWN
       /\ T' = band(2*T,131071)

shr == /\ opcode' = UNKNOWN
       /\ T'      = T \div 2

not == /\ opcode' = UNKNOWN
       /\ \/ /\ T < 0
             /\ T'= -T - 1
          \/ /\ T = 0
             /\ T'= -1
          \/ /\ T > 0
             /\ T'= -T + 1
      /\ PrintT(T)
      /\ PrintT(T')

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
\* Last modified Wed Feb 11 12:57:23 SAST 2015 by tonyseebregts
\* Created Tue Jan 06 12:42:48 SAST 2015 by tonyseebregts
