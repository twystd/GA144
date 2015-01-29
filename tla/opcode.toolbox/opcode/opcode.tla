------------------------------- MODULE opcode -------------------------------
EXTENDS Integers

VARIABLES opcode,T

CPU     == << T >>

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

TIsValid == (T \in -8..7)
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
           /\ T\in -8..7
        \/ /\ opcode = SHR
           /\ T\in -8..7
        \/ /\ opcode = NOT
           /\ T\in -8..7
        \/ /\ opcode = NOP
           /\ T \in -8..7
        

Next == \/ /\ opcode = SHL /\ shl
        \/ /\ opcode = SHR /\ shr
        \/ /\ opcode = NOT /\ not
        \/ /\ opcode = NOP /\ nop
        \/ /\ opcode  = UNKNOWN
           /\ UNCHANGED << opcode,CPU >>

=============================================================================
\* Modification History
\* Last modified Thu Jan 29 12:30:09 SAST 2015 by tonyseebregts
\* Created Tue Jan 06 12:42:48 SAST 2015 by tonyseebregts
