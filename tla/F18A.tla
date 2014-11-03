-------------------------------- MODULE F18A --------------------------------

EXTENDS  Integers
VARIABLE P                                       \* Register P: program counter
VARIABLE slot                                    \* 'slot' counter for instruction decoding (interim)
   
PIsValid    == (P \in 0..511) 
SlotIsValid == (slot \in 0..3)

Reset == /\ P = 170                            \* P = 0x0AA
         /\ slot = 0                           \* slot = 0

Decode0 == /\ slot  = 0                        \* Instruction decoding for slot 0
           /\ slot' = 1
           /\ P'    = P

Decode1 == /\ slot  = 1                        \* Instruction decoding for slot 1
           /\ slot' = 2
           /\ P'    = P
           
Decode2 == /\ slot  = 2                        \* Instruction decoding for slot 2
           /\ slot' = 3
           /\ P'    = P  

Decode3RAM == /\ slot = 3                      \* Instruction decoding for slot 3
              /\ P \in 0..127                  \* RAM
              /\ P'    = (P + 1) % 128
              /\ slot' = 0

Decode3ROM == /\ slot = 3                      \* Instruction decoding for slot 3
              /\ P \in 128..255                \* ROM
              /\ P'    = ((P - 128 + 1) % 128) + 128
              /\ slot' = 0

Decode3IO == /\ slot = 3                       \* Instruction decoding for slot 3
             /\ P \in 256..511                      \* I/O
             /\ P'    = P
             /\ slot' = 0
           
Run ==  \/ Decode0
        \/ Decode1
        \/ Decode2
        \/ Decode3RAM
        \/ Decode3ROM
        \/ Decode3IO
       
=============================================================================
\* Modification History
\* Last modified Mon Nov 03 19:50:45 SAST 2014 by tonys
\* Created Fri Oct 17 19:13:19 SAST 2014 by tonys
