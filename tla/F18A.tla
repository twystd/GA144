-------------------------------- MODULE F18A --------------------------------

EXTENDS  Integers
VARIABLE P                                       \* Register P: program counter

P_IsValid == (P \in 0..511) 

Reset == (P = 170)                               \* P = 0x0AA

Run == \/ /\ P \in 0..127                        \* RAM
          /\ P' = (P + 1) % 128
       \/ /\ P \in 128..255                      \* ROM
          /\ P' = ((P - 128 + 1) % 128) + 128
       \/ /\ P \in 256..511                      \* I/O
          /\ P' = P
       
=============================================================================
\* Modification History
\* Last modified Fri Oct 17 20:24:21 SAST 2014 by tonys
\* Created Fri Oct 17 19:13:19 SAST 2014 by tonys
