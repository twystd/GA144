------------------------------ MODULE channel ------------------------------

EXTENDS   Integers
VARIABLES channel,operation

StateOK     == channel   \in { "idle","read","read_wait" }
OperationOK == operation \in { "none","read","write" }

Init == /\ channel   = "idle"
        /\ operation = "none"

Next == \/ /\ channel    = "idle"
           /\ channel'   = "idle"
           /\ operation' = "none"
           
        \/ /\ channel    = "idle"
           /\ channel'   = "read"
           /\ operation' = "none"
           
        \/ /\ channel    = "read"
           /\ channel'   = "read_wait"
           /\ operation' = "none"

        \/ /\ channel    = "read_wait"
           /\ channel'   = "idle"
           /\ operation' = "none"
           
           
        
           
=============================================================================
\* Modification History
\* Last modified Tue Oct 21 17:00:30 SAST 2014 by AnthonySeebregts
\* Created Tue Oct 21 16:16:21 SAST 2014 by AnthonySeebregts
