------------------------------ MODULE channel ------------------------------
EXTENDS Integers

VARIABLES N404,N405

Init == /\ N404 = "idle"
        /\ N405 = "idle"
        
N404Idle == /\ N404  = "idle"
            /\ N404' = "idle"
            /\ N405' = N405
        
N405Idle == /\ N405  = "idle"
            /\ N404' = N405
            /\ N405' = "idle"

N404Write == /\ N404  = "idle"
             /\ N405  = "idle"
             /\ N404' = "write"
             /\ N405' = N405

N404WriteWait == /\ N404  = "write"
                 /\ N405  = "idle"
                 /\ N404' = N404
                 /\ N405' = N405

N405Read == /\ N404  = "idle"
            /\ N405  = "idle"
            /\ N404' = N404
            /\ N405' = "read"

N405ReadWait == /\ N404  = "idle"
                /\ N405  = "read"
                /\ N404' = N404
                /\ N405' = N405

ReadWrite == /\ N404  = "write"
             /\ N405  = "read"
             /\ N404' = "write ok"
             /\ N405' = "read ok"

N404WriteOk == /\ N404  = "write ok"
               /\ N404' = "idle"
               /\ N405' = N405

N405ReadOk == /\ N405  = "read ok"
              /\ N404' = N404
              /\ N405' = "idle"
      
Reset == /\ N404' = "idle"
         /\ N405' = "idle"
                                           
Next == \/ N404Idle
        \/ N405Idle
        \/ N404Write
        \/ N404WriteWait
        \/ N405Read
        \/ N405ReadWait
        \/ ReadWrite
        \/ N404WriteOk
        \/ N405ReadOk
        \/ Reset

=============================================================================
\* Modification History
\* Last modified Tue Nov 04 21:04:29 SAST 2014 by tonys
\* Created Tue Nov 04 20:43:25 SAST 2014 by tonys
