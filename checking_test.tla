--------------------------- MODULE checking_test ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, Integers
CONSTANTS Producer, Consumer, QueueSize, QueueTTL
(* expecting to have just 1 producer and consumer thread in each set. *)
(*QueueSize is the total size of the queue/how many items/messages can sit in the queue*)

VARIABLES timeNoConsumer, queueBuffer, waitSet
RunningThreads == (Producer \cup Consumer) \ waitSet

\* queueTTL is a certain value that determines when the queue needs to be deleted. 
\* if the queueBuffer is empty for the duration of queueTTL then it needs to be deleted (i.e it cannot accept put statements anymore)
\* The waitSet is only needed if the producer tries to put an item on the queue if the queue exists, and the queue is full, or if the consumer
\* tries to consumer from an empty queue (if the queue exists)

(**************************************)
(* The initial state of the system *)
(**************************************)

Init == /\ queueBuffer = <<>>
        /\ waitSet = {}
(* There is nothing in the queue, and the waitSet is empty*)

(**************************************)
(* The next state of the system should allow the producer to add something, and consumer to consume something *)
(**************************************)

Put(t, d, s) ==
/\ t \notin waitSet /\ QueueOK(s)
/\ \/ /\ Len(queueBuffer) < QueueSize
      /\ queueBuffer' = Append(queueBuffer, d)
      /\ NotifyOther(t)
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)
      
Next == \/ \E p \in Producer: Put(p, p, s)
        \/ \E c \in Consumer: Get(c)

(****************)
(* action items*)
(****************)

(* Borrowing this *)
Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<queueBuffer>>

(* Borrowing this *)
NotifyOther(t) == 
          LET S == IF t \in Producer THEN waitSet \ Producer ELSE waitSet \ Consumer
          IN IF S # {}
             THEN \E x \in S : waitSet' = waitSet \ {x}
             ELSE UNCHANGED waitSet

\* the queue is still ok if the queue ttl is not expired. or if we still have a consumer running for the queue.        
QueueOK(s) == /\ \/ /\ timeNoConsumer < QueueTTL
                    /\ timeNoConsumer' = timeNoConsumer + s

\* a producer thread can put something on the queue, if the queue exists, meaning the queueTTL did not expire
\* and the queue is not full.

      
Get(t, s) ==
/\ t \notin waitSet /\ QueueOK(s)
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(t)
   \/ /\ buffer = <<>>
      /\ Wait(t)


(* borrowing this because TLC will always check for deadlocks*)
NoDeadLock == waitSet # (Producers \cup Consumers)
======