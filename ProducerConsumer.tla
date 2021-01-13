---- MODULE ProducerConsumer ----

\* simple model is a queue with a certain ttl set on it.
\* it will be deleted after a certain amount of time has passed where it is unused.
\* we can have at least 1 producer, and 1 consumer on the queue.
\* a consumer can consumer from the queue, or remove things from the queue if its not empty
\* a producer can put something onto the queue if it's not full.
\* the producer and consumer need to wait for each other
\* using https://github.com/lemmy/BlockingQueue/blob/master/BlockingQueue.tla as a template for producers, consumers, queues


EXTENDS TLC, Naturals, Sequences, FiniteSets, Integers
CONSTANTS Producer, Consumer, QueueSize, QueueTTL
(* expecting to have just 1 producer and consumer thread in each set. *)
(*QueueSize is the total size of the queue/how many items/messages can sit in the queue*)
ASSUME Assumption ==
       /\ Producer # {}                      (* at least one producer *)
       /\ Consumer # {}                      (* at least one consumer *)
       /\ Producer \intersect Consumer = {} (* no thread is both consumer and producer *)
       /\ QueueSize \in (Nat \ {0})         (* buffer capacity is at least 1 *)
VARIABLES timeNoConsumer, queueBuffer, waitSet

(**************************************)
(* The initial state of the system *)
(**************************************)

Init == /\ queueBuffer = <<>>
        /\ waitSet = {} 
        /\ timeNoConsumer = 0
(* There is nothing in the queue, and the waitSet is empty*)

RunningThreads == (Producer \cup Consumer) \ waitSet

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
QueueOK == /\ \/ timeNoConsumer < QueueTTL
              \/ \E c \in Consumer: c \in waitSet

\* a producer thread can put something on the queue, if the queue exists, meaning the queueTTL did not expire
\* and the queue is not full.

Put(t, d) ==
/\ t \notin waitSet 
/\ QueueOK
/\ \/ /\ Len(queueBuffer) < QueueSize
      /\ queueBuffer' = Append(queueBuffer, d)
      /\ NotifyOther(t)
   \/ /\ Len(queueBuffer) = QueueSize
      /\ Wait(t)
      
Get(t) ==
/\ t \notin waitSet 
/\ QueueOK
/\ \/ /\ queueBuffer # <<>>
      /\ queueBuffer' = Tail(queueBuffer)
      /\ timeNoConsumer' = 0
      /\ NotifyOther(t)
   \/ /\ queueBuffer = <<>>
      /\ Wait(t)

(**************************************)
(* The next state of the system should allow the producer to add something, and consumer to consume something *)
(**************************************)
Next == /\ \/ /\ \E p \in Producer: Put(p, p)
              /\ timeNoConsumer' = timeNoConsumer + 1
           \/ /\ \E c \in Consumer: Get(c)
              /\ timeNoConsumer' = 0 \* once we can consume from the queue, we reset to 0

(* borrowing this because TLC will always check for deadlocks *)
NoDeadLock == waitSet # (Producer \cup Consumer)

============================================================================================================