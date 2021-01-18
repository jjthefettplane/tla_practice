---- MODULE ProducerConsumer ----

\* states of a queue with a queue ttl set:
\* its in an ok/active state = consumer is connected
\* it dne = consumer is not connected and queue ttl is expired.
\* it is redeclared => redeclaration is something that is external to the base queue behavior.
\* the third state of the queue would be the consumer is not connected, but the queue ttl has not yet expired.
\* In this case, if there is a consumer thread waiting in the waitset, we can assume its still conected to the queue.
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
       /\ QueueTTL \in (Nat \ {0})          (* Queue ttl needs to be greater than 1 *)

VARIABLES timeNoConsumer, queueBuffer, waitSet, conState
(* timeNoConsumer is the amount of time passed without the consumer being connected to the queue*)
vars == <<queueBuffer, waitSet>>

(**************************************)
(* The initial state of the system *)
(**************************************)

Init == /\ queueBuffer = <<>>
        /\ waitSet = {} 
        /\ timeNoConsumer = 0
        /\ conState = "connected"
(* The queue buffer is empty, so nothing is yet in the queue. *)
(* The wait set is also empty. *)
(* We start off the timer for no consumer connected, assume that the consumer starts off as being connected to the queue *)

RunningThreads == (Producer \cup Consumer) \ waitSet

(****************)
(* action items*)
(****************)

(* Borrowing this. If a consumer or a producer thread cannot take action, they must wait *)
Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ IF t \in Consumer 
              THEN conState' = "!connected" 
              ELSE UNCHANGED conState
           /\ UNCHANGED <<queueBuffer>>

(* Borrowing this. once a put or get action is done, the other threads need to be notified. *)
NotifyOther(t) == 
          LET S == IF t \in Producer THEN waitSet \ Producer ELSE waitSet \ Consumer
          IN IF S # {}
             THEN \E x \in S : waitSet' = waitSet \ {x}
             ELSE UNCHANGED waitSet

(* Determine if the queue is in a 'good' state *)
(* TTL must not be expired, the consumer must be connected *)
(* if the consumer is waiting and the TTL is not expired, then the queue is still valid *)
QueueOK == /\ \/ /\ timeNoConsumer < QueueTTL 
                 /\ conState = "connected"           
              \/ /\ \E c \in Consumer: c \in waitSet 
                 /\ timeNoConsumer < QueueTTL
              \/ timeNoConsumer < QueueTTL

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
      /\ NotifyOther(t)
   \/ /\ queueBuffer = <<>>
      /\ Wait(t)

(**************************************)
(* The next state of the system should allow the producer to add something, and consumer to consume something *)
(**************************************)
Next == /\ \/ /\ \E p \in Producer: Put(p, p) 
              /\ conState' = "!connected"          
              /\ timeNoConsumer' = timeNoConsumer + 1    
           \/ /\ \E c \in Consumer: Get(c) 
              /\ conState' = "connected"
              /\ timeNoConsumer' = 0 

(* borrowing this because TLC will always check for deadlocks *)
NoDeadLock == waitSet # (Producer \cup Consumer)

THEOREM Init /\ [][Next]_vars => []NoDeadLock

============================================================================================================