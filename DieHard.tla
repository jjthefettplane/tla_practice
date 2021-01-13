---- MODULE DieHard ----
EXTENDS TLC, Integers
VARIABLES small, big

(* The next state formula describes all
permitted steps that can be a next step.
it's usually written as 
F1 \/ F2 ... \/ Fn where each Fi allows a different step.*)

(*We allow 3 different kinds of steps
fill a jug
empty a jug
pour from one jug to another
We need to end up with 4 gallons of water in the big jug
*) 

BadBig == big # 4

TypeOK == /\ small \in 0..3 
          /\ big   \in 0..5

Init == /\ big   = 0 
        /\ small = 0

FillSmall == /\ small' = 3 \* the max volume of the small jug
             /\ big'   = big

FillBig == /\ big'   = 5 \* the max volume of the big jug
           /\ small' = small

EmptySmall == /\ small' = 0 
              /\ big'   = big

EmptyBig == /\ big'   = 0 
            /\ small' = small

SmallToBig == IF big + small =< 5
               THEN /\ big'   = big + small
                    /\ small' = 0
               ELSE /\ big'   = 5
                    /\ small' = small - (5 - big)

BigToSmall == IF big + small =< 3
               THEN /\ big'   = 0 
                    /\ small' = big + small
               ELSE /\ big'   = small - (3 - big)
                    /\ small' = 3

Next == \/ FillSmall 
        \/ FillBig    
        \/ EmptySmall 
        \/ EmptyBig    
        \/ SmallToBig    
        \/ BigToSmall   

====