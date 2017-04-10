------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* This is a TLA+ specification of the Paxos Consensus algorithm,          *)
(* described in                                                            *)
(*                                                                         *)
(*  Paxos Made Simple:                                                     *)
(*   http://research.microsoft.com/en-us/um/people/lamport/pubs/pubs.html#paxos-simple *)
(*                                                                         *)
(* and a TLAPS-checked proof of its correctness.  This was mostly done as  *)
(* a test to see how the SMT backend of TLAPS is now working.              *)
(***************************************************************************)
EXTENDS Integers, TLAPS, TLC

CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}                 

(***************************************************************************)
(* The following lemma is an immediate consequence of the assumption.      *)
(***************************************************************************)
LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
BY QuorumAssumption

Ballots == Nat

VARIABLES msgs,    \* The set of messages that have been sent.
          maxBal,  \* maxBal[a] is the highest-number ballot acceptor a
                   \*   has participated in.
          maxVBal, \* maxVBal[a] is the highest ballot in which a has
          maxVal   \*   voted, and maxVal[a] is the value it voted for
                   \*   in that ballot.

vars == <<msgs, maxBal, maxVBal, maxVal>>

Send(m) == msgs' = msgs \cup {m}

None == CHOOSE v : v \notin Values

LEMMA NoneNotAValue == None \notin Values
BY NoSetContainsEverything DEF None

Init == /\ msgs = {}
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxBal  = [a \in Acceptors |-> -1]
        /\ maxVal  = [a \in Acceptors |-> None]

(***************************************************************************)
(* Phase 1a: A leader selects a ballot number b and sends a 1a message     *)
(* with ballot b to a majority of acceptors.  It can do this only if it    *)
(* has not already sent a 1a message for ballot b.                         *)
(***************************************************************************)
Phase1a(b) == /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
              /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxVBal, maxBal, maxVal>>
              
(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b and with the highest-numbered ballot   *)
(* (if any) for which it has voted for a value and the value it voted for  *)
(* in that ballot.  That promise is made in a 1b message.                  *)
(***************************************************************************)
Phase1b(a) == 
  \E m \in msgs : 
     /\ m.type = "1a"
     /\ m.bal > maxBal[a]
     /\ Send([type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a], 
               maxVal |-> maxVal[a], acc |-> a])
     /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
     /\ UNCHANGED <<maxVBal, maxVal>>
        
(***************************************************************************)
(* Phase 2a: If the leader receives a response to its 1b message (for      *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b with a value v, where v is the     *)
(* value of the highest-numbered proposal among the responses, or is any   *)
(* value if the responses reported no proposals.  The leader can send only *)
(* one 2a message for any ballot.                                          *)
(***************************************************************************)
Phase2a(b) ==
  /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b) 
  /\ \E v \in Values :
       /\ \E Q \in Quorums :
            \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
               /\ \A a \in Q : \E m \in S : m.acc = a
               /\ \/ \A m \in S : m.maxVBal = -1
                  \/ \E c \in 0..(b-1) : 
                        /\ \A m \in S : m.maxVBal =< c
                        /\ \E m \in S : /\ m.maxVBal = c
                                        /\ m.maxVal = v
       /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot numbered    *)
(* b, it votes for the message's value in ballot b unless it has already   *)
(* responded to a 1a request for a ballot number greater than or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
Phase2b(a) == 
  \E m \in msgs :
    /\ m.type = "2a" 
    /\ m.bal >= maxBal[a]
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a] = m.val]

Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a) 

Spec == Init /\ [][Next]_vars       
-----------------------------------------------------------------------------
(***************************************************************************)
(* How a value is chosen:                                                  *)
(*                                                                         *)
(* This spec does not contain any actions in which a value is explicitly   *)
(* chosen (or a chosen value learned).  Wnat it means for a value to be    *)
(* chosen is defined by the operator Chosen, where Chosen(v) means that v  *)
(* has been chosen.  From this definition, it is obvious how a process     *)
(* learns that a value has been chosen from messages of type "2b".         *)
(***************************************************************************)
VotedForIn(a, v, b) == \E m \in msgs : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
-----------------------------------------------------------------------------
(***************************************************************************)
(* This section of the spec defines the invariant Inv.                     *)
(***************************************************************************)
Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : Values \cup {None}, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : Values]
            \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]
        

TypeOK == /\ msgs \in SUBSET Messages
          /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
          /\ maxBal \in  [Acceptors -> Ballots \cup {-1}]
          /\ maxVal \in  [Acceptors -> Values \cup {None}]
          /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]

(***************************************************************************)
(* WontVoteIn(a, b) is a predicate that implies that a has not voted and   *)
(* never will vote in ballot b.                                            *)
(***************************************************************************)                                       
WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedForIn(a, v, b)
                    /\ maxBal[a] > b

(***************************************************************************)
(* The predicate SafeAt(v, b) implies that no value other than perhaps v   *)
(* has been or ever will be chosen in any ballot numbered less than b.     *)
(***************************************************************************)                   
SafeAt(v, b) == 
  \A c \in 0..(b-1) :
    \E Q \in Quorums : 
      \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)

MsgInv ==
  \A m \in msgs : 
    /\ (m.type = "1b") => /\ m.bal =< maxBal[m.acc]
                          /\ \/ /\ m.maxVal \in Values
                                /\ m.maxVBal \in Ballots
                                \* conjunct strengthened 2014/04/02 sm
                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
\*                                /\ SafeAt(m.maxVal, m.maxVBal)
                             \/ /\ m.maxVal = None
                                /\ m.maxVBal = -1
                          \** conjunct added 2014/03/29 sm
                          /\ \A c \in (m.maxVBal+1) .. (m.bal-1) : 
                                ~ \E v \in Values : VotedForIn(m.acc, v, c)
    /\ (m.type = "2a") => 
         /\ SafeAt(m.val, m.bal)
         /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal)
                                => (ma = m)
    /\ (m.type = "2b") => 
         /\ \E ma \in msgs : /\ ma.type = "2a"
                             /\ ma.bal  = m.bal
                             /\ ma.val  = m.val
         /\ m.bal =< maxVBal[m.acc]

(***************************************************************************)
(* The following two lemmas are simple consequences of the definitions.    *)
(***************************************************************************)
LEMMA VotedInv == 
        MsgInv /\ TypeOK => 
            \A a \in Acceptors, v \in Values, b \in Ballots :
                VotedForIn(a, v, b) => SafeAt(v, b) /\ b =< maxVBal[a]
BY DEF VotedForIn, MsgInv, Messages, TypeOK

LEMMA VotedOnce == 
        MsgInv =>  \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
                       VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
BY DEF MsgInv, VotedForIn

AccInv ==
  \A a \in Acceptors:
    /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
    /\ maxVBal[a] =< maxBal[a]
    \* conjunct strengthened corresponding to MsgInv 2014/04/02 sm
    /\ (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])  \* SafeAt(maxVal[a], maxVBal[a])
    \* conjunct added corresponding to MsgInv 2014/03/29 sm
    /\ \A c \in Ballots : c > maxVBal[a] => ~ \E v \in Values : VotedForIn(a, v, c)
                                       
(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)
Inv == TypeOK /\ MsgInv /\ AccInv
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma shows that (the invariant implies that) the         *)
(* predicate SafeAt(v, b) is stable, meaning that once it becomes true, it *)
(* remains true throughout the rest of the excecution.                     *)
(***************************************************************************)
LEMMA SafeAtStable == Inv /\ Next /\ TypeOK' => 
                          \A v \in Values, b \in Ballots:
                                  SafeAt(v, b) => SafeAt(v, b)'
<1> SUFFICES ASSUME Inv, Next, TypeOK',
                    NEW v \in Values, NEW b \in Ballots, SafeAt(v, b)
             PROVE  SafeAt(v, b)'
  OBVIOUS
<1> USE DEF Send, Inv, Ballots
<1> USE TRUE /\ TRUE
<1>1. ASSUME NEW bb \in Ballots, Phase1a(bb)
      PROVE  SafeAt(v, b)'
  BY <1>1, SMT DEF SafeAt, Phase1a, VotedForIn, WontVoteIn
<1>2. ASSUME NEW a \in Acceptors, Phase1b(a)
      PROVE  SafeAt(v, b)'
  BY <1>2, QuorumAssumption, SMTT(60) DEF TypeOK, SafeAt, WontVoteIn, VotedForIn, Phase1b
<1>3. ASSUME NEW bb \in Ballots, Phase2a(bb)
      PROVE  SafeAt(v, b)'
  BY <1>3, QuorumAssumption, SMT DEF TypeOK, SafeAt, WontVoteIn, VotedForIn, Phase2a
<1>4. ASSUME NEW a \in Acceptors, Phase2b(a)
      PROVE  SafeAt(v, b)'
  <2>1. PICK m \in msgs : Phase2b(a)!(m)
    BY <1>4 DEF Phase2b
  <2>2 \A aa \in Acceptors, bb \in Ballots, vv \in Values :
            VotedForIn(aa, vv, bb) => VotedForIn(aa, vv, bb)'
    BY <2>1 DEF TypeOK, VotedForIn
  <2>3. \A aa \in Acceptors, bb \in Ballots : maxBal[aa] > bb => maxBal'[aa] > bb
    BY <2>1 DEF TypeOK
  <2>4. ASSUME NEW aa \in Acceptors, NEW bb \in Ballots,
               WontVoteIn(aa, bb), NEW vv \in Values,
               VotedForIn(aa, vv, bb)'
        PROVE FALSE
    <3> DEFINE mm == [type |-> "2b", val |-> vv, bal |-> bb, acc |-> aa]
    <3>1. mm \notin msgs
      BY <2>4 DEF WontVoteIn, VotedForIn
    <3>2. mm \in msgs'
      <4>1. PICK m1 \in msgs' :
              /\ m1.type = "2b"
              /\ m1.val = vv
              /\ m1.bal = bb
              /\ m1.acc = aa
        BY <2>4 DEF VotedForIn
      <4>. QED  BY <4>1 DEF TypeOK, Messages \* proved by Zenon
    <3>3. aa = a /\ m.bal = bb
      BY <2>1, <3>1, <3>2 DEF TypeOK
    <3>. QED
      BY <2>1, <2>4, <3>3 DEF Phase2b, WontVoteIn, TypeOK 
  <2>5 \A aa \in Acceptors, bb \in Ballots : WontVoteIn(aa, bb) => WontVoteIn(aa, bb)'
    BY <2>3, <2>4 DEF WontVoteIn
  <2> QED
    BY <2>2, <2>5, QuorumAssumption DEF SafeAt
                         
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballots
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, AccInv, MsgInv, VotedForIn
  
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, Next
               PROVE  Inv'
    BY DEF vars, Inv, TypeOK, MsgInv, AccInv, SafeAt, VotedForIn, WontVoteIn
  <2> USE DEF Inv
  <2>1. TypeOK'
    <3>1. ASSUME NEW b \in Ballots, Phase1a(b) PROVE TypeOK'
      BY <3>1 DEF TypeOK, Phase1a, Send, Messages
    <3>2. ASSUME NEW b \in Ballots, Phase2a(b) PROVE TypeOK'
      <4>1. PICK v \in Values :
               /\ Send([type |-> "2a", bal |-> b, val |-> v])
               /\ UNCHANGED <<maxBal, maxVBal, maxVal>>
        BY <3>2 DEF Phase2a
      <4>. QED
        BY <4>1 DEF TypeOK, Send, Messages
    <3>3. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE TypeOK'
      <4>. PICK m \in msgs : Phase1b(a)!(m)
        BY <3>3 DEF Phase1b
      <4>. QED
        BY DEF Send, TypeOK, Messages
    <3>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE TypeOK'
      <4>. PICK m \in msgs : Phase2b(a)!(m)
        BY <3>4 DEF Phase2b
      <4>. QED 
        BY DEF Send, TypeOK, Messages
    <3>. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Next
  <2>2. AccInv'
    <3>1. ASSUME NEW b \in Ballots, Phase1a(b) PROVE AccInv'
      BY <2>1, <3>1, SafeAtStable DEF AccInv, TypeOK, Phase1a, VotedForIn, Send
    <3>2. ASSUME NEW b \in Ballots, Phase2a(b) PROVE AccInv'
        BY <2>1, <3>2, SafeAtStable DEF AccInv, TypeOK, Phase2a, VotedForIn, Send
    <3>3. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE AccInv'
        BY <2>1, <3>3, SafeAtStable DEF AccInv, TypeOK, Phase1b, VotedForIn, Send
    <3>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE AccInv'
      <4>1. PICK m \in msgs : Phase2b(a)!(m)
        BY <3>4 DEF Phase2b
      <4>2. \A acc \in Acceptors : 
               /\ maxVal'[acc] = None <=> maxVBal'[acc] = -1
               /\ maxVBal'[acc] =< maxBal'[acc]
        BY <2>1, <4>1, NoneNotAValue DEF AccInv, TypeOK, Messages
      <4>3. \A aa,vv,bb : VotedForIn(aa,vv,bb)' <=>
                          VotedForIn(aa,vv,bb) \/ (aa = a /\ vv = maxVal'[a] /\ bb = maxVBal'[a])
        BY <4>1, Isa DEF VotedForIn, Send, TypeOK, Messages
      <4>4. ASSUME NEW acc \in Acceptors, maxVBal'[acc] >= 0
            PROVE  VotedForIn(acc, maxVal[acc], maxVBal[acc])'
        BY <4>1, <4>3, <4>4 DEF AccInv, TypeOK
      <4>5. ASSUME NEW acc \in Acceptors, NEW c \in Ballots, c > maxVBal'[acc],
                   NEW v \in Values, VotedForIn(acc, v, c)'
            PROVE  FALSE
        BY <4>1, <4>3, <4>5, <2>1 DEF AccInv, TypeOK
      <4>. QED  BY <4>2, <4>4, <4>5 DEF AccInv
    <3>. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Next
  <2>3. MsgInv'
    <3>1. ASSUME NEW b \in Ballots, Phase1a(b)
          PROVE  MsgInv'
      <4>1. \A aa,vv,bb : VotedForIn(aa,vv,bb)' <=> VotedForIn(aa,vv,bb)
        BY <3>1 DEF Phase1a, Send, VotedForIn
      <4>. QED
        BY <3>1, <4>1, SafeAtStable, <2>1 DEF Phase1a, MsgInv, TypeOK, Messages, Send
    <3>2. ASSUME NEW a \in Acceptors, Phase1b(a)
          PROVE  MsgInv'
      <4>. PICK m \in msgs : Phase1b(a)!(m)
        BY <3>2 DEF Phase1b
      <4>1. \A aa,vv,bb : VotedForIn(aa,vv,bb)' <=> VotedForIn(aa,vv,bb)
        BY DEF Send, VotedForIn
      <4>. DEFINE mm == [type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a], 
                         maxVal |-> maxVal[a], acc |-> a]
      <4>2. mm.bal =< maxBal'[mm.acc]
        BY DEF TypeOK, Messages
      <4>3. \/ /\ mm.maxVal \in Values
               /\ mm.maxVBal \in Ballots
               /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)
            \/ /\ mm.maxVal = None
               /\ mm.maxVBal = -1
        BY DEF TypeOK, AccInv
      <4>4. \A c \in (mm.maxVBal+1) .. (mm.bal-1) :
                ~ \E v \in Values : VotedForIn(mm.acc, v, c)
        BY DEF AccInv, TypeOK, Messages
      <4>. QED
        BY <4>1, <4>2, <4>3, <4>4, SafeAtStable DEF MsgInv, TypeOK, Messages, Send
    <3>3. ASSUME NEW b \in Ballots, Phase2a(b)
          PROVE  MsgInv'
      <4>1. ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
        BY <3>3 DEF Phase2a
      <4>1a. UNCHANGED <<maxBal, maxVBal, maxVal>>
        BY <3>3 DEF Phase2a
      <4>2. PICK v \in Values :
               /\ \E Q \in Quorums : 
                     \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
                        /\ \A a \in Q : \E m \in S : m.acc = a
                        /\ \/ \A m \in S : m.maxVBal = -1
                           \/ \E c \in 0..(b-1) : 
                                 /\ \A m \in S : m.maxVBal =< c
                                 /\ \E m \in S : /\ m.maxVBal = c
                                                 /\ m.maxVal = v
               /\ Send([type |-> "2a", bal |-> b, val |-> v])
        BY <3>3 DEF Phase2a
      <4>. DEFINE mm == [type |-> "2a", bal |-> b, val |-> v]
      <4>3. msgs' = msgs \cup {mm}
        BY <4>2 DEF Send
      <4>4. \A aa, vv, bb : VotedForIn(aa,vv,bb)' <=> VotedForIn(aa,vv,bb)
        BY <4>3 DEF VotedForIn
      <4>6. \A m,ma \in msgs' : m.type = "2a" /\ ma.type = "2a" /\ ma.bal = m.bal
                                => ma = m
        BY <4>1, <4>3, Isa DEF MsgInv
      <4>10. SafeAt(v,b)
        <5>0. PICK Q \in Quorums, 
                   S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
                     /\ \A a \in Q : \E m \in S : m.acc = a
                     /\ \/ \A m \in S : m.maxVBal = -1
                        \/ \E c \in 0..(b-1) : 
                              /\ \A m \in S : m.maxVBal =< c
                              /\ \E m \in S : /\ m.maxVBal = c
                                              /\ m.maxVal = v
          BY <4>2, Zenon
        <5>1. CASE \A m \in S : m.maxVBal = -1
          \* In that case, no acceptor in Q voted in any ballot less than b,
          \* by the last conjunct of MsgInv for type "1b" messages, and that's enough
          BY <5>1, <5>0 DEF TypeOK, MsgInv, SafeAt, WontVoteIn
        <5>2. ASSUME NEW c \in 0 .. (b-1),
                     \A m \in S : m.maxVBal =< c,
                     NEW ma \in S, ma.maxVBal = c, ma.maxVal = v
              PROVE  SafeAt(v,b)
          <6>. SUFFICES ASSUME NEW d \in 0 .. (b-1)
                        PROVE  \E QQ \in Quorums : \A q \in QQ : 
                                  VotedForIn(q,v,d) \/ WontVoteIn(q,d)
            BY DEF SafeAt
          <6>1. CASE d \in 0 .. (c-1)
            \* The "1b" message for v with maxVBal value c must have been safe
            \* according to MsgInv for "1b" messages and lemma VotedInv, 
            \* and that proves the assertion
            BY <5>2, <6>1, VotedInv DEF SafeAt, MsgInv, TypeOK, Messages
          <6>2. CASE d = c
            <7>1. VotedForIn(ma.acc, v, c)
              BY <5>2 DEF MsgInv
            <7>2. \A q \in Q, w \in Values : VotedForIn(q, w, c) => w = v
              BY <7>1, VotedOnce, QuorumAssumption DEF TypeOK, Messages
            <7>3. \A q \in Q : maxBal[q] > c
              BY <5>0 DEF MsgInv, TypeOK, Messages
            <7>. QED
              BY <6>2, <7>2, <7>3 DEF WontVoteIn
          <6>3. CASE d \in (c+1) .. (b-1)
            \* By the last conjunct of MsgInv for type "1b" messages, no acceptor in Q
            \* voted at any of these ballots.
            BY <6>3, <5>0, <5>2 DEF MsgInv, TypeOK, Messages, WontVoteIn
          <6>. QED  BY <6>1, <6>2, <6>3
        <5>. QED  BY <5>0, <5>1, <5>2
      <4>11. SafeAt(mm.val,mm.bal)'
        BY <4>10, <2>1, SafeAtStable
      <4>. QED
\*        This proof used to work.
         BY <2>1, <4>1a, <4>3, <4>4, <4>6, <4>11, SafeAtStable, Zenon
           DEF MsgInv, TypeOK, Messages
\*        The following decomposition added by LL on 21 Nov 2014 because
\*        Zenon failed on this proof.  However, ZenonT(200) worked.
(*
        <5> SUFFICES ASSUME NEW m \in msgs'
                    PROVE MsgInv!(m)'
         BY DEF MsgInv
         
       <5>1. m.type = "1b"
              => (/\ m.bal =< maxBal[m.acc]
                  /\ \/ /\ m.maxVal \in Values
                        /\ m.maxVBal \in Nat
                        /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                     \/ /\ m.maxVal = None
                        /\ m.maxVBal = -1
                  /\ \A c \in m.maxVBal + 1..m.bal - 1 :
                        ~(\E v_1 \in Values : VotedForIn(m.acc, v_1, c)))'
         BY <2>1, <4>1a, <4>3, <4>4, <4>6, <4>11, SafeAtStable \*, Zenon
           DEF MsgInv, TypeOK, Messages

       <5>2.  m.type = "2a"
              => (/\ SafeAt(m.val, m.bal)
                  /\ \A ma \in msgs :
                        ma.type = "2a" /\ ma.bal = m.bal => ma = m)'
         BY <2>1, <4>1a, <4>3, <4>4, <4>6, <4>11, SafeAtStable \*, Zenon
           DEF MsgInv, TypeOK, Messages

       <5>3. m.type = "2b"
              => (/\ \E ma \in msgs :
                        /\ ma.type = "2a"
                        /\ ma.bal = m.bal
                        /\ ma.val = m.val
                  /\ m.bal =< maxVBal[m.acc])'
         BY <2>1, <4>1a, <4>3, <4>4, <4>6, <4>11, SafeAtStable\* , Zenon
           DEF MsgInv, TypeOK, Messages

       <5>4. QED
         BY <5>1, <5>2, <5>3 
*)
    <3>4. ASSUME NEW a \in Acceptors, Phase2b(a)
          PROVE  MsgInv'
      <4>. PICK m \in msgs : Phase2b(a)!(m)
        BY <3>4 DEF Phase2b
      <4>1. \A aa, vv, bb : VotedForIn(aa,vv,bb) => VotedForIn(aa,vv,bb)'
        BY DEF VotedForIn, Send
      <4>2. \A mm \in msgs : mm.type = "1b"
               => \A v \in Values, c \in (mm.maxVBal+1) .. (mm.bal-1) :
                     ~ VotedForIn(mm.acc, v, c) => ~ VotedForIn(mm.acc, v, c)'
        BY DEF Send, VotedForIn, MsgInv, TypeOK, Messages
      <4>. QED
        BY <4>1, <4>2, SafeAtStable, <2>1 DEF MsgInv, Send, TypeOK, Messages
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Next
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Inv

<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

    
THEOREM Consistent == Spec => []Consistency
<1> USE DEF Ballots
  
<1>1. Inv => Consistency
  <2> SUFFICES ASSUME Inv,  
                      NEW v1 \in Values,  NEW v2 \in Values, 
                      NEW b1 \in Ballots, NEW b2 \in Ballots,
                      ChosenIn(v1, b1), ChosenIn(v2, b2),
                      b1 =< b2
               PROVE  v1 = v2
    BY DEF Consistency, Chosen
  <2>1. CASE b1 = b2
    BY <2>1, VotedOnce, QuorumAssumption, SMTT(100) DEF ChosenIn, Inv
(*
    <3>1. PICK a1 \in Acceptors : VotedForIn(a1, v1, b1)
      BY QuorumAssumption DEF ChosenIn
    <3>2. PICK a2 \in Acceptors : VotedForIn(a2, v2, b2)
      BY QuorumAssumption DEF ChosenIn
    <3>. QED
      BY <3>1, <3>2, <2>1, VotedOnce DEF Inv
*)
  <2>2. CASE b1 < b2
    <3>1. SafeAt(v2, b2)
      BY VotedInv, QuorumNonEmpty, QuorumAssumption DEF ChosenIn, Inv
    <3>2. PICK Q2 \in Quorums : 
                  \A a \in Q2 : VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
      BY <3>1, <2>2 DEF SafeAt
    <3>3. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
      BY DEF ChosenIn
    <3>4. QED
      BY <3>2, <3>3, QuorumAssumption, VotedOnce, Z3 DEF WontVoteIn, Inv
  <2>3. QED
    BY <2>1, <2>2

<1>2. QED
  BY Invariant, <1>1, PTL

-----------------------------------------------------------------------------
chosenBar == {v \in Values : Chosen(v)}

C == INSTANCE Consensus WITH chosen <- chosenBar

(***************************************************************************)
(* The following theorem asserts that this specification of Paxos refines  *)
(* the trivial specification of consensus in module Consensus.             *)
(***************************************************************************)
THEOREM Refinement == Spec => C!Spec
<1>1. Init => C!Init
  BY QuorumNonEmpty DEF Init, C!Init, chosenBar, Chosen, ChosenIn, VotedForIn

<1>2. TypeOK' /\ Consistency' /\ [Next]_vars => [C!Next]_chosenBar
  <2> SUFFICES ASSUME TypeOK', Consistency', Next, chosenBar' # chosenBar
               PROVE  C!Next
    BY DEF vars, chosenBar, Chosen, ChosenIn, VotedForIn
  <2>1. chosenBar \subseteq chosenBar'
    BY DEF Send, chosenBar, Chosen, ChosenIn, VotedForIn, Next, Phase1a, Phase1b, Phase2a, Phase2b
  <2>2. \A v, w \in chosenBar': v = w
    BY DEF Consistency, chosenBar, ChosenIn, TypeOK
  <2>3. chosenBar = {}
    BY <2>1, <2>2, SetExtensionality
  <2>. QED
    BY <2>1, <2>2, <2>3 DEF C!Next, chosenBar

<1>3. QED
  BY <1>1, <1>2, Invariant, Consistent, PTL DEF Spec, C!Spec, Inv

=============================================================================
\* Modification History
\* Last modified Fri Nov 28 10:39:17 PST 2014 by lamport
\* Last modified Sun Nov 23 14:45:09 PST 2014 by lamport
\* Last modified Mon Nov 24 02:03:02 CET 2014 by merz
\* Last modified Sat Nov 22 12:04:19 CET 2014 by merz
\* Last modified Fri Nov 21 17:40:41 PST 2014 by lamport
\* Last modified Tue Mar 18 11:37:57 CET 2014 by doligez
\* Last modified Sat Nov 24 18:53:09 GMT-03:00 2012 by merz
\* Created Sat Nov 17 16:02:06 PST 2012 by lamport
