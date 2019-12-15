## Dr. TLA+ Series - Specification and Verification of Multi-Paxos (Saksham Chand)

### Time
November 15, 2019

### Location
Microsoft Building 99, Research Lecture Room A 1915 Hopper
+ 14820 NE 36th St, Redmond, WA 98052

### Abstract
A critical problem in distributed systems is distributed consensus---a set of servers aiming to agree on a single value or a continuing sequence of values, called single-value consensus or multi-value consensus, respectively. It is essential in any distributed service that must maintain and replicate a state to tolerate failures caused by machine crashes, network outages, etc. To this end, we study Paxos---a well-known algorithm for solving distributed consensus used in many distributed services, including Microsoft's Autopilot and IronRSL. 

In this talk, we detail formal specifications of the exact phases of multi-value Paxos in TLA+, Lamport's Temporal Logic of Actions, and complete proofs of its safety that are mechanically checked in TLAPS, the TLA Proof System. We also discuss general strategies for proving properties involving sets and tuples that helped the proof check succeed insignificantly reduced time. The specification and proof are small (55 lines and 787 lines, respectively) and took about 100 seconds to check, contrasting others that are an order of magnitude larger, more time-consuming, or worse.

Next, we discuss using message history variables, that is, variables holding all sent messages and all received messages, for verification of distributed algorithms, with variants of Paxos as precise case studies. We show that using history variables, instead of using and maintaining other state variables, yields specifications that are more declarative and easier to understand. It also allows easier proofs to be developed by needing fewer invariants and facilitating proof derivations. Furthermore, the proofs are mechanically checked more efficiently. Our specifications, proofs, and proof checking times were reduced by a quarter or more for single-value Paxos and by about half or more for multi-value Paxos.

### Bio
Saksham Chand is a PhD student at the Computer Science Department of Stony Brook University, New York, where he conducts research in specification and verification of distributed algorithms. He supervises graduate students working on byzantine fault tolerance, fast state machine replication, and blockchain systems. In his free time, he enjoys beaches, snowboarding and singing. He received an M.Sc. degree from the Computer Science Department of Stony Brook University (F &#39;15) and a B.Sc. degree in Computer Science from National Institute of Technology, Nagpur, India in (S &#39;12). Prior to joining Stony Brook University, he worked as a System Software Developer at Nvidia where he worked on the products Shield and GRID.

### Media
+ [video](https://youtu.be/uBQSE4MMWhY)
+ [slides](./SakshamChand_MultiPaxos.pdf)

[back to the complete schedule of Dr. TLA+ Series](https://github.com/tlaplus/DrTLAPlus)
