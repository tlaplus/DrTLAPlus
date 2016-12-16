## Dr. TLA+ Series - Byzantine Paxos (Shuai Mu)

### Time
TBD

### Abstract
In this lecture we will discuss how to tolerate Byzantine faults in achieving consensus. In particular, we will do this by refining Paxos step by step. This problem was solved by Castro and Liskov in 1999. The Practical Byzantine Fault Tolerance (PBFT) protocol they proposed can tolerate f byzantine failures with 3f+1 replicas.

From another angle, PBFT is deeply related to Liskov's previous work, Viewstamped Replication (VR). To people who are not familar with VR, understanding PBFT from scratch could be challenging. Therefore, in this discussion we will try to rebase PBFT on Paxos instead of VR. This could be useful and fun to those who have their knowledge of distributed consensus based on Paxos.

### Bio
Shuai Mu is a post-doc in New York University. He recently received his PhD from Tsinghua University. Shuai is studying on how to improve performance, scalability and consistency in distributed systems.

### Paper and Spec
+ [Practical Byzantine Fault Tolerance](http://pmg.csail.mit.edu/papers/osdi99.pdf)
+ [Byzantizing Paxos by Refinement](http://research.microsoft.com/en-us/um/people/lamport/pubs/paxos-simple.pdf)
+ [Byzantine Paxos TLA+ specification](http://research.microsoft.com/en-us/um/people/chengh/private/Paxos.tla)

### Media

[back to schedule](https://github.com/tlaplus/DrTLAPlus)
