## Dr. TLA+ Series - Flexible Paxos (Heidi Howard)

### Time
November 9, 2016 (TBD)

### Abstract
The Paxos algorithm is a widely adopted approach to reaching agreement in unreliable asynchronous distributed systems. Since its development in 1998, Paxos has been extensively researched, taught and built upon by systems such as Chubby, Zookeeper and Raft. At its foundation, Paxos uses two phases, each requiring agreement from a quorum of participants to reliably reach consensus.

This lecture will introduce Flexible Paxos, the simple yet powerful result that each of the phases of Paxos may use non-intersecting quorums. The result means that majorities are no longer the only practical quorum system for Paxos, opening the door to a new breed of performant, scalable and resilient consensus algorithms. This lecture will demonstrate how we are able to test this result with only simple modifications to the existing Paxos TLA+ specification.

### Bio
[Heidi Howard](http://hh360.user.srcf.net/blog/) is a PhD student in the Systems Research Group at the University of Cambridge. Under the supervision of Professor [Jon Crowcroft](https://www.cl.cam.ac.uk/~jac22/), Heidi is studying how to develop distributed systems which are scalable, consistent and resilient in the face of failures. She also recently interned with [Dahlia Malkhi](https://dahliamalkhi.wordpress.com/) at the [VMware Research Group](https://research.vmware.com/) and has previously worked as a research assistant and undergraduate researcher at the University of Cambridge.
 
### Prerequisite
+ none, but may be helpful to review [Andrew Helwer's lecture on Classic Paxos](../Paxos/README.md)

### Paper and Spec
(not required, but helpful to take a quick look)
+ [Flexible Paxos: Quorum Intersection Revisited](https://arxiv.org/abs/1608.06696), Heidi Howard, Dahlia Malkhi, Alexander Spiegelman
+ [TLA+ Spec for Flexible Paxos](https://github.com/fpaxos)

### Media
+ video (to be updated)

[back to schedule](https://github.com/tlaplus/DrTLAPlus)
