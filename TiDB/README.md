## Dr. TLA+ Series - Verifying Distributed Transaction with TLA+ in TiDB (Ed Huang)

### Time
Feburary, 2018

### Abstract
TiDB is an open source distributed Hybrid Transactional/Analytical Processing (HTAP) database that empowers users to meet both online transactional and real-time analytical workloads with a single database. The design is inspired by Google Spanner/F1, and highly compatible with MySQL, for more information, please check out: [http://github.com/pingcap/tidb](http://github.com/pingcap/tidb).

Under the hood, TiDB is a complex distributed system, including storage engine, SQL parser, query optimizer, transaction layer, replication, etc. TiDB uses a highly optimized 2PC (2-phase commit) algorithm to support ACID semantic. The correctness of the algorithm is very important to us.

TLA+ is formal specification language which can help us to find the design problem in critical systems. It is widely used to verify the algorithm, like the distributed consensus algorithm - Raft. In TiDB, we also use TLA+ to verify our distributed transaction implementation, it gives us more confident that we are on the right way when we pass the verification.

In this talk, I will first show what is TiDB, the design and key components, then I will show you some our works with TLA+ ( spec: [https://github.com/pingcap/tla-plus](https://github.com/pingcap/tla-plus) ).

### Bio
Ed Huang worked for MSRA, NetEase and WandouLabs before co-founding PingCAP. He is a senior infrastructure software engineer, architect and the CTO of PingCAP. Ed is an expert in distributed system and database development with rich experience and unique understanding in distributed storage. As an open-source fanatic and developer, he has developed Codis, a distributed Redis cache solution, and TiDB, an open source distributed HTAP database.

[back to schedule](https://github.com/tlaplus/DrTLAPlus)
