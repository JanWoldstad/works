# Independent graph6 cross-check

The input file [graph8.g6](graph8.g6) is an unmodified copy of Brendan McKay's catalogue of all 12,346 simple graphs on eight vertices up to isomorphism. Its SHA-256 digest is 546a249902101c97d3aa590f93e53366854bd0a6f405aa59bdb32d25c57f845a. The data are distributed under the Creative Commons Attribution 4.0 International license. [Source file](https://users.cecs.anu.edu.au/~bdm/data/graph8.g6) · [Catalogue](https://users.cecs.anu.edu.au/~bdm/data/graphs.html) · [Author's license statement](https://users.cecs.anu.edu.au/~bdm/data/) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

The pure-Python [cross-check](check_graph6.py) reads this external census. For each possible maximum-degree link, every absent pair leaves six vertices whose ten splits into two triples must each contain a bad triple. Treating those requirements as edges of a graph on the 56 triples, the program branches on the two possible endpoints of one uncovered edge. A greedy matching gives a lower bound on the remaining cover size. A vertex of this graph with more neighbors than the remaining budget must be selected, since omitting it forces all its neighbors. A true blocker also respects the maximum degree and the lower bound two at each point. The search uses those bounds only to discard impossible branches.

The check examined all 11,072 links having 10 through 19 edges in the 12,346 graph records. Two survived. In record 909 the absent pairs are all ten edges on vertices 0 through 4. In record 3378 the absent pairs are the same edges except for the pair joining 0 to 4. Their link degrees are 18 and 19, respectively. Each of the remaining degrees had zero survivors.

Run the independent script from the `wild-number-13-14` directory using Python 3.10 or newer.

    python -I -B blockers/check_graph6.py
