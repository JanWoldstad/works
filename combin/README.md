# The nine-point blocker classification

A family of triples on nine points is a **blocker** if every partition of the points into three triples contains a member. A point's degree is the number of members containing it. The following finite classification rules out a blocker in **both** abstract endgames of the $K_{13}$ reduction.

**Classification.** A blocker of at most 35 triples and maximum degree at most 19 has one of two forms.

1. It consists of all 35 triples on a fixed seven-point subset.
2. It contains all 34 triples meeting a fixed four-point subset in at least two points, with at most one further triple. There are 30 such triples with exactly two points in the subset and four contained in it.

## Why this solves the two endgames

Write $W$ for the nine points and $k=0,1$ for the two cases. The reduction identifies a family $B$ of triples that are forbidden as blocks. A split avoiding $B$ exists exactly when $B$ fails to be a blocker. The following description follows from the color matchings. [Reduction and matching counts](../reduction.md) · [Original reduction by @aadrianvv, §4](https://github.com/1337isnot1337/solved-conjectures/blob/684c6e68a3db58e3f8535f8bac27bec2dda1b3fa/results/wild-number-complete-graphs/continuation/attempt3/REPORT.md)

- Each of the $6-k$ heavy colors $u$ in $W$ has three edges on the other eight points. Those three edges and the pair of remaining points form a perfect matching. Adjoining $u$ to each pair gives four forbidden triples.
- Each of the $3+k$ light colors $u$ in $W$ contributes two forbidden triples by adjoining $u$ to two disjoint edges.
- Each of the $4-k$ ordinary outside colors contributes one triple, the three points missed by its matching. When $k=1$, the exceptional outside color has four edges on $W$, missing a single point $w_*$. Adjoining $w_*$ to each edge gives another family of four forbidden triples.

Thus in either case there are six families each formed by adjoining a center to a perfect matching of the other eight points. At least five **distinct** points are centers, since the heavy centers have different names. The total number of triple occurrences is $6(4)+2(3+k)+(4-k)=34+k$. Coinciding triples count only once in $B$.

Fix a vertex $v$. Write $c$ for the number of the six families centered there and $l=1$ if $v$ is light, zero otherwise. The six families contribute $6+3c$ occurrences through $v$. The light families centered elsewhere contribute at most $3+k-l$, the light family at $v$ contributes $2l$, and the ordinary outside colors contribute at most $4-k$. Hence the degree is at most $13+3c+l$. If $c=2$, then $v$ is a heavy center also equal to $w_*$, so $l=0$. In all cases the degree is at most 19.

For a center $v$, the link of $B$ at $v$ consists of the pairs $xy$ such that $vxy$ belongs to $B$. Each of the at least five distinct centers just identified has a perfect matching in its link. In the seven-point blocker no link has a perfect matching because the triples all omit two points. In the 34-triple family from the four-point subset $S$, a link at a point of $S$ has all its edges meeting the other three points of $S$, which rules out four disjoint edges. At any point outside $S$ its link has edges only within $S$. Adding one triple can change links at only its three points, so at most three links can acquire perfect matchings. Both possibilities from the classification contradict the five required centers. This establishes A13(0) and A13(1).

## Exhaustive proof of the classification

Choose a point of minimum degree $d$ as root. The sum of degrees is at most $3(35)=105$, so $d\le 11$. Its link $L$ is an ordinary graph with $d$ edges on the other eight points. Fix $L$. Every partition of the nine points has exactly one block containing the root. If this block is forbidden, the partition is already blocked. Otherwise the other two triples $T,U$ must include a forbidden one. The possible forbidden families extending $L$ thus correspond exactly to vertex covers of the following graph with size and degree constraints.

- The 56 vertices are triples of the eight nonroot points.
- Join disjoint $T,U$ when the two points left over form a pair outside $L$.
- Select at most $35-d$ of the 56 vertices. After the root triples are included, every point must have degree between $d$ and 19.

The checker generates root graphs by adding one vertex at a time with every possible neighborhood. Each newly formed graph is replaced by a relabeling and duplicates are dropped. Removing one vertex of an arbitrarily labeled graph gives the induction proving coverage. The checker also computes the number of eight-vertex graph types at each edge count independently by Burnside's lemma. For a permutation of the points, the fixed graphs are unions of cycles of its action on pairs. The resulting counts agree at every degree.

At each vertex-cover branch the checker either selects a vertex of this graph or omits it and selects all its neighbors. Isolated vertices are kept for a final enumeration of all subsets within budget. A packing of pairwise disjoint edges gives a lower bound on the remaining cover size. Additional pruning uses the point-degree bounds and the fact that each selected triple adds three incidences. Each surviving leaf is verified against all 280 partitions directly, then tested for the seven-set and four-set patterns by enumerating the candidate point subsets.

The run covered 2,481 root graphs and 23,629 vertex-cover search nodes. The eight surviving leaves at root degree zero were seven-set families. The 29 at root degree six all contained the four-set family. No other leaves survived. These are leaf counts after fixing labeled representatives for the root links. Several leaves can represent isomorphic blockers.

Run from the repository root with Python 3.10 or newer. The script uses only the standard library and exits with an error if it finds an unclassified blocker or disagrees with the orbit counts. [Checker](minimum_link.py) · [Recorded output](minimum_link.log)

```shell
python -I -B combin/minimum_link.py
```
