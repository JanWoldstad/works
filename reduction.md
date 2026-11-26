# Reduction of the 13-vertex wild-number problem

The catalogue contributor @aadrianvv reduced the 13-vertex case of Conjecture 6.1 to two finite assertions, A13(0) and A13(1). We give the details because the theorem quantifies over **every** minimum proper edge coloring. The two abstract assertions also quantify over colorings on nine vertices that might have no extension to the original graph. [Original paper by Dawkins, Nappo, Tong and Zimbizi, §3.3](https://arxiv.org/html/2610.22142v1#S3.SS3) · [Original reduction by @aadrianvv, §4](https://github.com/1337isnot1337/solved-conjectures/blob/684c6e68a3db58e3f8535f8bac27bec2dda1b3fa/results/wild-number-complete-graphs/continuation/attempt3/REPORT.md)

## Choosing the four-vertex block

Thirteen colors are necessary because each matching on 13 vertices covers at most six of the 78 edges. Thirteen also suffice. Label the vertices modulo 13 and give edge $xy$ color $(x+y)/2$ modulo 13. At each vertex these colors are distinct and only its own label is missing. For 14 vertices, add a vertex and give the edge joining it to $x$ color $x$. This gives the minimum of 13 there as well, since each vertex has degree 13.

Now fix an arbitrary proper 13-coloring on 13 vertices. Each color class is a matching with at most six edges. There are 78 edges and 13 colors, so each class has six edges and misses exactly one vertex. Conversely, each vertex has twelve incident edges of distinct colors and misses exactly one color. Label color classes by their missing vertices. Write $M_c$ for the matching missing $c$.

For a four-element set $D$, let $k(D)$ count its edges whose color label lies in $D$. A non-rainbow $D$ contains two disjoint edges of one color. Consequently at most $13\binom{6}{2}=195$ four-sets are non-rainbow. For any edge $xy$ of color $c$, the three vertices $x,y,c$ are distinct. Exactly ten four-sets contain them. Summing over edges gives $\sum_D k(D)=780$, so at most 390 four-sets have $k(D)\ge2$. Among the $\binom{13}{4}=715$ four-sets, at least 130 are rainbow and have $k(D)\le1$.

Fix one such $D$, write $W=V\setminus D$ and put $k=k(D)$. The six edges on $D$ have six distinct colors. Exactly $6-k$ of those colors have labels in $W$. Relabel these vertices first, and relabel the others in $W$ afterward. When $k=1$, we may also name the one internal $D$-color $d_0$. All relabelings act simultaneously on a vertex and its color.

## What a split must accomplish

Split $W$ into triples $A,B,C$. Pick a spanning tree inside each of $D,A,B,C$. This uses $3+2+2+2=9$ edges. The graph consisting of these edges and $M_c$ is disconnected exactly when some nonempty proper union of the four blocks has no $M_c$-edge to its complement. Call that cut *closed* for color $c$. This definition treats the two sides symmetrically. For a closed cut, the side that excludes $c$ is perfectly matched internally. This is the seal used in the paper. [Original connectivity criterion, §3.3.2](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS2)

Up to complements, the seven cuts have representatives $D,A,B,C,D\cup A,D\cup B,D\cup C$. The cut $D$ cannot close. A closed side of even size excludes $c$ because the matching pairs its other vertices. A closed four-set would therefore contain two edges of the same color, contrary to the choice of $D$. A triple $X\subset W$ closes precisely when $c\in X$ and the other two vertices are paired by $M_c$.

It remains to test $D\cup X$. For each $c$, let $h=1$ if $c\in D$, otherwise $h=0$. Let $a=1$ if an edge inside $D$ has color $c$, otherwise $a=0$. Define $U_c$ as the vertices in $W\setminus\{c\}$ having no partner inside $W$ under $M_c$. They are exactly the $W$-endpoints of the matching edges crossing from $D$. Counting matched vertices in $D$ gives

$$
|U_c|=4-h-2a,\qquad |M_c\cap E(W)|=6-a-|U_c|=2+h+a.
$$

Since $D\cup X$ has seven vertices, closure requires it to contain the unmatched vertex $c$. To close, $X$ must contain every crossing endpoint in $U_c$. After accounting for those endpoints and for $c$ when $c\in W$, the unused positions in $X$ must be filled by whole $M_c$-pairs inside $W$. These conditions are sufficient as well, and give the full list.

| Location of $c$ | $a$ | $c$-edges in $W$ | $X$ that close $D\cup X$ |
| --- | --- | --- | --- |
| $D$ | 0 | 3 | $X=U_c$, a triple. |
| $D$ | 1 | 4 | $X=U_c\cup e$, with $e$ any $c$-edge in $W$. Here $U_c$ is a singleton. |
| $W$ | 0 | 2 | Impossible because its four crossing endpoints cannot fit in a triple. |
| $W$ | 1 | 3 | $X=U_c\cup\{c\}$, with two crossing endpoints. |

## The two finite statements

In case $k$, color the 36 edges of the complete graph on $W$ with the 13 inherited labels. Each color class must be a matching with the size in the table, and neither endpoint of an edge may be its color. These conditions hold for the restriction of every original coloring with the selected $D$. Mark as bad the triples that close their own cut or close their union with $D$, using the preceding criteria. There are $9!/(3!^3 3!)=280$ unordered splits of $W$ into triples.

The abstract assertion A13(k) is that **every** such coloring of $W$ admits a split with three good triples. Each satisfying split makes every color connected using the same nine tree edges. For checking computations, the count of potential bad triples from a closed triple alone is at most $3(6-k)+2(3+k)=24-k$. The $D\cup X$ rows contribute at most $4-k+4k+(6-k)=10+2k$ additional triples. Thus the upper bounds on the union are 34 and 35. Repeated triples across witnesses may be discarded. [Original abstract encoding](https://github.com/1337isnot1337/solved-conjectures/blob/684c6e68a3db58e3f8535f8bac27bec2dda1b3fa/results/wild-number-complete-graphs/continuation/attempt3/abs13.py)

If both cases hold, the same value follows for every minimum proper coloring of $K_{14}$. Each color class there is a perfect matching. Delete one vertex, obtain a minimum 13-coloring of $K_{13}$, and choose its nine connecting edges. Restoring the deleted vertex attaches it to the connected graph of each color through its matching edge. The paper's lower bound is again nine. Both abstract cases are proved in the [blocker argument](PROOF.md#exhausting-the-possibilities).
