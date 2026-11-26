# The wild number of the complete graphs on 13 and 14 vertices

Prepared by **JanWoldstad** with **OpenAI Codex**.

**Result.** In every proper 13-edge-coloring of the complete graph on 13 vertices, one can choose nine edges so that adding those same edges to each individual color class connects all 13 vertices. Eight never suffice. The wild number is therefore exactly **9**. The same value follows for every minimum proper edge-coloring of the complete graph on 14 vertices.

Dawkins, Nappo, Tong and Zimbizi state the general claim in Conjecture 6.1. The catalogue contributor @aadrianvv reduced the 13-vertex case to two questions about partitions of nine points, called A13(0) and A13(1). Below we derive that reduction for every proper 13-edge-coloring and settle the two questions by exhaustive enumeration. One proof fixes a point of maximum degree. A second proof fixes a point of minimum degree and classifies the possible obstructions. [Original paper](https://arxiv.org/abs/2610.22142) · [Original reduction, §4](https://github.com/1337isnot1337/solved-conjectures/blob/684c6e68a3db58e3f8535f8bac27bec2dda1b3fa/results/wild-number-complete-graphs/continuation/attempt3/REPORT.md) · [Contributor credit](https://github.com/1337isnot1337/solved-conjectures/blob/684c6e68a3db58e3f8535f8bac27bec2dda1b3fa/results/wild-number-complete-graphs/README.md)

## Why every coloring reaches one of the two cases

Each color class is a matching with at most six edges. The 13 classes cover 78 edges, so each contains exactly six and misses one vertex. Each vertex meets twelve different colors, so the missed vertices give the colors distinct names. For a four-set $D$, let $k$ count its internal edges whose color is named for a vertex in $D$. Of the 715 possible four-sets, at most 195 repeat a color, since the two disjoint edges of a repeated color determine their four vertices. At most 390 have $k\ge2$, since each of the 78 edges contributes to $k$ on exactly ten four-sets. Thus **at least 130** four-sets have six different colors and $k\in\{0,1\}$.

Choose any such $D$. We want to split the remaining nine vertices into three triples. A triple is *bad* if some color has no matching edge crossing the cut formed by the triple, or the cut formed by the triple together with $D$. The cut around $D$ itself cannot close because its six edge colors are distinct. These are all cuts of the four blocks up to complement. With three good triples, a tree inside each block gives $3+2+2+2=9$ wild edges and connects every color. The matching counts below show that every coloring restricted to the nine vertices satisfies the conditions of one of the two abstract cases. [Full reduction and matching counts](reduction.md)

## What a counterexample would require

Write $B$ for the **set** of bad triples. A counterexample to either abstract case would require $B$ to meet all 280 partitions of nine points into three triples. Call such a family a *blocker*. Each triple occurs in ten partitions, so a blocker has at least 28 triples.

The following description counts occurrences before discarding duplicate triples. A full group centered at $x$ consists of four triples made by adjoining $x$ to the four pairs of a perfect matching of the other eight points. A partial group consists of two triples made from two disjoint pairs and their common center.

| Source of bad triples | Case $k=0$ | Case $k=1$ |
| --- | --- | --- |
| Named colors occurring on an edge inside $D$ and named for a vertex outside $D$ | 6 full groups | 5 full groups |
| Other colors named for vertices outside $D$ | 3 partial groups | 4 partial groups |
| Colors named for a vertex of $D$ | 4 individual triples | 3 individual triples and 1 full group |
| Maximum number of distinct bad triples | **34** | **35** |

For example, a full group of the first kind comes from the three matching edges of a named color $x$ on the nine-set. These give three bad triples through $x$. The pair of other vertices left uncovered supplies the fourth bad triple through $x$. In case 1 the special color named in $D$ has four matching edges on the nine-set. The vertex they miss is the center of its full group. The entries follow from checking the two possible cuts of a triple. [Four cut cases](reduction.md)

Let $d$ be the largest number of *distinct* bad triples containing one point. Each full group contributes four occurrences at its center and one elsewhere. Each partial group contributes two at its center and at most one elsewhere. Thus at a vertex $x$ the total number of occurrences is at most $13+3m_x+\ell_x$, where $m_x$ counts full groups centered at $x$ and $\ell_x$ is one if $x$ centers a partial group. In case 0 this gives $d\le16$. In case 1, $d\le17$ unless the special center is also a center of one of the five named full groups. At that double center, $d\le19$. Every point centers at least two distinct bad triples from its own named color. [Independent degree calculation](sat/terminal-links.md)

## Exhausting the possibilities

Fix a point $x$ of largest bad degree. Its *link* is the graph on the other eight points whose edges $ab$ represent bad triples $xab$. Since $|B|\ge28$, averaging the nine degrees gives $d\ge10$. Only links with 10 through 19 edges need examination.

For a fixed link, form a graph whose 56 vertices are the triples avoiding $x$. Join two disjoint triples if the pair of points they leave over is absent from the link. Along any such edge the third triple in the nine-point partition is good. Hence at least one endpoint must belong to $B$. The triples of $B$ avoiding $x$ must therefore be a vertex cover of this graph, with at most $35-d$ members. Any full family also has bad degree between two and $d$ at every vertex.

The first checker generates every link up to relabeling by adding one vertex with every possible neighborhood to every smaller graph. It branches on including a vertex in the cover or including all its neighbors. A matching of size larger than the remaining budget rules out a branch. A branch survives the leaf checks when each point's current degree is at most $d$ and could reach two within the remaining budget. These conditions can retain extra links, all of which the matching argument below considers. Of **11,072** link types in the degree range, just two survive. [Exhaustive C++ checker](blockers/link_search.cpp) · [Run output](blockers/max_link.log)

| Largest bad degree | Surviving link | Why the coloring excludes it |
| --- | --- | --- |
| 10–17 | None | This already proves **A13(0)**. |
| 18 | An eight-vertex complete graph with every edge inside a five-set removed | The five vertices would need five distinct partners among the other three. The double center requires a perfect matching. |
| 19 | The same graph with one edge restored inside the five-set | Every perfect matching must use that one edge. The double center supplies two perfect matchings. With 19 distinct triples and at most 19 occurrences they must be edge-disjoint. |

The last two contradictions prove **A13(1)**. The decision depends only on the bad triples and applies even to abstract nine-vertex colorings that need not extend to the original graph. A separate Python search using Brendan McKay's published census of eight-vertex graphs reproduced the same two link shapes and counts at every degree. [Terminal matching check](sat/check_terminal_links.py) · [McKay catalogue cross-check and provenance](blockers/graph6-crosscheck.md)

An independent Python checker instead fixes a point of *smallest* degree. It finds that every blocker with at most 35 triples and largest degree at most 19 either contains all 35 triples on seven points, or contains all 34 triples meeting some four-set in at least two points. The first family has no possible full-group center. The second has none before its one possible extra triple is added. That addition can enable at most three centers, while the reduction supplies at least five distinct centers. This proves both cases again. [Independent proof and verifier](combin/README.md)

## Optimality and the 14-vertex consequence

On $K_{13}$, a singleton component of the wild edges stays isolated in the color missing that vertex. A two-vertex component stays isolated from the rest in the color of its internal edge. Thus every component has at least three vertices, and there are at most four components. Connecting 13 vertices into at most four components requires at least nine edges.

On $K_{14}$ every color in a minimum proper coloring is a perfect matching. Delete a vertex, apply the 13-vertex result, then restore the vertex. Each color attaches the restored vertex by its own matching edge. For the lower bound, a two-vertex wild component again fails, and two singletons would form an isolated pair in the color of the edge joining them. Hence there is at most one singleton and every other component has at least three vertices. There are at most five components, giving at least $14-5=9$ wild edges. These bounds also agree with the paper's formula. [Original lower bound](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS1)

## Reproducing the computations

Follow the [fresh-clone instructions](README.md) to rerun the exhaustive checks. The [witness script](witness.py) also constructs nine wild edges for a supplied 13-vertex coloring and checks connectivity separately for each of its 13 colors.
