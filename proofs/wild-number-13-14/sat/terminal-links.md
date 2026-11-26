# Excluding the two surviving links

Let `Bad` be the family of forbidden triples in the nine-vertex reduction.
The link at a vertex $x$ has edge $uv$ precisely when $\{x,u,v\}$ is
bad. Its edge count is the degree of $x$ in `Bad`.

## Upper bounds on bad degree

Call a color in the nine-set heavy if its matching there has three edges
and light if it has two. Write $s$ for the size of color $x$'s matching.
Write $H,L,D$ for the numbers of edges incident to $x$ in heavy, light
and ordinary outside colors. In case 1 the special outside color is counted
separately. Count occurrences of triples through $x$ in the defining
list for `Bad`, keeping duplicates for this calculation.

* An invalid triple is formed by adding the name of a nine-set color to an
  edge of that color. There are $s+H+L$ occurrences through $x$.
* Each ordinary outside color contributes its unique uncovered triple. It
  contains $x$ precisely when $x$ has no incident edge of that color.
* Each heavy color contributes the triple consisting of its name and its
  two other uncovered vertices. It contains $x$ precisely when $x$ has
  no incident edge of that color, including the case when $x$ is its name.
* In case 1 the special outside color is a matching of four edges and misses
  a unique vertex $w$. The four bad triples formed by adjoining $w$ to
  these edges give four occurrences at $w$ and one at every other vertex.

| Case | Occurrences through $x$ | Upper bound at heavy / light $x$ |
| --- | --- | --- |
| 0 | $s+H+L+(4-D)+(6-H)=s+10+L-D$ | 16 / 14 |
| 1, $x\ne w$ | $s+H+L+(3-D)+(5-H)+1=s+9+L-D$ | 16 / 14 |
| 1, $x=w$ | $s+H+L+(3-D)+(5-H)+4=s+12+L-D$ | 19 / 17 |

There are three light colors in case 0 and four in case 1. A light
vertex has no incident edge of its own color, giving the smaller bound
in its column. Distinct bad triples never exceed the occurrence count.
Consequently any link of size 18 or 19 is centered at the special
uncovered vertex $w$ in case 1, and $w$ is heavy.

## Matching obstruction

At $w$ the four special-color edges yield a perfect matching in the link.
The three edges colored $w$, together
with the edge between the two remaining vertices, yield another matching covering all eight vertices. These four link edges
arise from the three invalid triples centered at $w$ and the
uncovered-vertices triple of heavy color $w$, respectively. If the link
has 19 edges, all 19 counted occurrences are distinct, so the two perfect
matchings are edge-disjoint.

The surviving 18-edge link has an independent set of five vertices.
Each one needs a different partner among the other three to participate
in a perfect matching, which is impossible. In the 19-edge link that
five-set contains exactly one edge. Every perfect matching must use that
edge, ruling out two edge-disjoint perfect matchings.

The following independent check decodes the actual two canonical masks
and enumerates the 105 perfect matchings of the complete graph on eight
vertices. Run from the `wild-number-13-14` directory.

```shell
python -I -B sat/check_terminal_links.py
```

```text
degree=18 mask=268434432 perfect_matchings=0 edge_disjoint_pairs=0
degree=19 mask=268434944 perfect_matchings=6 edge_disjoint_pairs=0
```
