# Nine wild edges suffice on 13 and 14 vertices

By **Astra (OpenAI Codex)** and **JanWoldstad**.

Draw 13 or 14 dots and join every pair. Color the lines with 13 colors so that lines meeting at a dot have different colors. You can always choose **nine** lines to serve as wild cards. Pick any color and you can travel between any two dots using that color and the nine wild lines. The same nine work for all 13 colors, and eight never suffice.

In graph-theoretic terms, the wild number of every minimum proper edge coloring of the complete graph on 13 or 14 vertices is exactly nine. This settles these two orders of Conjecture 6.1 of Dawkins, Nappo, Tong and Zimbizi. The paper gives the lower bound and proves equality through 12 vertices. [Original paper](https://arxiv.org/abs/2610.22142)

## Proof and credit

**@aadrianvv** reduced the 13-vertex problem to two cases on nine points. Their reduction is the starting point for this proof. The 14-vertex conclusion uses the vertex-deletion argument of Dawkins, Nappo, Tong and Zimbizi. [Original reduction, §4](https://github.com/1337isnot1337/solved-conjectures/blob/684c6e68a3db58e3f8535f8bac27bec2dda1b3fa/results/wild-number-complete-graphs/continuation/attempt3/REPORT.md) · [Original paper, §3.3.3](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) · [Catalogue discussion](https://github.com/1337isnot1337/solved-conjectures/issues/155)

The new step rules out an obstruction in both nine-point cases. One computation examines 11,072 graphs and leaves just two possibilities, each excluded by a matching argument. A second computation chooses a point of smallest degree and classifies the obstructions independently. The written proof explains why these finite searches cover every coloring. [Proof](PROOF.md) · [Coverage of the reduction](reduction.md) · [Independent classification](combin/README.md)

Astra, the AI assistant on this project, helped develop the argument, implement the checkers, and formalize the result in Lean. Independent mathematical review is welcome.

## Check the Lean proof

The two main theorems are `WildNumber.wildNumber_K13` and `WildNumber.wildNumber_K14`. Both quantify over an arbitrary proper edge coloring with 13 colors. Lean proves that 13 is the minimum palette size for each graph, and that the connectivity condition is equivalent to a spanning tree for every color after adding the same wild edges. [Theorem statements](WildNumber/Main.lean) · [Wild number and spanning trees](WildNumber/Value.lean) · [Minimum palette](WildNumber/Palette.lean)

With Elan installed, run the following commands to check a fresh clone. The toolchain and mathlib revisions are pinned. The certificates are included in this folder.

```sh
git clone https://github.com/JanWoldstad/works.git
cd works/proofs/wild-number-13-14
lake exe cache get
lake build
```

| Part of the proof | What Lean checks |
| --- | --- |
| [Reduction coverage theorem](WildNumber/Coverage.lean) | Every 13-coloring has at least 130 eligible four-sets. For any one of them, the count of internal named edges is zero or one. |
| [Local cut rules](WildNumber/LocalMatching.lean) and [the full reduction](WildNumber/ReductionAssembly.lean) | A failed split would produce a family of forbidden triples satisfying the exact conditions of the finite theorem. |
| [Nine-point theorem](WildNumber/Main.lean) | The minimum-degree vertex has one of 2,481 possible links up to relabeling. Lean checks that inserting each possible edge preserves coverage of the list, then checks a finite refutation for each representative. Both abstract cases allow matchings that need not extend to a coloring on 13 vertices. |
| [Wild edges](WildNumber/Blocks.lean), [lower bounds](WildNumber/Lower.lean), and [the 14-vertex case](WildNumber/Lift.lean) | The nine chosen edges connect all vertices in each color. Eight cannot suffice. Restoring a deleted vertex preserves connectivity in every color. |

The default build audits the public theorems' dependencies. It permits only `propext`, `Classical.choice`, and `Quot.sound`. The Python generators supply finite certificates, and Lean checks those certificates in its kernel. [Axiom audit](WildNumber.lean) · [Relabeling checker](WildNumber/OrbitCheck.lean) · [Search certificate checker](WildNumber/FiniteReplay.lean)

## Reproduce the checks

Use Python 3.10 or newer. From the root of the clone, enter the proof folder and run the checker. The default run uses only the standard library. All input data are included.

```sh
cd proofs/wild-number-13-14
python verify.py
```

Use `python3` if that is your Python command. The runner checks both Python enumerations, the matching obstruction for the two surviving graphs, and explicit nine-edge witnesses. The graph-atlas check verifies the SHA-256 digest of its input before reading it. The atlas is Brendan McKay's catalogue of eight-vertex graphs, distributed under CC BY 4.0. [Data source, license and checksum](blockers/graph6-crosscheck.md)

To also **generate the graph census from scratch**, run the full suite with a C++17 compiler. On Windows with MSVC, run this in an x64 Developer Command Prompt.

```sh
python verify.py --with-cpp
```

To see the actual nine edges in an example, run `python witness.py`. To check your own 13-vertex coloring, run `python witness.py colors.json` with a JSON array of 78 integer color labels in vertex-pair order `(0,1), (0,2), …, (11,12)`. The script tests connectivity separately for every color. [Witness checker](witness.py)
