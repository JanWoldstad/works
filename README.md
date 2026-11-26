# Nine wild edges suffice on 13 and 14 vertices

Draw 13 or 14 dots and join every pair. Color the lines with 13 colors so that lines meeting at a dot have different colors. You can always choose **nine** lines to serve as wild cards. Pick any color and you can travel between any two dots using that color and the nine wild lines. The same nine work for all 13 colors, and eight never suffice.

In graph-theoretic terms, the wild number of every minimum proper edge coloring of the complete graph on 13 or 14 vertices is exactly nine. This settles these two orders of Conjecture 6.1 of Dawkins, Nappo, Tong and Zimbizi. The paper gives the lower bound and proves equality through 12 vertices. [Original paper](https://arxiv.org/abs/2610.22142)

## Proof and credit

**@aadrianvv** reduced the 13-vertex problem to two cases on nine points and explained how the 14-vertex result follows. Their reduction is the starting point for this proof. [Original reduction, §4](https://github.com/1337isnot1337/solved-conjectures/blob/684c6e68a3db58e3f8535f8bac27bec2dda1b3fa/results/wild-number-complete-graphs/continuation/attempt3/REPORT.md) · [Catalogue discussion](https://github.com/1337isnot1337/solved-conjectures/issues/155)

The new step rules out an obstruction in both nine-point cases. One computation examines 11,072 graphs and leaves just two possibilities, each excluded by a matching argument. A second computation chooses a point of smallest degree and classifies the obstructions independently. The written proof explains why these finite searches cover every coloring. [Proof](PROOF.md) · [Coverage of the reduction](reduction.md) · [Independent classification](combin/README.md)

JanWoldstad worked with **OpenAI Codex**, an AI assistant, on the two remaining cases. Codex helped develop the counting argument and wrote and tested the Python and C++ checkers. Independent mathematical review is welcome. External peer review and an end-to-end Lean formalization remain open.

## Reproduce the checks

Use Python 3.10 or newer. The default run uses only the standard library. All input data are included in the clone.

```sh
git clone https://github.com/JanWoldstad/wild-number-13-14.git
cd wild-number-13-14
python verify.py
```

Use `python3` if that is your Python command. The runner checks both Python enumerations, the matching obstruction for the two surviving graphs, and explicit nine-edge witnesses. The graph-atlas check verifies the SHA-256 digest of its input before reading it. The atlas is Brendan McKay's catalogue of eight-vertex graphs, distributed under CC BY 4.0. [Data source, license and checksum](blockers/graph6-crosscheck.md)

To also **generate the graph census from scratch**, run the full suite with a C++17 compiler. On Windows with MSVC, run this in an x64 Developer Command Prompt.

```sh
python verify.py --with-cpp
```

To see the actual nine edges in an example, run `python witness.py`. To check your own 13-vertex coloring, run `python witness.py colors.json` with a JSON array of 78 integer color labels in vertex-pair order `(0,1), (0,2), …, (11,12)`. The script tests connectivity separately for every color. [Witness checker](witness.py)
