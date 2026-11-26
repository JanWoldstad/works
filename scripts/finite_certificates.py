"""Generate proof-search hints for Lean's certified nine-point search."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / "combin"))
from minimum_link import link_types


def positions(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def packed(values, width):
    return sum(x << (width * i) for i, x in enumerate(values))


EDGES = [x for x in range(256) if x.bit_count() == 2]
TRIPLES = [x for x in range(256) if x.bit_count() == 3]
INC = [sum(1 << i for i, t in enumerate(TRIPLES) if t & 1 << v) for v in range(8)]
ROOT_INC = [sum(1 << i for i, t in enumerate(EDGES) if t & 1 << v) for v in range(8)]
PAIRS = [[sum(1 << i for i, t in enumerate(TRIPLES)
              if t & 1 << x and t & 1 << y) for y in range(9)] for x in range(9)]
ROOT_PAIRS = [[sum(1 << i for i, e in enumerate(EDGES) if (e | 256) & 1 << x
                   and (e | 256) & 1 << y) for y in range(9)] for x in range(9)]
EDGE_AT = {(i, j): EDGES.index(255 ^ (t | u))
           for i, t in enumerate(TRIPLES) for j, u in enumerate(TRIPLES) if not t & u}


def search(g):
    d = g.bit_count()
    adj = [sum(1 << j for j in range(56) if (i,j) in EDGE_AT
               and not (g >> EDGE_AT[i,j]) & 1) for i in range(56)]
    root_degrees = [(g & m).bit_count() for m in ROOT_INC]

    def visit(selected, allowed):
        budget = 35 - d - selected.bit_count()
        if budget < 0:
            return ".oversize"
        for x in range(8):
            if root_degrees[x] + (selected & INC[x]).bit_count() > 19:
                return f"(.high {x})"
            if root_degrees[x] + (allowed & INC[x]).bit_count() < d:
                return f"(.low {x})"
        if budget == 0 and allowed != selected:
            return f"(.full {visit(selected,selected)})"
        unknown = allowed ^ selected
        if not unknown:
            # All remaining clauses have either two absent vertices or a chosen endpoint.
            absent = ((1 << 56) - 1) ^ allowed
            for i in positions(absent):
                neighbors = adj[i] & absent
                if neighbors:
                    j = next(positions(neighbors))
                    return f"(.missing {EDGE_AT[i,j]} {i} {j})"
        pivot = None
        neighbors = 0
        available = unknown
        matching = []
        for i in positions(unknown):
            adjacent = adj[i] & unknown
            if adjacent.bit_count() > neighbors.bit_count():
                pivot, neighbors = i, adjacent
            if available & 1 << i and adjacent & available:
                j = next(positions(adjacent & available))
                available ^= 1 << i | 1 << j
                matching.append(EDGE_AT[i,j] + (i << 5) + (j << 11))
                if len(matching) > budget:
                    return f"(.pack (unpackConflicts {len(matching)} {packed(matching,17)}))"
        if pivot is None:
            possible_centers = sum(all(x == y or (allowed & PAIRS[x][y]) or
                                       (g & ROOT_PAIRS[x][y]) for y in range(9)) for x in range(9))
            if possible_centers < 5:
                return ".centers"
            if not unknown:
                raise ValueError(f"unrefuted blocker {g} {selected}")
            # Branch on any remaining optional triple. A sound certificate must
            # account for supersets of a minimum cover as well.
            pivot = next(positions(unknown))
        forced = [EDGE_AT[pivot,j] + (j << 5) for j in positions(neighbors)]
        yes = visit(selected | (1 << pivot), allowed)
        no = visit(selected | neighbors, allowed ^ (1 << pivot))
        fs = f"(unpackForced {len(forced)} {packed(forced,11)})" if forced else "[]"
        return f"(.split {pivot} {fs} {yes} {no})"

    return visit(0, (1 << 56) - 1)


def main():
    reps = sorted(link_types())
    target = ROOT / "WildNumber"
    batches = [reps[i:i+32] for i in range(0,len(reps),32)]
    names = [f"repBatch{i:03d}" for i in range(len(batches))]
    repdefs = [f"def {name} : List Nat := [{', '.join(map(str,batch))}]"
               for name,batch in zip(names,batches)]
    (target / "FiniteReps.lean").write_text(
        "/-! The eight-point link representatives used by the census. -/\n"
        "namespace WildNumber.Nine.Census\n" + "\n".join(repdefs) +
        f"\ndef repBatches : List (List Nat) := [{', '.join(names)}]\n"
        "def repMasks : Array Nat := repBatches.flatten.toArray\n"
        "end WildNumber.Nine.Census\n",encoding="utf8")
    directory = target / "FiniteCertificates"
    directory.mkdir(exist_ok=True)
    for start in range(0,len(reps),32):
        idx = start // 32
        # Three dependency lanes bound peak memory for a fresh Lake build.
        imports = (["import WildNumber.FiniteFast", "import WildNumber.FiniteReps"]
                   if idx < 3 else [f"import WildNumber.FiniteCertificates.Batch{idx-3:03d}"])
        lines = [*imports, "",
                 "namespace WildNumber.Nine.Census", "",
                 "set_option Elab.async false", "set_option maxRecDepth 200000", "set_option maxHeartbeats 0", ""]
        for g in reps[start:start+32]:
            term = search(g)
            lines.extend([f"private def w{g} : Refutation := {term}",
                f"private theorem exclude{g} (B : Finset ℕ) : ¬ NumericModel {g} B :=",
                f"  using_hint w{g} (by decide +kernel) B",""])
        lines.extend([f"theorem checked{idx:03d} : ∀ g ∈ repBatch{idx:03d}, ∀ B, ¬ NumericModel g B :=",
                      "  " + "".join(f"checkedCons exclude{g} (" for g in batches[idx]) +
                      "by simp" + ")" * len(batches[idx]), ""])
        lines.extend(["end WildNumber.Nine.Census",""])
        (directory / f"Batch{start//32:03d}.lean").write_text("\n".join(lines),encoding="utf8")
        print(start, flush=True)
    (target/"FiniteTheorem.lean").write_text(
        "\n".join(f"import WildNumber.FiniteCertificates.Batch{i:03d}" for i in range(len(batches))) +
        "\n\nnamespace WildNumber.Nine.Census\nset_option maxRecDepth 12000\n" +
        "theorem all_representatives : ∀ g ∈ repMasks, ∀ B, ¬ NumericModel g B := by\n"
        "  have h : ∀ batch ∈ repBatches, ∀ g ∈ batch, ∀ B, ¬ NumericModel g B :=\n    " +
        "".join(f"checkedCons checked{i:03d} (" for i in range(len(batches))) +
        "by simp" + ")"*len(batches) +
        "\n  intro g hg\n  obtain ⟨xs,hxs,hg⟩ := List.mem_flatten.mp " +
        "(show g ∈ repBatches.flatten by simpa [repMasks] using hg)\n"
        "  exact h xs hxs g hg\nend WildNumber.Nine.Census\n",encoding="utf8")


if __name__ == "__main__":
    main()
