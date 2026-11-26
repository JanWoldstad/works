"""Generate relabeling witnesses for the independent Lean link census."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "combin"))
from minimum_link import canonical_label, link_types


def permutation_code(order):
    return sum(vertex << (3 * index) for index, vertex in enumerate(order))


def lean_array(xs):
    return "#[" + ", ".join(hex(x) for x in xs) + "]"

def write_lean(path, source):
    if not path.exists() or path.read_text(encoding="utf-8") != source:
        path.write_text(source, encoding="utf-8")


def main():
    directory = ROOT / "WildNumber" / "Orbit"
    directory.mkdir(exist_ok=True)
    graphs = link_types()
    levels = [[g for g in graphs if g.bit_count() == d] for d in range(12)]
    data = ["import WildNumber.OrbitCheck", "", "namespace WildNumber.Nine.Orbit", ""]
    for d, level in enumerate(levels):
        data.append(f"def level{d} : Array Nat := {lean_array(level)}")
    data.append("\ndef reps : Nat → Array Nat")
    data.extend(f"  | {d} => level{d}" for d in range(12))
    data.append("  | _ => #[]\n\nend WildNumber.Nine.Orbit\n")
    write_lean(directory / "Data.lean", "\n".join(data))
    imports = []
    combined = []
    lanes = [None] * 3
    for d, level in enumerate(levels[:-1]):
        index = {g: i for i, g in enumerate(levels[d + 1])}
        rows = []
        for g in level:
            row = 0
            for k in range(28):
                if g & (1 << k):
                    continue
                target, order = canonical_label(g | 1 << k, 8)
                inverse = [order.index(i) for i in range(8)]
                witness = (permutation_code(inverse) | permutation_code(order) << 24
                           | index[target] << 48)
                row |= witness << (58 * k)
            rows.append(row)
        # Short chunks keep reduction depth and recompilation costs bounded.
        modules = []
        for start in range(0, len(rows), 32):
            chunk = rows[start:start+32]
            name = f"L{d}x{start}"
            modules.append((start, len(chunk), name))
            lane = len(imports) % len(lanes)
            dependency = lanes[lane] or "Data"
            lanes[lane] = name
            imports.append(f"import WildNumber.Orbit.{name}")
            source = f"""import WildNumber.Orbit.{dependency}

namespace WildNumber.Nine.Orbit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk{name} : CoversRows level{d} level{d+1} {start} {len(chunk)} := by
  apply rows_of_check {lean_array(chunk)}
  decide +kernel

end WildNumber.Nine.Orbit
"""
            write_lean(directory / f"{name}.lean", source)
        combined.append(f"theorem checked{d} : CoversRows level{d} level{d+1} 0 {len(level)} := by")
        for start, length, name in modules[:-1]:
            combined.append(f"  apply rows_append (m := {length}) (n := {len(rows)-start-length}) chunk{name}")
        combined.append(f"  exact chunk{modules[-1][2]}\n")
    write_lean(directory / "All.lean", "\n".join(imports + ["", "namespace WildNumber.Nine.Orbit",""] +
        combined + ["end WildNumber.Nine.Orbit", ""]))


if __name__ == "__main__":
    main()
