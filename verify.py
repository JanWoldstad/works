"""Run the executable checks for the 13- and 14-vertex wild-number proof."""

import argparse
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent


def run_check(label, command, expected_prefixes):
    print(f"\nChecking {label} ...", flush=True)
    result = subprocess.run(command, stdout=subprocess.PIPE, text=True)
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    lines = result.stdout.splitlines()
    for prefix in expected_prefixes:
        if not any(line.startswith(prefix) for line in lines):
            raise SystemExit(f"{label}: missing result starting with {prefix!r}")


def cpp_census():
    for name in ("c++", "g++", "clang++", "cl"):
        compiler = shutil.which(name)
        if compiler:
            break
    else:
        raise SystemExit("The C++ check needs GCC, Clang, or an x64 MSVC developer shell.")

    source = ROOT / "blockers" / "link_search.cpp"
    with tempfile.TemporaryDirectory() as build:
        executable = Path(build) / ("link_search.exe" if sys.platform == "win32" else "link_search")
        if name == "cl":
            command = [compiler, "/nologo", "/O2", "/EHsc", "/std:c++17", str(source), f"/Fe{executable}"]
        else:
            command = [compiler, "-O2", "-std=c++17", str(source), "-o", str(executable)]
        print(f"\nBuilding the maximum-degree checker with {compiler} ...", flush=True)
        subprocess.run(command, cwd=build, check=True)
        run_check("the generated maximum-degree census", [executable], [
            "degree 18 tested 663 survivors 1",
            "degree 19 tested 402 survivors 1",
            "PASS: all surviving links have the two reported forms.",
        ])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--with-cpp", action="store_true",
                        help="also build and run the independent C++17 graph census")
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        parser.exit(1, "The checkers require Python 3.10 or later.\n")

    checks = [
        ("the minimum-degree blocker classification", "combin/minimum_link.py", [
            "PASS: classified every blocker with at most 35 triples and maximum degree at most 19; 2481 link types.",
        ]),
        ("the maximum-degree graph atlas census", "blockers/check_graph6.py", [
            "Examined 11072 eligible links in 12346 atlas records",
            "Survivors by degree: [(18, 1), (19, 1)]",
        ]),
        ("the two terminal matching configurations", "sat/check_terminal_links.py", [
            "degree=18 mask=268434432 perfect_matchings=0 edge_disjoint_pairs=0",
            "degree=19 mask=268434944 perfect_matchings=6 edge_disjoint_pairs=0",
        ]),
        ("explicit witnesses for both cases of the cyclic coloring", "witness.py", [
            "k=0, blocks=", "k=1, blocks=", "9 wild edges connect all 13 colors:",
        ]),
    ]
    for label, script, expected in checks:
        run_check(label, [sys.executable, "-I", "-B", ROOT / script], expected)
    if args.with_cpp:
        cpp_census()
    print("\nAll requested checks passed.")


if __name__ == "__main__":
    main()
