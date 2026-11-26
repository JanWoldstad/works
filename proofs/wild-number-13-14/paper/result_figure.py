"""Render the result with ReportLab and Poppler after checking its Lean statements."""
from pathlib import Path
import subprocess
import sys
import tempfile

from reportlab.lib.colors import HexColor
from reportlab.pdfgen.canvas import Canvas

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
sys.path.insert(0, str(PROJECT))
from witness import EDGES, connected, matchings, witness


def verified_statements():
    names = [f"WildNumber.wildNumber_K{n}" for n in (13, 14)]
    query = "import WildNumber\nopen WildNumber\n" + "".join(
        f"#check {name}\n#print axioms {name}\n" for name in names
    )
    output = subprocess.run(
        ["lake", "env", "lean", "--stdin"], cwd=PROJECT, input=query,
        capture_output=True, text=True, encoding="utf-8", check=True,
    ).stdout.splitlines()
    statements = []
    for n, name in zip((13, 14), names):
        statement = f"{name} (C : Coloring {n}) : wildNumber C = 9"
        audit = f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        if statement not in output or audit not in output:
            raise ValueError(f"Unexpected Lean output for {name}:\n" + "\n".join(output))
        statements.append(output[output.index(statement)])
    return statements


def verified_example():
    colors = [7 * (a + b) % 13 for a, b in EDGES]
    classes = matchings(colors)
    _, _, _, wild = witness(colors, case=0)
    bridges = [(1, 12), (3, 10), (4, 9)]
    if len(set(wild)) != 9 or not set(bridges) <= set(classes[0]):
        raise ValueError("Unexpected wild set or color-0 bridges")
    if len(set(wild + bridges)) != 12 or not connected(wild + bridges):
        raise ValueError("The displayed subgraph is not a spanning tree")
    if not all(connected(wild + matching) for matching in classes.values()):
        raise ValueError("The wild edges must work for every color")
    return wild, bridges


def draw_tree(page, wild, bridges, x_offset, top, background):
    positions = {
        0: (308, 316), 1: (242, 347), 3: (374, 348), 9: (308, 268),
        2: (246, 211), 4: (306, 212), 7: (188, 230),
        5: (109, 390), 8: (63, 354), 12: (171, 383),
        6: (506, 387), 10: (441, 384), 11: (558, 353),
    }
    coords = {v: (x + x_offset, top - y) for v, (x, y) in positions.items()}
    for edges, color, weight, dash in ((wild, "#187466", 4, []), (bridges, "#B64E27", 3.5, [7, 5])):
        page.setStrokeColor(HexColor(color))
        page.setLineWidth(weight)
        page.setDash(dash)
        for a, b in edges:
            page.line(*coords[a], *coords[b])
    page.setDash()
    for vertex, (x, y) in coords.items():
        page.setFillColor(HexColor(background))
        page.setStrokeColor(HexColor("#172F2C"))
        page.setLineWidth(1.7)
        page.circle(x, y, 13.5, stroke=1, fill=1)
        page.setFillColor(HexColor("#172F2C"))
        page.setFont("Helvetica-Bold", 14)
        page.drawCentredString(x, y-5, str(vertex))


def draw(path, statements, wild, bridges):
    width, height = 1000, 635
    page = Canvas(str(path), pagesize=(width, height), invariant=1)
    page.setTitle("Nine wild edges suffice")
    page.setAuthor("Astra (OpenAI Codex) and JanWoldstad")
    ink = "#172F2C"
    green, rust = "#187466", "#B64E27"
    paper, rule = "#FBF9F2", "#BBC9BD"

    def label(x, y, value, size, font="Helvetica", color=ink):
        page.setFont(font, size)
        page.setFillColor(HexColor(color))
        page.drawString(x, height - y, value)

    def line(a, b, color, weight=1, dash=()):
        page.setStrokeColor(HexColor(color))
        page.setLineWidth(weight)
        page.setDash(list(dash))
        page.line(a[0], height-a[1], b[0], height-b[1])
        page.setDash()

    page.setFillColor(HexColor(paper))
    page.rect(0, 0, width, height, fill=1, stroke=0)
    label(44, 40, "THE WILD-NUMBER CONJECTURE", 13, "Helvetica-Bold", green)
    label(42, 94, "Nine wild edges suffice", 54, "Times-Bold")
    label(45, 126, "For complete graphs on 13 or 14 vertices, every minimum proper edge coloring has wild number nine.", 19)
    line((44, 149), (956, 149), rule)
    label(45, 182, "A spanning tree for color 0", 23, "Times-Bold")
    line((607, 172), (607, 456), rule)

    draw_tree(page, wild, bridges, 0, height, paper)

    line((47, 441), (82, 441), green, 4)
    label(91, 446, "9 wild edges", 16, "Helvetica-Bold", green)
    line((245, 441), (284, 441), rust, 3.5, (7, 5))
    label(294, 446, "3 edges of color 0", 16, "Helvetica-Bold", rust)

    label(635, 189, "How to read the tree", 23, "Times-Bold")
    for y, value in [
        (226, "The solid edges are wild cards."),
        (250, "They form four groups of vertices."),
        (286, "The three dashed edges all have"),
        (310, "color 0. They join the four groups"),
        (334, "into a tree covering all 13 vertices."),
        (379, "Pick another color in this example."),
        (403, "The same nine wild edges still work."),
        (439, "All 13 colors checked."),
    ]:
        label(636, y, value, 17, "Helvetica-Bold" if y == 439 else "Helvetica",
              green if y == 439 else ink)

    page.setFillColor(HexColor(ink))
    page.rect(0, 0, width, height - 477, fill=1, stroke=0)
    label(45, 506, "WHAT LEAN PROVES FOR EVERY COLORING", 13, "Helvetica-Bold", "#9DDBCA")
    for i, statement in enumerate(statements):
        label(45, 537 + 24*i, statement, 17, "Courier", "#FFFFFF")
    label(45, 597, "The lower bound is sharp. Eight wild edges can never suffice.", 16,
          color="#CDE3DB")
    label(45, 619, "Astra (OpenAI Codex) and JanWoldstad", 12, color="#CDE3DB")
    page.showPage()
    page.save()


if __name__ == "__main__":
    statements = verified_statements()
    wild, bridges = verified_example()
    tree = Canvas(str(HERE / "example-tree.pdf"), pagesize=(542, 226), invariant=1)
    tree.setTitle("A spanning tree in the cyclic coloring of K13")
    draw_tree(tree, wild, bridges, -40, 418, "#FFFFFF")
    tree.showPage()
    tree.save()
    with tempfile.TemporaryDirectory() as directory:
        vector = Path(directory) / "figure.pdf"
        draw(vector, statements, wild, bridges)
        subprocess.run(["pdftoppm", "-png", "-scale-to", "2200", "-singlefile",
                        str(vector), str(HERE / "nine-wild-edges")], check=True)
