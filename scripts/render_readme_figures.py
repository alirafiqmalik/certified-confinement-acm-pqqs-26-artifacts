#!/usr/bin/env python3
"""Render README figures from the sample circuit and committed benchmark data.

Run with Python and matplotlib: python3 scripts/render_readme_figures.py
The ring and partition follow heavyHex and tenantF in the linked Lean modules.
"""
import json
import re
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "docs/assets"
OUT.mkdir(parents=True, exist_ok=True)
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 12,
                     "svg.fonttype": "none", "svg.hashsalt": "confinement"})
INK, TEAL, RED = "#172b4d", "#087f8c", "#c43b4d"


def save(fig, name):
    fig.savefig(OUT / f"{name}.svg", bbox_inches="tight", facecolor="white",
                metadata={"Date": None, "Creator": "Certified Qubit Confinement"})
    path = OUT / f"{name}.svg"
    path.write_text("\n".join(line.rstrip() for line in path.read_text().splitlines()) + "\n")
    plt.close(fig)


def topology():
    source = (ROOT / "examples/02_cotenant_touch.qasm").read_text()
    gates = [(int(a), int(b)) for a, b in re.findall(r"^cz q\[(\d+)\],\s*q\[(\d+)\];", source, re.M)]
    # CompileHH.lean defines the cycle 0--1--...--11--0;
    # Confine.lean defines tenantF as 6 <= q < 12.
    angles = np.pi / 2 - (np.arange(12) + 0.5) * 2 * np.pi / 12
    points = np.column_stack((np.cos(angles), np.sin(angles)))
    fig, ax = plt.subplots(figsize=(10, 4.8))
    for a in range(12):
        b = (a + 1) % 12
        ax.plot(*points[[a, b]].T, color="#cbd5e1", lw=3, zorder=1)
    for a, b in gates:
        ax.plot(*points[[a, b]].T, color=RED if max(a, b) >= 6 else TEAL, lw=6, zorder=2)
    for q, (x, y) in enumerate(points):
        ax.scatter(x, y, s=780, color=TEAL if q < 6 else RED, edgecolor="white", lw=2, zorder=3)
        ax.text(x, y, str(q), color="white", ha="center", va="center", weight="bold", zorder=4)
    ax.text(1.5, .83, "LEGAL EDGE.\nFORBIDDEN SUPPORT.", color=INK, fontsize=19, weight="bold", va="top")
    ax.text(1.5, .12, "cz q[5], q[6];", color=RED, fontsize=17, family="monospace")
    ax.text(1.5, -.18, "The device permits edge 5–6.\nThe policy forbids touching qubit 6.\n\nResult: REJECT", color=INK, linespacing=1.6, va="top")
    ax.text(-1.15, -1.36, "Forbidden F = {6…11}", color=RED, fontsize=11)
    ax.text(.45, -1.36, "Allowed A = {0…5}", color=TEAL, fontsize=11)
    ax.set(xlim=(-1.4, 4.6), ylim=(-1.5, 1.3), aspect="equal")
    ax.axis("off")
    save(fig, "confinement")


def benchmark():
    data = json.loads((ROOT / "harness/benchmarks/e5_results.json").read_text())
    rows = [data[f"opt{i}"]["full"] for i in range(4)]
    rates = [100 * row["violations"] / row["n"] for row in rows]
    fig, ax = plt.subplots(figsize=(9, 3.8))
    bars = ax.bar(range(4), rates, width=.5, color=[TEAL, "#267a9c", "#415f91", INK])
    for bar, row, rate in zip(bars, rows, rates):
        ax.text(bar.get_x() + bar.get_width()/2, rate+2,
                f'{row["violations"]}/{row["n"]} · {rate:.0f}%', ha="center", color=INK, weight="bold")
    ax.set(xticks=range(4), xticklabels=[f"Level {i}" for i in range(4)], ylim=(0, 90),
           ylabel="Confinement violations (%)", xlabel="Qiskit optimization level")
    ax.set_title("Unconstrained transpilation · 38 circuits per level", loc="left", color=INK, pad=18, weight="bold")
    ax.spines[["top", "right"]].set_visible(False)
    ax.set_axisbelow(True)
    ax.grid(axis="y", alpha=.15)
    fig.text(.12, -.10, "QASMBench-small subset · 12-node ring · safe parser · committed reference run", fontsize=10, color=INK)
    save(fig, "benchmark")


if __name__ == "__main__":
    topology()
    benchmark()
