#!/usr/bin/env python3
"""Reproduce the paper's mathematical figures (optional NumPy/Matplotlib).

The renderer never participates in proof verification. Integer examples use
exact arithmetic; complex pixels are explicitly finite floating-point trials.
No research-tree import, network access, or generated external asset is used.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import platform

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import BoundaryNorm, ListedColormap
from matplotlib.patches import FancyArrowPatch, Patch, Rectangle
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "figures"
WORD = (1, 0, -1)
INK = "#24313b"
MUTED = "#596670"
GRID = "#e1e5e8"
BLUE = "#0072B2"
ORANGE = "#D55E00"
GREEN = "#009E73"
GOLD = "#E69F00"
PURPLE = "#CC79A7"
GRAY = "#d8dde1"
DARK = "#48535e"
COLORS = [GRAY, BLUE, ORANGE, DARK, PURPLE, GREEN, GOLD]

plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 8.3,
    "mathtext.fontset": "dejavusans", "pdf.fonttype": 42,
    "axes.titlesize": 9.1, "axes.labelsize": 8.5,
    "xtick.labelsize": 7.4, "ytick.labelsize": 7.4,
    "legend.fontsize": 7.4, "axes.edgecolor": "#78838b",
    "axes.labelcolor": INK, "text.color": INK,
    "xtick.color": MUTED, "ytick.color": MUTED,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.linewidth": 0.55, "lines.linewidth": 1.1,
    "savefig.facecolor": "white", "figure.facecolor": "white",
})


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(value):
    return hashlib.sha256(value).hexdigest()


@lru_cache(maxsize=None)
def read_certificate(relative):
    return json.loads((ROOT / relative).read_text())


def geometry():
    return read_certificate("certificates/geometry/certificate.json")


def T(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def U(n):
    return (n + 1) // 2 if n % 2 else 3 * n // 2


def orbit(seed, phase=0):
    values, positions = [], {}
    state = seed, phase
    while state not in positions:
        require(len(values) < 10000, "Integer orbit did not close within the stated budget")
        positions[state] = len(values)
        values.append(state)
        n, p = state
        state = T(n) + WORD[p], (p + 1) % 3
    return values, positions[state]


def lap(n):
    for d in WORD:
        n = T(n) + d
    return n


def save(fig, name, title):
    OUT.mkdir(parents=True, exist_ok=True)
    fig.savefig(OUT / (name + ".pdf"), dpi=230,
                metadata={"Title": title, "Creator": "Collatz release figure renderer",
                          "CreationDate": None, "ModDate": None})
    plt.close(fig)


def panel(ax, title):
    ax.set_title(title, loc="left", fontweight="semibold", pad=8)
    ax.tick_params(length=3, width=0.55)


def arrow(ax, start, end, color=INK, lw=1.25, scale=9, **kwargs):
    if start != end:
        ax.add_patch(FancyArrowPatch(start, end, arrowstyle="-|>",
                                    mutation_scale=scale, color=color,
                                    linewidth=lw, shrinkA=2, shrinkB=2, **kwargs))


def phase_cycles():
    short, mu0 = orbit(0)
    long, mu1 = orbit(1)
    require(mu0 == mu1 == 0 and len(short) == 3 and len(long) == 9,
            "Wrong integer cycle periods")
    require([n for n, p in long if p == 0] == [1, 7, 2], "Wrong return cycle")
    certified = geometry()["discrete_cycles"]["cycles"]
    require([list(s) for s in short] == certified[0]["states"] and
            [list(s) for s in long] == certified[1]["states"], "Cycle data disagree with the certificate")
    fig = plt.figure(figsize=(6.4, 3.9))
    ax = fig.add_axes([0.00, 0.08, 0.65, 0.84], projection="3d")
    theta0 = -np.pi / 2
    for p in range(3):
        angle = theta0 + 2 * np.pi * p / 3
        x, y = np.cos(angle), np.sin(angle)
        ax.plot([x, x], [y, y], [0, 12.5], color="#aeb7bd", lw=0.7)
        ax.text(1.25*x, 1.25*y, -1.2, f"$\\varphi={p}$\nnext {['+1','0','-1'][p]}",
                ha="center", va="top", fontsize=7.5, color=MUTED)
    theta = np.linspace(0, 2*np.pi, 180)
    for height in (0, 4, 8, 12):
        ax.plot(np.cos(theta), np.sin(theta), np.full_like(theta, height),
                color=GRID, lw=0.6, zorder=0)
    for cycle, color, marker in ((short, BLUE, "o"), (long, ORANGE, "D")):
        for j, (n, p) in enumerate(cycle):
            target = cycle[(j+1) % len(cycle)][0]
            angles = theta0 + 2*np.pi/3 * (p + np.linspace(0, 1, 35))
            heights = np.linspace(n, target, len(angles))
            ax.plot(np.cos(angles), np.sin(angles), heights, color=color, lw=1.45)
            k = 18
            ax.quiver(np.cos(angles[k]), np.sin(angles[k]), heights[k],
                      np.cos(angles[k+2])-np.cos(angles[k]),
                      np.sin(angles[k+2])-np.sin(angles[k]), heights[k+2]-heights[k],
                      color=color, arrow_length_ratio=0.55, linewidth=0.8)
            angle = theta0 + 2*np.pi*p/3
            ax.scatter(np.cos(angle), np.sin(angle), n, s=25, color=color,
                       marker=marker, edgecolor="white", linewidth=0.4, depthshade=False)
            if p == 0:
                ax.text(.17, -1.13, n+.08, str(n), color=color, fontsize=7.7, ha="left",
                        bbox={"facecolor": "white", "edgecolor": "none", "alpha": .92, "pad": .25})
            else:
                ax.text(1.35*np.cos(angle), 1.35*np.sin(angle), n,
                        str(n), color=color, fontsize=7.7, ha="left" if p == 1 else "right",
                        bbox={"facecolor": "white", "edgecolor": "none", "alpha": .92, "pad": .25})
    ax.set(xlim=(-1.45, 1.45), ylim=(-1.45, 1.45), zlim=(-1.6, 13.3),
           xticks=[], yticks=[], zticks=[0, 4, 8, 12])
    ax.set_zlabel("Integer height $n$", fontsize=8, labelpad=3)
    ax.view_init(elev=19, azim=-90)
    ax.set_box_aspect((1, 1, 1.7))
    ax.grid(False)
    for axis in (ax.xaxis, ax.yaxis, ax.zaxis):
        axis.pane.set_facecolor((1, 1, 1, 0))
        axis.pane.set_edgecolor((1, 1, 1, 0))
    ax.xaxis.line.set_visible(False)
    ax.yaxis.line.set_visible(False)
    fig.text(0.035, 0.94, "(a) The integer and its forcing phase", fontsize=9.1, weight="semibold")
    bx = fig.add_axes([0.69, 0.16, 0.285, 0.72])
    bx.set(xlim=(0, 1), ylim=(0, 1.5), aspect="equal")
    bx.axis("off")
    positions = {1: (0.18, 0.24), 7: (0.82, 0.24), 2: (0.5, 0.79)}
    for a, b in ((1, 7), (7, 2), (2, 1)):
        arrow(bx, positions[a], positions[b], ORANGE, lw=1.7, scale=11)
    for n, point in positions.items():
        bx.scatter(*point, s=145, color=ORANGE, marker="D", zorder=3,
                   edgecolor="white", linewidth=1)
        bx.annotate(str(n), point, ha="center", va="center", color="white", fontsize=8.1)
    fig.text(0.69, 0.94, "(b) Phase-zero returns", fontsize=9.1, weight="semibold")
    bx.text(0.5, -.01, "$1\\to7\\to2\\to1$", ha="center", color=ORANGE, fontsize=9)
    bx.text(0.5, -.17, "3 returns = 9 updates", ha="center", color=ORANGE, fontsize=8)
    bx.scatter(.5, 1.24, s=155, color=BLUE, edgecolor="white", linewidth=1, zorder=5)
    bx.text(.5, 1.24, "0", ha="center", va="center", color="white", fontsize=8.4, zorder=6)
    bx.add_patch(FancyArrowPatch((.45, 1.29), (.55, 1.29), connectionstyle="arc3,rad=-1.7",
                                 arrowstyle="-|>", mutation_scale=9, color=BLUE, lw=1.3))
    bx.text(.5, 1.04, "1 return = 3 updates", ha="center", color=BLUE, fontsize=8)
    fig.text(0.035, 0.025, "One prescribed word $(+1,0,-1)$; a repeated height closes an orbit only at the same phase.",
             fontsize=8, color=MUTED)
    save(fig, "phase_cycles", "Two exact integer cycles with their forcing phase")
    return {"forcing": list(WORD), "short_cycle": short, "long_cycle": long,
            "minimal_augmented_periods": [3, 9],
            "phase_zero_return_cycles": [[0], [1, 7, 2]],
            "geometry": "Arcs encode discrete updates; arc interiors are not orbit states."}


def integer_return():
    records = []
    for r in range(8):
        a, b, odd = 8, r, 0
        for d in WORD:
            require(a % 2 == 0, "Symbolic branch parity varies")
            if b % 2:
                a, b = 3*a//2, (3*b+1)//2+d
                odd += 1
            else:
                a, b = a//2, b//2+d
        require(a == 3**odd, "Wrong symbolic branch coefficient")
        records.append({"residue": r, "coefficient": a, "constant": b, "odd_inputs": odd})
    for row, certified in zip(records, geometry()["discrete_cycles"]["return_branches"]):
        require((row["residue"], row["coefficient"], row["constant"]) ==
                (certified["residue_mod_8"], certified["slope_in_quotient"], certified["offset"]),
                "Return formula disagrees with exact certificate")
    require([lap(n) for n in range(9)] == [0, 7, 1, 4, 7, 6, 0, 2, 3], "Wrong return values")
    fig = plt.figure(figsize=(6.4, 4.15))
    ax = fig.add_axes([0.09, 0.33, 0.43, 0.56])
    bx = fig.add_axes([0.635, 0.33, 0.32, 0.56])
    palette = {1: PURPLE, 3: BLUE, 9: GREEN, 27: ORANGE}
    marks = ["o", "o", "s", "o", "s", "^", "o", "^"]
    for row, marker in zip(records, marks):
        r, a, b = row["residue"], row["coefficient"], row["constant"]
        xs = np.arange(r, 64, 8)
        ys = np.array([lap(int(n)) for n in xs])
        require(np.array_equal(ys, a*np.arange(len(xs))+b), "Displayed branch mismatch")
        ax.scatter(xs, ys, s=13, marker=marker, color=palette[a], zorder=3)
    ax.plot([0, 63], [0, 63], "--", color=MUTED, lw=0.75)
    ax.text(42, 37, "$y=x$", color=MUTED, fontsize=7.8)
    ax.set(xlim=(-1, 64), ylim=(-3, 205), xticks=[0, 16, 32, 48, 64],
           yticks=[0, 50, 100, 150, 200], xlabel="Integer input $n$ at phase zero", ylabel="Return value $F(n)$")
    ax.grid(color=GRID, lw=0.55)
    ax.set_axisbelow(True)
    panel(ax, "(a) Eight exact residue branches")
    bx.plot([-.2, 8.2], [-.2, 8.2], "--", color=MUTED, lw=0.7)
    bx.scatter(range(9), [lap(n) for n in range(9)], s=17, color="#b8c0c6", zorder=2)
    for returns, color in (([6, 0, 0], BLUE), ([1, 7, 2, 1], ORANGE)):
        for x, y in zip(returns, returns[1:]):
            arrow(bx, (x, x), (x, y), color, lw=1.2, scale=8)
            arrow(bx, (x, y), (y, y), color, lw=1.2, scale=8)
            bx.scatter(x, x, s=19, marker="s", facecolor="white", edgecolor=color, lw=1, zorder=5)
            bx.scatter(x, y, s=21, color=color, edgecolor="white", lw=0.45, zorder=6)
    bx.set(xlim=(-.4, 8.4), ylim=(-.4, 8.4), aspect="equal", xticks=[0, 2, 4, 6, 8],
           yticks=[0, 2, 4, 6, 8], xlabel="Current integer input", ylabel="Next return")
    panel(bx, "(b) Exact return orbits")
    tx = fig.add_axes([0.08, 0.04, 0.88, 0.20])
    tx.axis("off")
    formulas = [("k" if row["coefficient"] == 1 else f"{row['coefficient']}k")
                + (f"+{row['constant']}" if row["constant"] else "") for row in records]
    table = tx.table(cellText=[["$r$"]+[str(r) for r in range(8)],
                               ["$F(8k+r)$"]+["$"+s+"$" for s in formulas]],
                     cellLoc="center", colWidths=[.19]+[.10125]*8, loc="center")
    table.auto_set_font_size(False)
    table.set_fontsize(8)
    table.scale(1, 1.25)
    for (row, col), cell in table.get_celld().items():
        cell.set_edgecolor(GRID)
        cell.set_linewidth(.5)
        if col:
            cell.get_text().set_color(palette[records[col-1]["coefficient"]])
    save(fig, "integer_return", "Exact integer branches and return-map iteration")
    return {"forcing": list(WORD), "return_symbol": "F", "branches": records, "parameter_domain": "integer k >= 0",
            "displayed_inputs": [0, 63], "cobwebs": [[6, 0, 0], [1, 7, 2, 1]],
            "interpolation": "Only dots are map values; cobweb segments encode iteration."}


def exact_integer_basins(stop=65536, cap=10000):
    known = {}
    labels = np.zeros(stop, dtype=np.uint8)
    maximum_uncached_returns = 0
    new_cycles = []
    for seed in range(stop):
        n, trail, positions = seed, [], {}
        while n not in known and n not in positions and len(trail) < cap:
            positions[n] = len(trail)
            trail.append(n)
            n = lap(n)
        maximum_uncached_returns = max(maximum_uncached_returns, len(trail))
        if n in known:
            tag = known[n]
        elif n in positions:
            cycle = trail[positions[n]:]
            index = cycle.index(min(cycle))
            cycle = cycle[index:]+cycle[:index]
            tag = 1 if cycle == [0] else 2 if cycle == [1, 7, 2] else 3
            new_cycles.append(cycle)
        else:
            tag = 0
        labels[seed] = tag
        if tag:
            for value in trail:
                known[value] = tag
    return labels, {"seed_interval": [0, stop-1], "return_budget_per_uncached_path": cap,
                    "counts_by_code": np.bincount(labels, minlength=4).tolist(),
                    "maximum_uncached_returns": maximum_uncached_returns,
                    "new_cycles": new_cycles,
                    "labels_sha256": digest(labels.tobytes())}


def binary_address(x, y, depth=4):
    return sum((((x >> (depth-1-level)) & 1)+2*((y >> (depth-1-level)) & 1))*4**level
               for level in range(depth))


def binary_basins():
    labels, audit = exact_integer_basins()
    require(audit["counts_by_code"] == [0, 32123, 33413, 0], "Unexpected exact basin census")
    fig, axes = plt.subplots(1, 3, figsize=(6.4, 3.20))
    fig.subplots_adjust(left=.07, right=.985, top=.84, bottom=.30, wspace=.24)
    cmap = ListedColormap([GRAY, BLUE, ORANGE, PURPLE])
    norm = BoundaryNorm(np.arange(5)-.5, 4)
    views = []
    settings = [(0, 1, "(a) All low-bit endings", 1), (1, 4, "(b) Ending 01", 2),
                (9, 16, "(c) Ending 1001", None)]
    for ax, (residue, stride, title, quadrant) in zip(axes, settings):
        seeds = np.array([[residue+stride*binary_address(x, y) for x in range(16)] for y in range(16)])
        tiles = labels[seeds]
        ax.pcolormesh(np.arange(17), np.arange(17), tiles, cmap=cmap, norm=norm,
                      shading="flat", edgecolors="none", rasterized=False)
        ax.set(xlim=(0, 16), ylim=(16, 0), aspect="equal", xticks=[0, 8, 16], yticks=[0, 8, 16])
        ax.axhline(8, color="white", lw=.75)
        ax.axvline(8, color="white", lw=.75)
        ax.set_xlabel("Bit-interleaved column", labelpad=3, fontsize=7.4)
        panel(ax, title)
        if ax is axes[0]:
            ax.set_ylabel("Bit-interleaved row", labelpad=2, fontsize=7.4)
        if quadrant is not None:
            ax.add_patch(Rectangle((8*(quadrant%2)+.15, 8*(quadrant//2)+.15),
                                   7.7, 7.7, fill=False, edgecolor=INK, lw=1.4))
        counts = np.bincount(tiles.ravel(), minlength=4).tolist()
        ax.text(.5, -.20, f"$n={residue}+{stride}j$, $0\\leq j<256$\n"
                f"{counts[1]} short / {counts[2]} long", transform=ax.transAxes,
                fontsize=7.6, ha="center", va="top")
        views.append({"residue": residue, "modulus": stride, "seeds": seeds.tolist(),
                      "classes": tiles.tolist(), "counts_by_code": counts})
    fig.legend(handles=[Patch(facecolor=BLUE, label="Exact entry: 3-cycle"),
                        Patch(facecolor=ORANGE, label="Exact entry: 9-cycle"),
                        Patch(facecolor=GRAY, label="Unresolved (0 shown)")],
               loc="lower center", bbox_to_anchor=(.52, .005), ncol=3, frameon=False,
               handlelength=1, columnspacing=1.4, fontsize=7.6)
    save(fig, "binary_basins", "Exact integer basin samples in binary residue neighborhoods")
    return {**audit, "views": views,
            "address": "Low base-4 digits select coarse quadrants; digit = column_bit + 2*row_bit.",
            "zoom_scope": "Fixes further low bits and adds higher seeds; not interpolation of a real interval.",
            "proof_scope": "Finite exact samples; neither basin density nor absence of other basins follows."}


def affine_step(a, b, phase, forcing):
    require(a % 2 == 0, "Affine parity is not uniform")
    a, b = (3*a//2, (3*b+1)//2) if b % 2 else (a//2, b//2)
    return a, b+forcing[phase], (phase+1) % len(forcing)


def seven_step_merger():
    forcing = (0, 0, 1, -1, 0, 1, -1)
    traces = []
    for start, steps in (((12, 9, 6), 2), ((24, 17, 5), 3)):
        trace = [start]
        for _ in range(steps):
            trace.append(affine_step(*trace[-1], forcing))
        traces.append(trace)
    require(traces[0][-1] == traces[1][-1] == (27, 20, 1), "Merger endpoint mismatch")
    fig = plt.figure(figsize=(6.4, 3.6))
    ax = fig.add_axes([.025, .24, .95, .68])
    ax.set(xlim=(0, 10), ylim=(0, 3.1))
    ax.axis("off")
    source = [(1.1, 2.35), (4.15, 2.35), (8.6, 1.5)]
    alternate = [(1.1, .65), (3.6, .65), (6.1, .65), (8.6, 1.5)]
    for points, trace, color, marker in ((source, traces[0], ORANGE, "o"),
                                         (alternate, traces[1], BLUE, "s")):
        for left, right in zip(points, points[1:]):
            arrow(ax, left, right, color, lw=1.4, scale=10)
        for index, ((x, y), (a, b, phase)) in enumerate(zip(points, trace)):
            if index == len(points)-1:
                continue
            ax.scatter(x, y, s=40, color=color, marker=marker, zorder=3)
            ax.text(x, y+.31, f"$n={a}q+{b}$", ha="center", fontsize=9, color=color)
            ax.text(x, y-.30, f"phase {phase}", ha="center", fontsize=8, color=MUTED)
    ax.scatter(8.6, 1.5, s=55, color=GREEN, marker="D", zorder=4)
    ax.text(8.6, 1.91, "$n=27q+20$", ha="center", color=GREEN, fontsize=9)
    ax.text(8.6, 1.11, "same phase 1", ha="center", color=GREEN, fontsize=8)
    ax.text(1.1, 3.04, "Original launch", ha="center", color=ORANGE, fontsize=9.2, weight="semibold")
    ax.text(1.1, -.04, "Alternative launch", ha="center", color=BLUE, fontsize=9.2, weight="semibold")
    ax.text(5.8, 2.9, "2 updates", color=ORANGE, fontsize=8.3)
    ax.text(5.5, .02, "3 updates", color=BLUE, fontsize=8.3)
    fig.text(.065, .16, "Physical seed:", fontsize=8.3, weight="semibold")
    fig.text(.25, .16, "$24q+17 > 12q+9$", fontsize=9)
    fig.text(.53, .16, "Section rank:", fontsize=8.3, weight="semibold")
    fig.text(.70, .16, "$16q+12 < 16q+13$", fontsize=9)
    fig.text(.065, .055, "All integers $q\\geq0$; $m=4q+3$.  Original section $\\{3,5,6\\}$, "
             "$\\rho=(2m,2m,4m+1)$.", fontsize=8.2, color=MUTED)
    save(fig, "seven_step_merger", "A phase-correct whole-family merger with a smaller section rank")
    return {"forcing": list(forcing), "domain": "integer q >= 0", "physical_affine_traces": traces,
            "source_section_parameter": [4, 3], "alternate_section_parameter": [8, 6],
            "source_rank": [16, 13], "alternate_rank": [16, 12], "rank_gap": 1,
            "rank_scope": "Original section phases 3,5,6; rho(m,3)=rho(m,5)=2m, rho(m,6)=4m+1.",
            "horizontal_spacing": "Schematic: the two histories have unequal elapsed times."}


def synchronization():
    example = read_certificate("certificates/exposition/examples.json")["synchronization"]
    word = example["word"]
    require(example["initial_ensemble"] == list(range(1, 7)), "The displayed ensemble changed")
    paths = [[seed] for seed in example["initial_ensemble"]]
    for letter in word:
        for path in paths:
            path.append((T if letter == "T" else U)(path[-1]))
    reference = paths[0]
    require(reference == [1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1], "Wrong reference path")
    require(all(z in (1, 2, 3) for z in reference), "Reference escaped its protected set")
    require(all(not (reference[k] == 3 and letter == "T") for k, letter in enumerate(word)),
            "Forbidden reference transition")
    ensembles = [sorted({path[k] for path in paths}) for k in range(len(word)+1)]
    cardinalities = list(map(len, ensembles))
    require(cardinalities == [6, 5, 5, 5, 4, 3, 2, 2, 1, 1, 1], "Wrong ensemble counts")
    heights = [int(letter == "T") for letter in word]
    forcing = [heights[(k+1) % len(word)]-height for k, height in enumerate(heights)]
    response = [reference[k]-1+heights[k] for k in range(len(word))]
    physical = []
    for seed in range(6):
        path = [seed]
        for d in forcing:
            path.append(T(path[-1])+d)
        require(path[-1] == 0, "The displayed physical reset failed")
        require(all(path[k] == paths[seed][k]-1+heights[k % 10] for k in range(11)),
                "Physical and transformed trajectories disagree")
        physical.append(path)
    require(paths == [example["tracks"][str(seed)] for seed in range(1, 7)] and
            ensembles == example["ensembles"] and forcing == example["impulses"] and
            response == example["physical_response"] and
            physical == [record["physical"] for record in example["phase_zero_reset_paths"]],
            "Synchronization data disagree with exported exact example")
    other = 5
    for k in range(10):
        other = T(other)+forcing[(1+k) % 10]
    require(other == 3 and response[1] == 1, "Expected all-phase counterexample changed")
    fig = plt.figure(figsize=(6.4, 4.1))
    ax = fig.add_axes([.09, .38, .87, .48])
    bx = fig.add_axes([.09, .16, .87, .13], sharex=ax)
    x = np.arange(11)
    colors = [INK, BLUE, ORANGE, GREEN, PURPLE, GOLD]
    markers = ["o", "s", "^", "D", "v", "P"]
    ax.axhspan(.65, 3.35, facecolor="#f0f3f5", zorder=0)
    for seed, path, color, marker in reversed(list(zip(range(1, 7), paths, colors, markers))):
        ax.plot(x, path, color=color, marker=marker, markersize=3.5,
                lw=1.6 if seed == 1 else 1.0, label=f"$z_0={seed}$", zorder=8 if seed == 1 else 3)
    ax.set(xlim=(-.15, 10.2), ylim=(.3, 15.7), ylabel="Positive coordinate $z$", yticks=[1, 3, 6, 9, 12, 15])
    ax.tick_params(labelbottom=False)
    ax.grid(axis="y", color=GRID, lw=.55)
    for k, letter in enumerate(word):
        ax.text(k+.5, 15.15, letter, ha="center", fontsize=8.8, weight="semibold")
    ax.text(.02, 1.10, "(a) One common letter acts on all six states", transform=ax.transAxes,
            fontsize=9.1, weight="semibold")
    ax.annotate("Protected reference\n$r\\in\\{1,2,3\\}$", xy=(7, 2), xytext=(7.2, 7.5),
                fontsize=7.7, color=INK,
                arrowprops={"arrowstyle": "-", "color": MUTED, "lw": .65})
    handles, labels = ax.get_legend_handles_labels()
    fig.legend(handles[::-1], labels[::-1], loc="upper right", bbox_to_anchor=(.965, .995),
               ncol=6, frameon=False, columnspacing=.8, handlelength=1.2, fontsize=7.2)
    bx.step(x, cardinalities, where="post", color=INK, lw=1.3)
    bx.scatter(x, cardinalities, s=13, color=INK)
    bx.set(xticks=range(11), yticks=[1, 3, 6], ylim=(.5, 6.5), xlabel="Number of updates $k$", ylabel="$|S_k|$")
    bx.axvline(8, color=GREEN, ls="--", lw=.8)
    bx.text(8.15, 4.2, "Merged", color=GREEN, fontsize=7.5)
    fig.text(.09, .025, "Phase-zero seeds $0,\\ldots,5$ reset to $0$ after 10 updates; "
             "this example does not reset all phases.", fontsize=7.7, color=MUTED)
    save(fig, "synchronization", "A common word synchronizes a finite positive-coordinate ensemble")
    return {"word": word, "initial_ensemble": list(range(1, 7)), "reference": reference,
            "paths": paths, "ensembles": ensembles, "cardinalities": cardinalities,
            "height": heights, "forcing": forcing, "physical_response": response,
            "physical_paths": physical, "reset_phase": 0, "reset_physical_seeds": [0, 5],
            "not_all_phase": {"seed": 5, "phase": 1, "after_one_word": other, "response": response[1]}}


TARGET_CODES = {"integer_three": 1, "integer_nine": 2, "negative_integer_three": 4,
                "noninteger_nine": 5, "noninteger_three": 6}
TARGET_LABELS = {1: "Integer 3-cycle", 2: "Integer 9-cycle", 4: "Negative 3-cycle",
                 5: "Noninteger 9-cycle", 6: "Noninteger 3-cycle",
                 0: "Step budget reached", 3: "Magnitude guard reached"}


@lru_cache(maxsize=None)
def targets():
    by_phase = [{code: [] for code in (1, 2, 4, 5, 6)} for _ in range(3)]
    certificate = geometry()
    for cycle in certificate["integer_disks"]["cycles"]:
        require(Fraction(cycle["capture_radius"]) >= Fraction(1, 10**6), "Integer capture radius too small")
        code = TARGET_CODES[cycle["cycle_id"]]
        for n, phase in cycle["states"]:
            by_phase[phase][code].append(Fraction(n))
    for cycle in certificate["attracting_disks"]["cycles"]:
        require(Fraction(cycle["uniform_center_capture_radius"]) >= Fraction(1, 10**6),
                "Noninteger capture radius too small")
        code = TARGET_CODES[cycle["cycle_id"]]
        require(cycle["physical_period"] == (9 if code == 5 else 3), "Target period label changed")
        for disk in cycle["disks"]:
            center = Fraction(disk["center"])
            require(center == Fraction(disk["center_decimal"]), "Center representations differ")
            by_phase[disk["phase"]][code].append(center)
    for groups in by_phase:
        require({code: len(values) for code, values in groups.items()} == {1: 1, 2: 3, 4: 1, 5: 3, 6: 1},
                "The five target groups are incomplete at a phase")
        all_centers = [(code, value) for code, centers in groups.items() for value in centers]
        for i, (code, value) in enumerate(all_centers):
            for other_code, other in all_centers[i+1:]:
                if code != other_code:
                    require(abs(value-other) > Fraction(2, 10**6), "Overlapping target labels")
    return by_phase


def C(z):
    return z + .25 - (z/2 + .25)*np.cos(np.pi*z)


def classify_complex(z0, phase=0, max_steps=450, radius=1e-6, guard=32.0):
    require(phase in (0, 1, 2), "Invalid launch phase")
    starts = np.asarray(z0, dtype=np.complex128)
    values = starts.reshape(-1)
    indices = np.arange(values.size)
    result = np.zeros(values.size, dtype=np.uint8)
    times = np.full(values.size, max_steps, dtype=np.int32)
    centers = [{code: tuple(map(float, group)) for code, group in phase_groups.items()}
               for phase_groups in targets()]
    for tick in range(max_steps+1):
        current_phase = (phase+tick) % 3
        with np.errstate(over="ignore", invalid="ignore"):
            status = np.where(np.isfinite(values) & (np.abs(values) <= guard), 0, 3).astype(np.uint8)
            for code, group in centers[current_phase].items():
                for center in group:
                    status[(status == 0) & (np.abs(values-center) <= radius)] = code
        stopped = status != 0
        result[indices[stopped]] = status[stopped]
        times[indices[stopped]] = tick
        if tick == max_steps:
            break
        indices = indices[~stopped]
        if not indices.size:
            break
        with np.errstate(over="ignore", invalid="ignore"):
            values = C(values[~stopped])+WORD[current_phase]
    return result.reshape(starts.shape), times.reshape(starts.shape)


@lru_cache(maxsize=None)
def numerical_checks():
    import cmath
    rows = []
    for phase in range(3):
        centers = [(code, float(c)) for code, values in targets()[phase].items() for c in values]
        classes, times = classify_complex([c for _, c in centers], phase)
        require(classes.tolist() == [code for code, _ in centers] and not np.any(times),
                "Matching-phase centers are not classified at time zero")
        for initial in (.02+.01j, 1.001+.001j, 7.001+.002j, 3.12+.22j, .9952+.008j, .71+.02j):
            output, when = classify_complex(initial, phase)
            z = initial
            for tick in range(451):
                if not (np.isfinite(z) and abs(z) <= 32):
                    scalar = 3
                    break
                scalar = next((code for code, group in targets()[(phase+tick) % 3].items()
                               if any(abs(z-float(c)) <= 1e-6 for c in group)), 0)
                if scalar or tick == 450:
                    break
                z = z + .25 - (z/2+.25)*cmath.cos(cmath.pi*z) + WORD[(phase+tick) % 3]
            require((int(output), int(when)) == (scalar, tick), "Scalar and vectorized classifier mismatch")
            rows.append({"launch_phase": phase, "real": initial.real, "imaginary": initial.imag,
                         "class": scalar, "first_terminal_time": tick})
    sample = np.linspace(-.35, 7.3, 57) + 1j*np.linspace(0, .4, 13)[:, None]
    for phase in range(3):
        a, t = classify_complex(sample, phase)
        b, u = classify_complex(sample.conjugate(), phase)
        require(np.array_equal(a, b) and np.array_equal(t, u), "Complex-conjugation check failed")
    for entry in geometry()["phase_launches"]["launches"]:
        code, time = classify_complex(.71+.02j, entry["launch_phase"])
        require(int(code) == TARGET_CODES[entry["cycle_id"]] and
                int(time) == entry["first_target_disk_entry"], "Certified launch and sampled result disagree")
    return {"scalar_replays": rows, "conjugate_grid_shape": [13, 57], "conjugate_launch_phases": [0, 1, 2],
            "certified_marked_launches_match": True,
            "scope": "Numerical sanity checks, not interval certification of raster pixels."}


def raster(name, bounds, nx, ny, phase=0):
    xmin, xmax, ymin, ymax = bounds
    x = xmin+(np.arange(nx)+.5)*(xmax-xmin)/nx
    y = ymin+(np.arange(ny)+.5)*(ymax-ymin)/ny
    classes = np.empty((ny, nx), dtype=np.uint8)
    times = np.empty((ny, nx), dtype=np.int32)
    for start in range(0, ny, 32):
        points = x+1j*y[start:start+32, None]
        classes[start:start+len(points)], times[start:start+len(points)] = classify_complex(points, phase)
    return classes, {"array_name": name, "bounds": list(bounds), "shape": [ny, nx], "launch_phase": phase,
                     "grid": "Centers of uniform pixels; lower-left origin.",
                     "counts_by_code_0_through_6": np.bincount(classes.ravel(), minlength=7).tolist(),
                     "classes_sha256": digest(classes.tobytes()),
                     "terminal_times_sha256": digest(times.astype("<i4").tobytes()),
                     "minimum_terminal_time": int(times.min()), "maximum_terminal_time": int(times.max())}


def draw_raster(ax, classes, bounds):
    ax.imshow(classes, origin="lower", extent=bounds, interpolation="nearest", aspect="equal",
              cmap=ListedColormap(COLORS), norm=BoundaryNorm(np.arange(8)-.5, 7))
    ax.set_xlabel("Real part of the initial value")
    ax.set_ylabel("Imaginary part")
    ax.tick_params(length=3, pad=3)


def complex_basins():
    checks = numerical_checks()
    fig = plt.figure(figsize=(6.4, 4.75))
    axes = [fig.add_axes([.09, .66, .88, .20]),
            fig.add_axes([.09, .19, .385, .37]), fig.add_axes([.585, .19, .385, .37])]
    views = [("complex_overview", (-1.45, 7.55, -.60, .60), 1440, 192),
             ("complex_zero_zoom", (-.30, .30, -.222, .222), 540, 400),
             ("complex_one_zoom", (.9905, 1.0095, -.00703, .00703), 540, 400)]
    records = []
    for ax, (name, bounds, nx, ny), title in zip(axes, views,
            ("(a) Phase-zero numerical basin samples", "(b) Near 0", "(c) Near 1")):
        values, audit = raster(name, bounds, nx, ny)
        draw_raster(ax, values, bounds)
        panel(ax, title)
        records.append(audit)
    axes[0].set(xticks=range(-1, 8), yticks=[-.4, 0, .4])
    axes[1].set(xticks=[-.3, -.15, 0, .15, .3], yticks=[-.2, 0, .2])
    axes[2].set(xticks=[.992, 1, 1.008], yticks=[-.006, 0, .006])
    axes[2].ticklabel_format(axis="x", style="plain", useOffset=False)
    for code, group in targets()[0].items():
        for center in group:
            c = float(center)
            if -1.45 < c < 7.55:
                axes[0].plot(c, 0, marker="o" if code in (1, 4, 6) else "D", ms=3.1,
                             mfc=COLORS[code], mec="white", mew=.65)
    for ax, c, marker in ((axes[1], 0, "o"), (axes[2], 1, "D")):
        ax.plot(c, 0, marker=marker, ms=4, color=INK, mec="white", mew=.75)
    order = (1, 2, 6, 5, 4, 0, 3)
    fig.legend(handles=[Patch(facecolor=COLORS[code], label=TARGET_LABELS[code]) for code in order],
               loc="upper center", bbox_to_anchor=(.52, .99), ncol=4, frameon=False,
               fontsize=7.1, columnspacing=1.05, handlelength=1)
    fig.text(.09, .025, "Numerical disk entry: radius $10^{-6}$, 450 updates, guard $|z|>32$. "
             "Gray and dark pixels remain unresolved.", fontsize=7.6, color=MUTED)
    save(fig, "complex_basins", "Numerical complex basin samples for five certified targets")
    return {"model": "C(z)=z+1/4-(z/2+1/4)cos(pi*z), followed by prescribed impulse",
            "capture_radius": "1/1000000", "maximum_physical_updates": 450, "magnitude_guard": 32,
            "guard_precedes_target_test": True, "tests_include_time_zero_and_budget_endpoint": True,
            "codes": {str(code): label for code, label in TARGET_LABELS.items()}, "views": records,
            "checks": checks, "proof_scope": "Targets have exact certificates; the pixels are floating-point classifications only."}


def real_separator():
    record = geometry()["real_separator"]
    require(record["domain"] == ["0", "9/50"], "Unexpected separator interval")
    roots = record["nonzero_fixed_returns"]
    brackets = [tuple(Fraction(v) for v in row["bracket"]) for row in roots]
    require([row["kind"] for row in roots] == ["repeller", "attractor"] and
            brackets == [(Fraction(".16503724"), Fraction(".16503725")),
                         (Fraction(".17752760"), Fraction(".17752761"))],
            "Printed root brackets disagree with the certificate")
    derivative0 = list(map(Fraction, roots[0]["derivative_interval"]))
    derivative1 = list(map(Fraction, roots[1]["derivative_interval"]))
    require(Fraction("1.096") < derivative0[0] <= derivative0[1] < Fraction("1.097") and
            0 < derivative1[0] <= derivative1[1] < 1,
            "Printed derivative bounds disagree with the certificate")
    alpha, beta = [float(sum(interval)/2) for interval in brackets]
    def displacement(x):
        image = np.array(x, dtype=np.float64)
        for d in WORD:
            image = C(image)+d
        return image-x
    fig, axes = plt.subplots(1, 2, figsize=(6.4, 3.5))
    fig.subplots_adjust(left=.105, right=.975, top=.84, bottom=.34, wspace=.34)
    sample_records = []
    for ax, interval, title in zip(axes, [(0, .18), (.158, .18)],
                                   ["(a) Certified real interval", "(b) Two nearby fixed returns"]):
        x = np.linspace(*interval, 2001)
        y = displacement(x)
        ax.axvspan(interval[0], min(alpha, interval[1]), color=BLUE, alpha=.07)
        ax.axvspan(max(alpha, interval[0]), interval[1], color=GOLD, alpha=.09)
        ax.axhline(0, color=MUTED, lw=.65)
        ax.plot(x, y, color=INK, lw=1.15)
        for c, color, marker in ((0, BLUE, "o"), (alpha, PURPLE, "D"), (beta, GOLD, "o")):
            if interval[0] <= c <= interval[1]:
                ax.scatter(c, 0, s=29, marker=marker, facecolor="white" if c == alpha else color,
                           edgecolor=color, linewidth=1.1, zorder=4)
        ax.set_xlim(interval)
        ax.set_xlabel("Real initial value $x$ at phase zero")
        ax.set_ylabel("Smooth return displacement $R(x)-x$")
        ax.ticklabel_format(axis="y", style="sci", scilimits=(-3, -3), useMathText=True)
        panel(ax, title)
        sample_records.append({"x_interval": list(interval), "samples": len(x),
                               "x_sha256": digest(x.astype("<f8").tobytes()),
                               "displacement_sha256": digest(y.astype("<f8").tobytes())})
    axes[0].set_xticks([0, .06, .12, .18])
    axes[1].set_xticks([.16, .165, .17, .175, .18])
    axes[1].annotate("repeller $a$", (alpha, 0), xytext=(-24, -32),
                     textcoords="offset points", fontsize=7.7, color=PURPLE,
                     arrowprops={"arrowstyle": "-", "color": PURPLE, "lw": .6})
    axes[1].annotate("attractor $b$", (beta, 0), xytext=(-35, 24),
                     textcoords="offset points", fontsize=7.7, color="#8b6200",
                     arrowprops={"arrowstyle": "-", "color": GOLD, "lw": .6})
    fig.text(.105, .16, "$a\\in[0.16503724,\\,0.16503725]$,  $1.096<R'(a)<1.097$",
             fontsize=8.2, color=PURPLE)
    fig.text(.105, .095, "$b\\in[0.17752760,\\,0.17752761]$,  $0<R'(b)<1$",
             fontsize=8.2, color="#8b6200")
    fig.text(.105, .035, "Curve: floating-point samples. Brackets and derivative inequalities: exact rational certificates.",
             fontsize=7.6, color=MUTED)
    save(fig, "real_separator", "A certified repelling separator for the smooth real return map")
    return {"return_symbol": "R", "certified_domain": record["domain"], "root_records": roots,
            "plotted_root_locations": "Midpoints of the certified brackets; not claimed as exact roots.",
            "sampled_curves": sample_records,
            "shading": "Blue side converges to the integer fixed return; gold side to the nearby noninteger fixed return, by the separate exact interval argument."}


def phase_sheets():
    certificate = geometry()["phase_launches"]
    initial = complex(float(Fraction(certificate["source_real"])), float(Fraction(certificate["source_imaginary"])))
    require(initial == .71+.02j, "Marked phase-launch value changed")
    fig, axes = plt.subplots(3, 1, figsize=(6.4, 4.75))
    fig.subplots_adjust(left=.11, right=.97, top=.88, bottom=.14, hspace=.49)
    views = []
    bounds = (-.1, 3.1, -.3, .3)
    for phase, ax in enumerate(axes):
        values, audit = raster(f"phase_sheet_{phase}", bounds, 800, 150, phase)
        draw_raster(ax, values, bounds)
        ax.set(xticks=[0, 1, 2, 3], yticks=[-.2, 0, .2])
        entry = certificate["launches"][phase]
        expected = TARGET_CODES[entry["cycle_id"]]
        actual, time = classify_complex(initial, phase)
        require(int(actual) == expected and int(time) == entry["first_target_disk_entry"], "Phase launch mismatch")
        label = "3-cycle" if expected == 1 else "9-cycle"
        panel(ax, f"Phase {phase}, next impulse {['+1','0','-1'][phase]}:  {label}, certified first entry at update {int(time)}")
        ax.plot(initial.real, initial.imag, marker="D", ms=4.7, mfc=INK, mec="white", mew=.75, zorder=6)
        ax.text(initial.real+.06, initial.imag-.12, "$z_*$", fontsize=9.2, color="white",
                bbox={"facecolor": INK, "alpha": .8, "edgecolor": "none", "pad": 1}, zorder=7)
        if phase < 2:
            ax.set_xlabel("")
        views.append(audit)
    trajectory = certificate["launches"][0]["trajectory_balls"][:3]
    points = [(float(Fraction(ball["real"])), float(Fraction(ball["imaginary"]))) for ball in trajectory]
    for phase in (1, 2):
        axes[phase].plot(*points[phase], marker="o", ms=4.6, mfc="white", mec=INK, mew=.8, zorder=8)
        axes[phase].annotate(f"step {phase} from phase 0", points[phase],
                             xytext=(8, -16 if phase == 2 else 8), textcoords="offset points",
                             fontsize=7.1, color=INK, bbox={"facecolor": "white", "edgecolor": "none", "alpha": .9, "pad": 1})
    fig.text(.11, .955, "The same complex number on three forcing sheets:  $z_*=71/100+i/50$",
             fontsize=9.4, weight="semibold")
    fig.text(.11, .025, "Diamonds: certified launches. Background: numerical samples "
             "(450 updates, guard $|z|>32$).", fontsize=7.3, color=MUTED)
    save(fig, "phase_sheets", "One certified complex point launched at three different phases")
    return {"source_real": certificate["source_real"], "source_imaginary": certificate["source_imaginary"],
            "launches": [{k: entry[k] for k in ("launch_phase", "cycle_id", "first_target_disk_entry", "target_phase", "target_center", "final_error")}
                         for entry in certificate["launches"]],
            "phase_zero_first_three_balls": trajectory, "views": views,
            "proof_scope": "The three marked launches are certified; the surrounding numerical pixels are not."}


FIGURES = {"phase_cycles": phase_cycles, "integer_return": integer_return, "binary_basins": binary_basins,
           "complex_basins": complex_basins, "real_separator": real_separator, "phase_sheets": phase_sheets,
           "seven_step_merger": seven_step_merger, "synchronization": synchronization}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("names", nargs="*", metavar="FIGURE", help="Omit to render all eight figures")
    args = parser.parse_args()
    if set(args.names)-set(FIGURES):
        parser.error("Unknown figure; choose from "+", ".join(FIGURES))
    names = args.names or list(FIGURES)
    OUT.mkdir(parents=True, exist_ok=True)
    previous = OUT / "figure_inputs.json"
    results = json.loads(previous.read_text())["figures"] if previous.exists() else {}
    for name in names:
        print(f"Rendering {name}", flush=True)
        results[name] = FIGURES[name]()
        results[name]["pdf_sha256"] = digest((OUT / (name+".pdf")).read_bytes())
    dependencies = ["certificates/geometry/certificate.json", "certificates/exposition/examples.json"]
    report = {"schema_version": 1, "renderer": "scripts/render_figures.py",
              "software": {"python": platform.python_version(), "numpy": np.__version__, "matplotlib": matplotlib.__version__},
              "certificate_inputs": [{"path": path, "sha256": digest((ROOT/path).read_bytes())} for path in dependencies],
              "figures": results,
              "scope": "Rendering is optional and separate from proof verification. Floating-point basin pixels are explicitly numerical."}
    previous.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"status": "rendered", "figures": names, "inputs": str(previous.relative_to(ROOT))}))


if __name__ == "__main__":
    main()
