# Reproducible mathematical figures

The eight PDFs are laid out for a width of **6.4 inches** and embed their
fonts. All line diagrams, integer dots, tables, and binary tiles are vector
graphics. Only the complex basin backgrounds in `complex_basins.pdf` and
`phase_sheets.pdf` contain raster images.

## Rebuild

From the release root, install NumPy and Matplotlib in your chosen Python
environment and run:

```sh
python3 -m pip install -r requirements-figures.txt
python3 scripts/render_figures.py
```

Individual figures can be selected by their names without the extension:

```sh
python3 scripts/render_figures.py phase_cycles integer_return
python3 scripts/render_figures.py complex_basins phase_sheets
```

The tested rendering environment is Python 3.12.14, NumPy 2.3.5, and
Matplotlib 3.10.8. These are optional rendering dependencies. The proof
verification commands do not import the renderer or require these packages.
The PDFs are already included for ordinary reading and manuscript builds.

The renderer reads only the bundled geometry and exposition certificate JSON
files. It does not import the research source tree. Its integer calculations
use exact arithmetic and check the examples independently against those
inputs. Its numerical basin calculations are deterministic for the recorded
software environment. PDF creation and modification dates are suppressed.

## Figure map

| PDF | Mathematical purpose |
| --- | --- |
| `phase_cycles.pdf` | Phase-augmented geometry of the exact 3- and 9-update integer cycles. |
| `integer_return.pdf` | Eight exact affine residue branches and two return-map orbits. |
| `binary_basins.pdf` | Exact integer basin samples in successively fixed low-bit residue classes. |
| `complex_basins.pdf` | Numerical basin samples for five separately certified analytic targets. |
| `real_separator.pdf` | Sampled real return displacement with exact root brackets and stability bounds. |
| `phase_sheets.pdf` | Three certified launches of the same complex number, with numerical backgrounds. |
| `seven_step_merger.pdf` | A whole-family, same-phase merger under the original seven-step section rank. |
| `synchronization.pdf` | One common word merging a finite ensemble, including its limited phase scope. |

## Evidence and limitations

`figure_inputs.json` records the certificate digests, exact displayed integer
data, arithmetic checks, numerical grid domains, class counts, and raster
digests. No large pixel cache is required or shipped. Every raster is
regenerated from its recorded grid and formula.

The binary atlas uses exact integer trajectories. The finite atlas alone does
not prove an asymptotic basin density or the absence of other integer cycles.
The cylinder's arcs and the integer cobweb's segments encode discrete updates;
their interiors are not additional orbit states.

The complex atlas uses the specific cosine continuation, 450 physical
updates, a disk-entry radius of `1e-6`, and the magnitude guard `|z| > 32`.
The guard and step-budget outcomes remain distinct unresolved classes.
The five target traps have exact certificates, but general pixel trajectories
are floating-point computations. The figures do not establish global basin
boundaries, divergence of guarded points, or completeness of the target list.
Only the three marked launches in `phase_sheets.pdf` carry the separate exact
orbit-enclosure certificates.
