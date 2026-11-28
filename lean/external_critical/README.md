# Critical-space support

Twelve exact supporting theorems for the compact rooted-law argument, with local mathematical definitions and public pinned dependencies. See [the model and derivations](ARGUMENT.md). This release candidate has not yet passed its independent assurance gates. Full M4/R8/R9 and the critical Gibbs-law argument remain incomplete.

The physical phase is `AddCircle 1`; heights use the genuine `OnePoint Nat` topology. The finite law samples Haar phase before normalized quenched Gibbs paths and a uniform root. Infinite-height mass and the phase seam remain explicit.

The results cover topology, representative/shift/roof laws, weak roof passage, finite normalization, the2B/n shift error, stationary subsequences, conditional finite/infinite sector separation, weighted gap packing, excursion first moments and a conditional polynomial-tail contradiction.

After preparing the exact public dependencies in `lake-manifest.json`:

```
python3 lean/external_critical/verify.py --mode build --report /tmp/critical-build.json
python3 lean/external_critical/verify.py --mode full --report /tmp/critical-full.json
python3 lean/external_critical/test_mutations.py --mode full --report /tmp/critical-controls.json
```

Use the official Lean4.35.0 Linux archive (SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`) with its `bin` directory on PATH. It supplies `nanoda_bin`, Lean default/paranoid, lean4lean, con-leche and con-ron. Install `bubblewrap` for the Linux sandbox. The mandatory CI job performs this setup and fetches the exact public lockfile dependencies before verification.

Full mode requires Linux sandbox support and every configured checker. Missing required checks fail. Build mode reports lower assurance. Generated complete proof exports belong in temporary builds, not Git; compact complete reports, hashes, logs and fixtures must be retained.

The specification pins mathematical meanings fixed before implementation. Public aliases change no body; historical `Draft` names/comments remain provenance. The inventory covers every owned module/declaration, target/model row and source/configuration/document byte.

Jake S. Brusca; ChatGPT-assisted personal research draft. AI roles overlap. No human expert refereeing, priority certification, source-author endorsement or Collatz capture claim is made.
