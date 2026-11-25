# IUTLean

A Lean 4 project on Shinichi Mochizuki's *Inter-universal Teichmüller Theory* I to IV.

The project catalogs every numbered statement of the four papers, states in Lean what can be
stated without inventing definitions, and proves what it can with the kernel as the only
judge. Its central target is IUT III, Corollary 3.12, the inequality on which the derivation
of the abc conjecture in IUT IV rests. Every result is reported with its exact hypotheses, and
every step that cannot yet be stated or proved is recorded as an open obligation with its
source page.

The project takes no side in the dispute about the theory. It neither assumes that the theory
is correct nor that it is wrong. A countermodel in this repository refutes a simplified
abstraction stated in Lean; none refutes a statement of the papers. The website is
<https://adamrsophie.github.io/IUTLean/>.

## Status

* **The abc conjecture is not proved here.** `Challenge/Defs.lean` defines it (`Challenge.ABC`)
  and two equivalent forms; the library proves only that the three forms are equivalent.
* **IUT III, Corollary 3.12 is not formalized.** Its two log-volumes, `−|log(Θ)|` and
  `−|log(q)|`, are not constructed from initial Θ-data, because Hodge theaters, the
  log-theta-lattice, tensor packets and the multiradial representation are not formalized.
  Theorem 3.11 is not stated in Lean either. `docs/COR312_ANALYSIS.md` lists what is missing,
  step by step.
* **No claim is made about whether the theory is correct.**

**Stopping point.** The work so far stops at a point that does not depend on which revision of
the papers is used: nothing in the library constructs the objects of IUT I to III. Not done:
Hodge theaters, prime strips, the Θ-link and the log-link, the log-theta-lattice, log-shells
and tensor packets with their normalized log-volumes, the indeterminacies (Ind1) to (Ind3),
the holomorphic hull of possible images, a Lean statement of Theorem 3.11 or Corollary 3.12,
the comparison of Corollary 3.12 stated on the papers' objects (only an abstract interface with
the regions as inputs exists, `IUT/PaperIII/Corollary312/Comparison.lean`), and the specialization of IUT IV
Theorem A to abc triples. What is done is arithmetic and order-theoretic: numerical
consequences of stated inequalities, elementary estimates of IUT IV, countermodels to
simplified abstractions, and models of the arguments in the published discussion. The next
stage is in `docs/ROADMAP.md`.

**Verified scope.** A statement of the papers is counted as formalized or verified only when a
Lean declaration states the whole statement, with the same objects, hypotheses and conclusion.
A Lean lemma that checks one arithmetic or elementary step of a statement is a *fragment*: it
has its own record (`<statement id>.frag.<name>` in `data/curated/`), it is counted separately
from full statements, and it gives the parent statement no formalized or verified status. Kernel
acceptance establishes that a Lean declaration is proved as written; whether it says what the
paper says is a separate, human comparison against the cited pages (see
`docs/VERIFICATION_REPORT.md`).

What is checked in Lean today, by area:

| Area | Main results | Modules |
|---|---|---|
| abc statements | `abc_iff_abcFinite`, `abc_iff_abcLog`, `rad_eq_radical`, `coprime_iff_pairwise`; equivalence with the Formal Conjectures statement (`abc_iff_ABC`) | `IUT/Applications/` |
| IUT IV, §1 and §2 | the local estimates of Propositions 1.2 to 1.7 and 2.1; the arithmetic of Theorem 1.10 (`final_inequality`) and of Corollaries 2.2 and 2.3, conditional on the inequality of Corollary 3.12 where the paper uses it | `IUT/PaperIV/` |
| IUT III, Corollary 3.12 | the numerical layer only: the reduction at the start of the proof (`inequality_of_nonneg`) and the fact that the last inclusion of Step (xi-f) is the conclusion restated (`stepXIf_inclusion_iff_inequality`) | `IUT/PaperIII/Corollary312/Numerical.lean` |
| IUT III, Remark 3.9.5 | the hull operator from properties (P1) to (P3) | `IUT/PaperIII/Remark3_9_5/HullOperator.lean` |
| IUT III, Corollary 3.12, last step | an abstract interface: the comparison as a region containment and as a log-volume inequality on given regions, the conditional passage to the numerical layer, and examples; not the papers' objects | `IUT/PaperIII/Corollary312/Comparison.lean` |
| IUT I and II | poly-morphisms and capsules of IUT I §0; partial conditions of initial Θ-data (`PartialInitialThetaConditions`); the label arithmetic of IUT II | `IUT/PaperI/`, `IUT/PaperII/` |
| Prerequisites | product formula, `ℚ_{>0} ∩ Ẑ^× = {1}`, Grothendieck universes on `ZFSet` (the two existence results assume `ExistenceAxiom`, which is independent of what Lean proves about `ZFSet` and fails in some models, where they are vacuous) | `IUT/Prerequisites/`, `IUT/Foundations/` |
| The published discussion | the reduction and averaging arguments of Scholze and Stix; models from Mochizuki's responses | `IUT/Audit/` |
| Countermodels | simplified abstractions of steps of Corollary 3.12 that fail without an extra hypothesis | `IUT/Countermodels/` |

Statements that are cataloged but not formalized: the constructions of IUT I and II (prime
strips, Hodge theaters, Θ-links), the log-shells and log-volumes of IUT III, Theorem 3.11,
Corollary 3.12 itself, and the passage from Theorem A of IUT IV to `Challenge.ABCLog`.

All counts (statements extracted, full statements formalized, full statements verified
unconditionally or conditionally, fragments, obligations, ambiguities) are in
[docs/DASHBOARD.md](docs/DASHBOARD.md); the formalized and verified counts refer to full
statements only, and fragments are counted separately. They are generated by
`scripts/dashboard.py` from `data/`; this README quotes none, so that it cannot fall out of
date.

## Where to start reading

* [docs/COR312_ANALYSIS.md](docs/COR312_ANALYSIS.md): what Corollary 3.12 asserts, what each
  step of its proof needs, and which candidate conditions would close each gap.
* [docs/CRITICAL_PATH.md](docs/CRITICAL_PATH.md): the statements on which Corollary 3.12 and
  abc depend (generated).
* [docs/DASHBOARD.md](docs/DASHBOARD.md): progress by statement and status (generated).
* [OPEN_PROBLEMS.md](OPEN_PROBLEMS.md): every unresolved obligation, with its source page.
* [docs/VERIFICATION_REPORT.md](docs/VERIFICATION_REPORT.md): what each check establishes and
  what is trusted.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The toolchain is Lean 4.36.0 (`lean-toolchain`). Mathlib is pinned to tag v4.36.0, commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (`lakefile.toml`). `lake build` builds the default
targets, the libraries `IUT` and `Solution`.

The trust checks, in the order CI runs them (`.github/workflows/axiom-gate.yml`):

```sh
python3 -I scripts/Controls/source_scan.py          # constructs the gate cannot see
python3 -I scripts/gen_root.py --check              # IUT.lean imports every library file
lake build
python3 -I scripts/Controls/fingerprints.py --check # trusted definitions, challenge statements, trust files
git ls-files -- IUT.lean IUT > tracked-files.txt
AXIOM_GATE_TRACKED_FILES=tracked-files.txt lake env lean AxiomGate.lean
AXIOM_GATE_TRACKED_FILES=tracked-files.txt sh GateControls/run.sh AxiomGate.lean
lake comparator                                     # Linux only
lake check                                          # Linux only
```

`lake comparator` checks that every theorem listed in `comparator.json` has in `Solution` the
statement given in `Challenge`, uses only the permitted axioms, and is accepted by the kernel.
It and `lake check` run inside the bubblewrap sandbox, so they need Linux with unprivileged
user namespaces (CI uses Ubuntu 24.04). `docs/VERIFICATION_REPORT.md` says what each check
establishes and what it does not.

## Layout

| Path | Content |
| --- | --- |
| `IUT/` | The library, one directory per area: `Applications`, `Audit`, `Countermodels`, `Foundations`, `PaperI` to `PaperIV`, `Prerequisites`, and `Experimental` (drafts, never imported). |
| `IUT.lean` | Root module; imports every library file outside `IUT/Experimental/`. Generated by `scripts/gen_root.py`. |
| `Challenge/Defs.lean` | The trusted definitions: `rad` and the three forms of the abc conjecture. Mathlib only, reviewed by hand, fingerprinted. |
| `Challenge.lean` | The headline theorems, stated with `sorry` on purpose, for `lake comparator`. Not a default target. |
| `Solution.lean` | The same theorems under the same names, proved from the library. |
| `comparator.json` | The challenge and solution modules and the list of theorems that `lake comparator` checks. |
| `AxiomGate.lean` | The check over every constant of the library: axioms, `unsafe`, `partial` and `opaque` declarations, conjecture statements, coverage of the source files, experimental modules. |
| `GateControls/` | Files that the gate and the source scan must accept or reject, each for a stated reason. Run by `GateControls/run.sh`. |
| `scripts/` | The untrusted helpers: the source scan, the fingerprint check, the root file generator, and the catalog pipeline. See `scripts/README.md`. |
| `data/` | The statement catalog and its derived data. `data/curated/` holds the records written by reading the papers; the other files are generated or curated as stated in each. |
| `docs/` | Analyses, generated reports and the notation dictionaries. |
| `.github/workflows/` | CI: the trust checks on every push and pull request to `main`. |
| `README.md`, `CONTRIBUTING.md`, `OPEN_PROBLEMS.md` | This file, the contribution rules, the open obligations. |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Build configuration and pins. |
| `LICENSE` | GNU General Public License, version 3. |

## Sources

The four papers appeared in *Publications of the Research Institute for Mathematical
Sciences*, volume 57 (2021), issue 1:

* *Inter-universal Teichmüller Theory I*, pages 3 to 207, doi:[10.4171/PRIMS/57-1-1](https://doi.org/10.4171/PRIMS/57-1-1).
* *Inter-universal Teichmüller Theory II*, pages 209 to 401, doi:[10.4171/PRIMS/57-1-2](https://doi.org/10.4171/PRIMS/57-1-2).
* *Inter-universal Teichmüller Theory III*, pages 403 to 626, doi:[10.4171/PRIMS/57-1-3](https://doi.org/10.4171/PRIMS/57-1-3).
* *Inter-universal Teichmüller Theory IV*, pages 627 to 723, doi:[10.4171/PRIMS/57-1-4](https://doi.org/10.4171/PRIMS/57-1-4).

Page numbers in this repository refer to the author's manuscripts, not to the journal pages.
The versions in hand, recorded in `data/source_manifest.json` and `docs/SOURCE_MANIFEST.md`:

* IUT I: manuscript dated May 2020, 186 pages, SHA-256 `7360e3ed27c235b5497a0743d3ed1646fbb97688547d16b7c784fc7f127f1f03`.
* IUT II: manuscript dated December 2020, 174 pages, SHA-256 `180bfa6aaddc4ae37af37acaad51f61e0a47b33b8255ad3169e28a970ae39b7c`.
* IUT III: manuscript dated May 2020, 199 pages, SHA-256 `9a7ee3c77b1c7717210c0613eb39b6844649d0040dc3d9e1be7d544f8f91a0b9`.
* IUT IV: manuscript dated April 2020, 87 pages, SHA-256 `5bf4b1e0a8c2686562a6859e5009d301335044cfb5efec5d3a9edf764e4af87f`.

The PDFs are not redistributed here; obtain them from the publisher or the author's web page.

## License

GNU General Public License, version 3. See `LICENSE`.
