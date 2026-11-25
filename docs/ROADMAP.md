# Roadmap

A staged plan, with IUT III Corollary 3.12 first. Each stage has entry and exit criteria that
can be checked in the repository. A stage may end with a precise obstruction instead of a
proof; that counts as an exit when the obstruction is stated in Lean or recorded in
`OPEN_PROBLEMS.md` with its category.

## Stage 0: infrastructure (done)

* Exit: the trust checks of `docs/VERIFICATION_REPORT.md` pass in CI; `Challenge/Defs.lean`
  is fingerprinted; the catalog pipeline regenerates `docs/DASHBOARD.md` with no record
  claiming a verified status that fails the checks.

## Stage 1: the numerical layer and IUT IV (done in part)

* Entry: stage 0.
* Work: the arithmetic of IUT IV §1 and §2 conditional on Corollary 3.12, and the numerical
  layer of Corollary 3.12 itself.
* Exit: every step of Theorem 1.10 and Corollaries 2.2 and 2.3 has a Lean declaration named
  by its record in `data/curated/iut4.json`, with status `KERNEL_VERIFIED` or
  `CONDITIONALLY_VERIFIED` and the hypothesis listed; the passage from Theorem A to
  `Challenge.ABCLog` is either proved or recorded with the missing definitions (heights,
  log-differents, log-conductors).

## Stage 2: the vocabulary of Corollary 3.12

* Entry: stage 1; the ambiguities A1 (averaging index) and A2 (normalization) of
  `OPEN_PROBLEMS.md` have a recorded reading, with the reason.
* Work, in order: the `p`-adic logarithm properties needed for log-shells (P-LOG); log-shells
  and their mono-analytic versions; tensor packets and their procession-normalized log-volumes
  (IUT III Proposition 3.9); the holomorphic hull on packets (extending
  `IUT/PaperIII/Remark3_9_5/HullOperator.lean`).
* Exit: Lean definitions of these objects with no field that assumes a conclusion of the
  papers, each module citing its pages; Proposition 3.9 (i) and (iii) stated and proved or
  recorded as blocked with a category.

## Stage 3: the indeterminacies and the two log-volumes

* Entry: stage 2.
* Work: definitions of (Ind1), (Ind2), (Ind3) (obligations OB-IND, A3 to A6); a definition of
  the set of possible images; definitions of `−|log(Θ)|` and `−|log(q)|` (OB-DEF).
* Exit: `PilotLogVolumes` of `Numerical.lean` is instantiated from these definitions, not
  given as data; condition C4 (common normalization) proved or refuted.

## Stage 4: from Theorem 3.11 to Corollary 3.12

* Entry: stage 3.
* Work: a faithful statement of Theorem 3.11 (G-311, OB-311-HYP); then C1, C2, C3, C7, and
  the condition of Step (xi-f) in one of its readings C5, C5' or C5 with C8.
* Exit: one of three outcomes, each checkable in Lean:
  1. Corollary 3.12 proved from Theorem 3.11 and the named conditions, all proved;
  2. Corollary 3.12 proved conditionally, with each unproved condition a named hypothesis
     that is not a restatement of the conclusion (C6 is excluded);
  3. a countermodel to a faithfully formalized intermediate statement, with the statement
     traced to its pages.

## Stage 5: IUT I and II as needed by stage 4

* Entry: stage 4 has identified which constructions of IUT I and II its definitions need.
* Work: prime strips, Hodge theaters and Θ-links, only as far as stage 4 requires, starting
  with poly-morphisms and capsules (IUT I §0).
* Exit: the statements of IUT I and II on the critical path of `docs/CRITICAL_PATH.md` that
  stage 4 uses have status `STATEMENT_FORMALIZED` or a blocking status with a reason.

## Stage 6: review

* Entry: any stage exit.
* Work: a reading of every new Lean statement against the rendered pages by someone other than
  its author; a recheck of `OPEN_PROBLEMS.md` categories.
* Exit: the statement status of reviewed records is `STATEMENT_REVIEWED`.

Progress against these stages is measured in `docs/DASHBOARD.md`.
