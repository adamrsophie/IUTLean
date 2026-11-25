# IUT/Experimental

Scaffold modules: drafts of statements or proofs that are not finished.

The rules:

* Placeholders (`sorry`, `admit`) are allowed in this folder and, apart from the challenge
  file `Challenge.lean`, nowhere else. Every other construct that the source scan rejects in
  the library is rejected here too.
* No module outside this folder may import a module `IUT.Experimental` or
  `IUT.Experimental.*`. The root `IUT.lean` never lists these files
  (`scripts/gen_root.py` skips this folder).
* Three checks enforce the separation: the source scan `scripts/Controls/source_scan.py`
  rejects such an import and any placeholder outside this folder; the axiom gate
  `AxiomGate.lean` fails when an experimental module is in the import closure of the library;
  and the gate rejects every constant of the library that depends on `sorryAx`.
* Nothing in this folder counts as verified. A result moves into the library only when it is
  complete, and then under the library's rules.
