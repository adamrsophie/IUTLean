# Countermodels and falsification program

**None of the results in this document refutes a statement of the IUT papers.** Every countermodel below refutes a *simplified abstraction*: a general principle that an argument could be tempted to use and that is false without further hypotheses. Each is fully proved in Lean (no `sorry`; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`). Next to each countermodel a positive statement of the same flavor is proved, so that legitimate identifications are not ruled out by accident.

Machine-readable index: `data/countermodels.json` (one record per listed theorem, 37 records; helper definitions are omitted).

## Classification

The project distinguishes seven kinds of result: failure of proof search, missing library theorem, gap in the formalization, insufficient set of hypotheses, counterexample to a simplified abstraction (in some project documents called a counterexample to an intermediate claim), counterexample to the faithfully formalized original statement, demonstrated contradiction.

Every countermodel here is a **counterexample to a simplified abstraction**: it shows that the hypotheses of an abstract principle are insufficient for its conclusion. None is a counterexample to an intermediate claim of the papers, to a faithfully formalized statement of the papers, or a demonstrated contradiction: the abstractions are not statements found in the passages read, and the hypotheses of the papers are much richer than those the models satisfy.

To the question "do the hypotheses the countermodel satisfies correspond to the full hypotheses of an original claim?" the answer is **no** for every entry.

## Sources read

Mochizuki, *Inter-universal Teichmüller Theory III* (May 2020 manuscript), from the extracted text:

* Definition 1.1, Remarks 1.1.1, 1.1.2 and Proposition 1.2: pages 26 to 35.
* Proposition 3.9 and the start of Remark 3.9.1: pages 115 to 118. Page 115 was also read from the rendered page; it is the only page whose formulas are paraphrased here (the packet normalization: the integral structure has log-volume zero, and multiplying by `p_v` adds `−log(p_v)`).
* Theorem 3.11 (i), (ii), (iii) (a) to (c): pages 153 to 157.
* Corollary 3.12, its proof, and Remark 3.12.1 (i), (ii): pages 173 to 186.

Remarks 3.9.5 and 3.11.1 were not read. The holomorphic hull and the properties (IPL), (SHE), (APT) are referred to only through the passages of pages 173, 174 and 181 to 184 that mention them.

## The seven priority questions

### 1. Does multiplicative data determine additive structure?

File `IUT/Countermodels/MultiplicativeAdditive.lean`, namespace `IUT.Countermodels.MulAdd`; and `Basic.lean`.

| Lean name | Kind | Statement |
|---|---|---|
| `IUT.Countermodels.mul_iso_not_additive` | countermodel | Cubing on `ZMod 5` preserves `0`, `1`, multiplication, and is bijective, but is not additive. |
| `padic_inv_countermodel` | countermodel | On `ℚ_p`, inversion is a multiplicative bijection fixing `0` and `1`, commuting with every field automorphism, continuous on `ℚ_p^×`, mapping units to units, not norm preserving, and induced by no ring map. |
| `squareValue_countermodel` | countermodel | On `ℚ_p`, `x ↦ x · p^{v(x)}` is multiplicative, injective, the identity on units, doubles valuations, and is not additive. |
| `padicInt_units_inv_not_ringHom` | countermodel | Inversion, a group automorphism of `ℤ_p^×`, agrees on units with no ring endomorphism of `ℤ_p`. |
| `real_cube_countermodel` | countermodel | Cubing on `ℝ` is strictly increasing, continuous, bijective and multiplicative, and is induced by no ring map. |
| `inv_comm_ringEquiv` | positive | Inversion commutes with every ring automorphism of any field. |
| `inv_not_ringHom` | lemma | If `2 ≠ 0` and `3 ≠ 0`, no ring endomorphism agrees with inversion on nonzero elements. |
| `additive_of_mul_of_translate` | positive | On any field, a multiplicative map with `f 0 = 0` and `f (x + 1) = f x + 1` is additive. |

*Abstraction refuted:* a bijection respecting the multiplicative monoid of a field, together with one of: its topology, its order, its unit group, the action of its field automorphisms, respects addition. *What rules the countermodels out:* compatibility with the single translation `x ↦ x + 1` (positive statement). A Galois action in the weak sense of equivariance under field automorphisms does not, because power maps and inversion commute with every ring map.

*Bears on:* IUT III, Step (i) of the proof of Corollary 3.12 (page 175), where the Θ×μ_LGP-link is a poly-isomorphism with a unit portion and a value group portion; Remark 1.1.1 (i) (page 28), log-shells are built from units only; Step (ix) (page 180), the ring structure of `F_mod` as a translation apparatus between multiplicative and additive structures. `squareValue_countermodel` is shaped like "identity on units, homomorphism on the value group" and is not additive; it is a map on a field, not a model of the Θ×μ_LGP-link, which relates Frobenioid-theoretic prime-strips. Nothing here concerns reconstruction from the absolute Galois group, which the papers use.

*Not attempted:* power maps `u ↦ u^k` on `ℤ_p^×`.

### 2. Does an isomorphism at one structural level preserve invariants at another?

File `IUT/Countermodels/LevelMismatch.lean`, namespace `IUT.Countermodels.Level`.

| Lean name | Kind | Statement |
|---|---|---|
| `mulP_countermodel` | countermodel | Multiplication by `p` is an automorphism of the additive topological group `ℚ_p` that multiplies every norm by `p⁻¹` and sends `1` into the maximal ideal. |
| `no_ringEquiv_valuation_two_three` | countermodel | No ring automorphism of `ℚ` carries `v₃` to `v₂`, although the fields are equal and both value groups are `ℤ`. |
| `conj_unbounded` | countermodel | Conjugation on `ℤ[√2]` is an involutive ring automorphism that is unbounded on the elements whose real embedding has absolute value at most `1`. |
| `real_ringEquiv_isometry` | positive | Every ring automorphism of `ℝ` preserves the absolute value. |

*Abstraction refuted:* an isomorphism of an additive group, or of a field, preserves an invariant defined with further structure (norm, valuation, integral structure, archimedean absolute value). *Hypotheses satisfied:* additive automorphism, continuous both ways (`mulP`); isomorphic fields and isomorphic value groups (valuations); ring automorphism with a fixed real embedding (`ℤ[√2]`). `conj_unbounded` is stated as unboundedness; discontinuity in the induced topology is not formalized.

*Bears on (by analogy):* Step (xii) of the proof of Corollary 3.12 (pages 185 and 186), where an isomorphism preserving only isomorphism classes of local Frobenioid objects cannot tell an open submodule from its `p^N` multiple; Proposition 1.2 (iii) (page 31) and Theorem 3.11 (ii) (a) (page 155), where compatibility with log-volumes is asserted as a separate property of specific maps.

### 3. Does canonical reconstruction imply preservation of a chosen normalization?

File `IUT/Countermodels/HaarNormalization.lean`, namespace `IUT.Countermodels.Haar`; and `Basic.lean`.

| Lean name | Kind | Statement |
|---|---|---|
| `IUT.Countermodels.additive_iso_changes_volume` | countermodel | Doubling is additive on `ℝ`, and `[2 · 0, 2 · 1]` has Lebesgue measure different from `[0, 1]`. (Doubling is an automorphism of the topological group `ℝ`; the theorem states only additivity.) |
| `IUT.Countermodels.log_volume_shift` | positive | `log (c μ) = log c + log μ` for `c, μ > 0`: the arithmetic of the shift of the log-volume of a set of finite positive measure. |
| `rescaled_haar` | countermodel | For `c > 0`, `c · volume` is an additive Haar measure, differs from `volume` if `c ≠ 1`, and shifts by `log c` the log-volume of every set `s` with `0 < volume s < ∞`. (For `s = ∅` and `c = 2` both log-volumes are `0`, by the totalization of `logVol`.) |
| `scaling_law_all_normalizations` | countermodel | For `c > 0`, `a ≠ 0` and `0 < volume s < ∞`, the measure `c · volume` satisfies `logVol (a • s) = log (abs a) + logVol s`. |
| `transport_shifts_logVol` | countermodel | For `a ≠ 0`, transport of Lebesgue measure along `x ↦ a x` shifts by `−log (abs a)` the log-volume of every set `s` with `0 < volume s < ∞`. |
| `haar_eq_smul_volume` | positive | Every additive Haar measure on `ℝ` is a scalar multiple of Lebesgue measure. |
| `haar_eq_volume_of_anchor` | positive | An additive Haar measure giving `[0, 1]` volume `1` is Lebesgue measure. |
| `transport_preserves_iff` | positive | For `a ≠ 0`, transport along `x ↦ a x` preserves Lebesgue measure iff `abs a = 1`. |

*Abstraction refuted:* if an object (here the locally compact group `ℝ`, standing in for a local field) is reconstructed up to isomorphism, a normalized volume on it is reconstructed too. Haar measure is unique only up to one scalar; the scalar is fixed neither by the group structure nor by the scaling law, only by an anchor.

*Bears on:* Proposition 3.9 (i) (page 115, read from the render), which imposes both a scaling law ("multiplying by `p_v` adds `−log(p_v)`") and an anchor (the integral structure has log-volume `0`). `scaling_law_all_normalizations` shows that the first alone does not fix the normalization; `haar_eq_volume_of_anchor` shows that the second does. Also Proposition 3.9 (ii) (page 116) and Theorem 3.11 (ii) (a) (page 155), where compatibility of log-volumes with the relevant isomorphisms is asserted.

### 4. Do independent existential witnesses admit a common realization?

File `IUT/Countermodels/JointWitness.lean`, namespace `IUT.Countermodels.Joint`; and `Basic.lean`.

| Lean name | Kind | Statement |
|---|---|---|
| `IUT.Countermodels.separate_witnesses_no_joint` | countermodel | Two predicates on `Bool`, each satisfiable, with no common witness. |
| `zmod7_separate_not_joint` | countermodel | Among automorphisms of the multiplicative monoid of `ZMod 7`, "fixes `3`" and "sends `2` to `4`" are each satisfiable but not jointly. |
| `linear_separate_not_joint` | countermodel | For `θ > 0`, `q > 0`, among maps `x ↦ c x`, `c > 0`: "`1 ↦ 1`" and "`θ ↦ q`" are each satisfiable; jointly iff `θ = q`. |
| `joint_witness_of_product` | positive | If candidates form a product and the conditions constrain different factors, separate witnesses combine. |

*Abstraction refuted:* separately satisfiable compatibility conditions on a transport map are jointly satisfiable. In `zmod7_separate_not_joint` both conditions prescribe a Kummer-type value of one monoid automorphism; they clash because `2 = 3²`.

*Bears on:* Step (iii) of the proof of Corollary 3.12 (page 176): the unit portion and the value group portion must be related via a single Θ×μ_LGP-link, because relating them via different links runs into the non-commutativity of the log-theta-lattice. The positive statement is the situation of a single poly-isomorphism that is a product of its two portions.

### 5. Does invariance under individual indeterminacies give invariance under their combined action?

File `IUT/Countermodels/CombinedIndeterminacies.lean`, namespace `IUT.Countermodels.Indet`; and `Basic.lean`.

| Lean name | Kind | Statement |
|---|---|---|
| `IUT.Countermodels.invariant_comp` | positive | A function invariant under `g` and `h` is invariant under `g ∘ h`. |
| `invariant_closure` | positive | A function invariant under the permutations `g` and `h` is invariant under the whole group they generate. |
| `invariant_set_closure` | positive | A set mapped onto itself by the permutations `g` and `h` is mapped onto itself by the generated group. |
| `IUT.Countermodels.separate_orbits_ne_joint_orbit` | countermodel | On `Fin 3`, a composite image lies outside the union of the separate images. |
| `separate_finite_joint_infinite` | countermodel | With `S = [0, 1]` and the reflections `x ↦ −x`, `x ↦ 2 − x` (each of order 2), both preserve Lebesgue measure; the union of the images of `S` under each separately has volume at most `3`; under the generated group, infinite volume. |

*Principle that holds:* for single-valued quantities, invariance under each indeterminacy gives invariance under the combined action. *Abstraction refuted:* for set-valued constructions such as a union of possible images, a bound obtained per indeterminacy bounds the union under the combined action.

*Bears on:* the statement of Corollary 3.12 (pages 173 and 174), where `− |log(Θ)|` is the log-volume of the hull of the union of possible images subject to (Ind1), (Ind2), (Ind3) together; Theorem 3.11 (i), (ii) (pages 154 and 156); Step (x) (page 181), which states that the log-volumes are invariant under (Ind1), (Ind2). The example concerns volumes of unions, not the papers' log-volumes; see also `IUT.Audit.MochizukiResponses.LVEx` for a symmetrized region.

### 6. Do hull formation and transport commute?

File `IUT/Countermodels/HullTransport.lean`, namespace `IUT.Countermodels.Hull`; and `Basic.lean`.

| Lean name | Kind | Statement |
|---|---|---|
| `IUT.Countermodels.hull_transport_not_commute` | countermodel | On `Fin 3`, the order hull does not commute with a transposition. |
| `halfConj_countermodel` | countermodel | The bijective `ℝ`-linear map `(z, w) ↦ (z, conj w)` of `ℂ²` does not commute with the `ℂ`-span of `{(1, 1)}`. |
| `shear_countermodel` | countermodel | The `ℤ`-linear shear `a + b i ↦ (a + b) + b i` of `ℤ[i]` does not commute with the `ℤ[i]`-submodule generated by `1 + i`. |
| `hull_transport_semilinear` | positive | The image of a span under a semilinear map (over a surjective ring map) is the span of the image. |

*Abstraction refuted:* forming a hull commutes with transport, when the transport preserves less structure than the hull uses. The hulls are Mathlib's `Submodule.span`: over `ℂ` (a stand-in for a hull relative to a holomorphic structure, transported along a mono-analytic, i.e. only `ℝ`-linear, map) and over `ℤ[i]` (an integral hull, an `𝒪`-submodule, transported along a `ℤ`-linear map).

*Bears on:* the statement of Corollary 3.12 and Steps (xi-c), (xi-d) (pages 173, 174, 182, 183): the output of the multiradial algorithm is enlarged to its holomorphic hull relative to the arithmetic holomorphic structure labeled `1, ◦`, expressed over the rings `𝒪_{K_v}`.

### 7. Can the comparison be derived from a reconstruction statement alone?

File `IUT/Countermodels/ReconstructionComparison.lean`, namespace `IUT.Countermodels.Comparison`.

| Lean name | Kind | Statement |
|---|---|---|
| `invariant_of_iso` | positive | The log-volume of the pilot region of a normalized line is preserved by any measurable bijection carrying measure to measure and pilot to pilot (per-copy reconstruction). |
| `link_and_reconstruction_no_relation` | countermodel | For any positive pilot lengths and any `α, β`, there are normalizations and a continuous increasing additive link, carrying pilot onto pilot, with invariants `α` and `β`. |
| `link_compatible_with_both_orders` | countermodel | For fixed positive pilot lengths, a link and per-copy reconstruction are compatible with either strict order between the invariants. |
| `invariant_le_of_volume_compatible` | positive | If the link also carries measure to measure (volume compatibility) and pilot into pilot, the pilot of `T₀` has nonzero measure and the pilot of `T₁` finite measure, then the first invariant is at most the second. |

*The model.* A *normalized line* is `ℝ` with the measure `c · volume` and pilot region `[0, a]`; its invariant is the log-volume of the pilot region. The intended case is `c > 0`, `a > 0`, where the measure is a Haar measure; the structure `NormalizedLine` does not enforce it (for `c ≤ 0` its measure is the zero measure and the invariant is `0` by totalization), and every countermodel uses positive data. A *link* is an automorphism of the additive group `ℝ` carrying pilot onto pilot. *Abstraction refuted:* a link identifying part of the structure, together with per-copy reconstruction, determines a relation between the two invariants. *The named extra compatibility* that restores a comparison is volume compatibility of the link; with inclusion of pilots instead of equality it gives an inequality, the toy counterpart of the upper semi-compatibility (Ind3) of Theorem 3.11 (ii) (page 156).

*What the model does and does not satisfy.* It has two copies of a structure carrying a real-valued log-volume, a link identifying pilot objects, and internal computability of each log-volume. It has no Hodge theaters, Frobenioids, Kummer theory, log-links, log-Kummer correspondence, tensor packets, multiradial algorithm, indeterminacies, holomorphic hull, or the properties (IPL), (SHE), (APT). In the proof of Corollary 3.12, Steps (xi-b) to (xi-e) (pages 181 to 184) do not compare the two log-volumes through a bare link: they express both, through the multiradial representation and (SHE), relative to the single arithmetic holomorphic structure of the `1`-column. Volume compatibility in the model is the toy counterpart of what those steps are meant to supply. The model shows only that some such compatibility is indispensable; it does not show that the papers fail to supply it. The link is linear, so the model sits inside the hypothesis "(Lin)" of `IUT.Audit.ScholzeStix.Diagram`, which Mochizuki disputes for the situation of the papers.

## Build

Each module imports only `Mathlib` and builds with, for example, `lake build IUT.Countermodels.ReconstructionComparison`. New modules: `IUT.Countermodels.MultiplicativeAdditive`, `IUT.Countermodels.LevelMismatch`, `IUT.Countermodels.HaarNormalization`, `IUT.Countermodels.JointWitness`, `IUT.Countermodels.CombinedIndeterminacies`, `IUT.Countermodels.HullTransport`, `IUT.Countermodels.ReconstructionComparison`.
