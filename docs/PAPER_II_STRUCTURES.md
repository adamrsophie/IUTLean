# Structures of IUT II

Source: Mochizuki, *Inter-universal Teichmüller Theory II: Hodge-Arakelov-theoretic
Evaluation*. Page numbers are PDF pages of `documentation/ref/Inter-universal Teichmuller
Theory II.pdf`. Displays marked "rendered" were checked against a page render; others come from
the text layer only.

Notation: l ≥ 5 is a prime; l^⋇ = (l − 1)/2; |F_l| = F_l/{±1} = {0} ⊔ F_l^⋇ with
F_l^⋇ = F_l^×/{±1}; F_l^{⋊±} = F_l ⋊ {±1} (IUT I page 3, rendered; IUT II page 3, rendered).
Each j ∈ |F_l| has a unique representative in {0, 1, …, l^⋇} (IUT II page 3). This last fact
is proved in `IUT/PaperII/Labels.lean` (`labelRep_bijective`).

## 1. Étale theta functions

* The étale theta function is the reciprocal of an l-th root of the theta function, written
  Θ_v at bad places (Introduction, page 2).
* Group-theoretically, the theta classes are the ι-invariant classes θ(Π) attached to the
  tempered group Π, constructed up to a μ_{2l}-indeterminacy (Remark 1.12.2 (i), page 58), and
  the subsets ∞θ(Π) up to μ (Proposition 1.4, Corollary 1.12, pages 55 to 58).
* In the mono-theta-theoretic version they are attached to a projective system M^Θ_* of
  mono-theta environments and written θ_env (Definition 2.7, Corollary 2.8, pages 80 to 83).
* In the base-field-theoretic version they are written θ_bs (Corollary 2.9, pages 84 to 85).

## 2. Theta values at torsion points

* **Points.** For t ∈ LabCusp±, the evaluation section D_{t,μ−} is the decomposition group of
  the μ_−-translate of the cusp labeled t (Corollary 2.4 (ii), pages 69 to 70). The values
  depend only on |t| ∈ |F_l| (Corollary 2.5 (ii), page 71).
* **Values.** Relative to the standard cyclotomic rigidity and Kummer map, for j ∈ |F_l| the
  set θ^j consists of the μ_{2l}-orbit of q_v^{j²}, with j read in {0, 1, …, l^⋇} (Remark
  2.5.1 (i), page 72, rendered). The Introduction gives the same list: q^{j²} up to a 2l-th
  root of unity (page 2).
* **Up to what.** Each value is a μ_{2l}-orbit (θ) or μ-orbit (∞θ) (Corollary 2.5 (ii),
  page 71). The μ_{2l}-indeterminacies for different j are independent of each other, not
  synchronized (Remark 2.5.1 (iii), page 73). A value-profile chooses one element of each
  orbit; the set of value-profiles has cardinality (2l)^{l^⋇} (Corollary 3.5 (ii), page 94, rendered).
* **Zero label.** θ^0 is the μ_{2l}-orbit of the identity, which gives the zero-labeled
  splittings (Corollary 2.6 (ii), page 76).
* **Why j² and not other powers.** Remark 2.6.3 (pages 79 to 80, rendered) motivates the
  subgraph Γ_Y^▶ with vertices 0, …, l^⋇ via the quantity ‖Γ′‖. See
  `data/curated/iut2.json`, record `IUT2.Rem2_6_3`, for an interpretation issue on page 80.

## 3. Kummer-theoretic representations

* Kummer isomorphisms relate Frobenioid-theoretic monoids to group-theoretic ones:
  (Ψ_{†C_v})_t ⥲ Ψ_cns(M^Θ_*)_t, with an inner indeterminacy independent of t
  (Corollary 3.6 (i), page 99).
* The chain Ψ_{†F^Θ_v} ⥲ Ψ_env ⥲ Ψ_gau ⥲ Ψ_{F_gau} combines Kummer theory and Galois
  evaluation (Corollary 3.6 (ii), pages 100 to 101; Propositions 4.2 and 4.4, pages 123 to 131).
* At good nonarchimedean v the units admit a unique Ẑ^×-orbit of isomorphisms (Proposition
  4.2 (ii), page 124); at archimedean v a unique {±1}-orbit (Proposition 4.4 (ii), page 129).
* A ×-Kummer structure is a Ẑ^×-orbit of isomorphisms O^×(G) ⥲ O^×(A); a ×μ-Kummer structure
  is an Ism-orbit of isomorphisms O^{×μ}(G) ⥲ O^{×μ}(A) (Definition 4.9 (i), pages 153 to 154).
* Kummer N-th power maps respect multiplication but not addition (Remark 3.6.4, pages 105 to
  108). Only the first power of the theta function crosses the mono-theta "narrow bridge".

## 4. Gaussian monoids

* Mono-theta-theoretic: Ψ_ξ = Ψ^×_cns⟨F_l^⋇⟩ · ξ^ℕ and ∞Ψ_ξ = Ψ^×_cns⟨F_l^⋇⟩ · ξ^{Q≥0}, for
  value-profiles ξ; Ψ_{2l·ξ} does not depend on ξ (Corollary 3.5 (ii), pages 94 to 95,
  rendered 94).
* Formal version at good v: Ψ_gau = Ψ^×_cns⟨F_l^⋇⟩ × {R≥0 · (…, j² · log(p_v), …)}, inside
  ∏_{j ∈ F_l^⋇} Ψ^ss_cns,j, with j ∈ {1, …, l^⋇}; formal evaluation sends
  log(p_v)·log(Θ) to (…, j² log(p_v), …) (Proposition 4.1 (iv), page 122, rendered).
* Global: D_gau is the weighted diagonal (1²φ, 2²φ, …, j²φ, …) (Remark 4.5.4, page 136,
  rendered); volumes at each j get weight 1/l^⋇ (Remark 4.7.3 (iii), page 145, rendered).
* Gaussian monoids built group-theoretically are uniradial, since they use the cyclotomic
  rigidity of Corollary 1.11 (b) (Corollary 3.7 (ii), page 111).
* Elementary arithmetic (not in the paper, proved in `IUT/PaperII/Labels.lean`):
  24 · Σ_{j=1}^{l^⋇} j² = l(l² − 1), and (1/l^⋇) · Σ j² = l(l + 1)/12.

## 5. Cyclotomic rigidity isomorphisms

| Name | Identifies | Remaining indeterminacy | Radiality | Pages |
|---|---|---|---|---|
| (∗^{mono-Θ}_Π), mono-theta | (l·Δ_Θ)(Π) ⥲ Π_μ(M^Θ_*(Π)): interior cyclotome of the geometric tempered group with the cyclotome of the mono-theta environment | None stated beyond the choice of M^Θ_* | Multiradial (Cor 1.10); the reason is that Π_μ ⊗ Q/Z → O^{×μ}(G) is trivial (Rem 1.10.2) | 46 to 48 (rendered 47) |
| (∗bs-Gal_{G,▷}) | μ_Ẑ(G) ⥲ μ_Ẑ(O^×(G)) | A Γ-orbit, Γ ⊆ Ẑ^× closed | Multiradial only with this indeterminacy | 49 (rendered) |
| (∗bs-Gal_{G,Π}) | μ_Ẑ(G) ⥲ (l·Δ_Θ)(Π), via α: Π/Δ ⥲ G and [AbsTopIII] Cor 1.10 (c) | An Aut(G)-orbit | Multiradial with indeterminacy; induced surjections to Ẑ are uniradial or multiradial only up to Ẑ^× (Rem 1.11.5) | 49, 55 |
| Restricted mono-theta rigidity | (l·Δ_Θ)(M^Θ_{* subgraph}) ⥲ Π_μ(M^Θ_{* subgraph}) | As for (∗^{mono-Θ}) | Multiradial | 80 to 81 |

The Introduction describes the identification as one of the exterior cyclotome (roots of
unity of the base) with the interior cyclotome (pages 9 to 11).

## 6. Indeterminacies from changes of representation

* Conjugacy: Π_v-conjugacy at nonarchimedean v (Corollary 4.5 (i), pages 131 to 132).
* Conjugate synchronization: for F_l^{⋊±}-symmetry the inner indeterminacy is independent of
  |t| (Corollary 3.5 (i), page 94, rendered; Corollary 3.6 (i), page 99).
* F_l^⋇-symmetry: independent conjugacy indeterminacies for distinct j, plus one
  j-independent indeterminacy (Corollary 4.7 (ii), pages 140 to 141).
* Unit isomorphisms: Ẑ^× (good nonarchimedean), {±1} (archimedean), Ism for ×μ-Kummer
  structures (Proposition 4.2, Proposition 4.4, Definition 4.9 (i)).
* Theta values: μ_{2l} per label, independent across labels (Remark 2.5.1 (iii), page 73).
* Prime-strips at bad v: automorphisms of the split Frobenioids inducing the identity on the
  F^{⊢×}-prime-strip, absorbed by full poly-isomorphisms (Remark 4.10.1, pages 161 to 162).
* Global realified Frobenioids: compatibility only up to R>0-orbits (Corollary 4.10 (v),
  pages 160 to 161).
* Representative of a label: the identification of label 0 with F_l^⋇ (assignment "0, ≻ ↦ >")
  when passing to the D-ΘNF-Hodge theater (Remark 3.8.2 (ii), page 116; Corollary 4.10 (i),
  page 158, rendered).
