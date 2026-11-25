# The log-theta-lattice of IUT III

Source: Mochizuki, *Inter-universal Teichmüller Theory III*, Proposition 1.2 (x) (page 34), Proposition 1.3 (pages 41 to 43), Definition 1.4 and Remark 1.4.1 (pages 45 to 47), Theorem 1.5 (pages 48 to 51), Definition 3.8 (pages 112 to 114), Remarks 3.10.2, 3.11.3 and 3.12.2 (pages 151 to 152, 169 to 171, 187 to 195), and Corollary 3.12 Step (xi) and Fig. 3.8 (pages 181 to 185).

Displays were checked against rendered pages 34, 45, 46, 48 to 50, 113, 114 and 185. Remarks 3.10.2, 3.11.3 and 3.12.2 (iv), (v) were read in text only, so their diagrams are described here in words and not transcribed.

## Vertices

* **The vertices of the lattice.** The vertices are Θ^{±ell}NF-Hodge theaters `n,m HT^{Θ±ellNF}`, indexed by `(n,m) ∈ Z × Z`. Definition 1.4 (page 45) requires them to be distinct. They are all relative to one fixed collection of initial Θ-data.
* **Coric vertices.** These are not vertices of the lattice. They are objects determined by a whole column or by the whole lattice:
  * **Vertical cores** `n,◦HT^{D-Θ±ellNF}`: the D-Θ^{±ell}NF-Hodge theater of the n-th column, determined up to isomorphism (Thm 1.5 (i), page 48).
  * **Bi-cores**:
    * the F^{⊢×μ}-prime-strips `F^{⊢×μ}_△(n,m D^⊢_△)`, regarded up to a certain class of isomorphisms (Thm 1.5 (iii), pages 49 to 50);
    * the mono-analytic log-shells (Thm 1.5 (iv), page 50);
    * the global realified Frobenioids `D^⊩(n,m D^⊢_△)` (Thm 1.5 (v), page 50).

## Arrows and their structural levels

**Vertical arrows: full log-links `n,m HT → n,m+1 HT`** (Def 1.4, page 45; Def 1.1 (iii), page 27).

* **Level:** F-prime-strips. The link is the tautological log-link post-composed with the full poly-isomorphism of F-prime-strips.
* **What it preserves** (Prop 1.3, Thm 1.5 (i)):
  * the associated D-prime-strips and the D-Θ^{±ell}NF-Hodge theater, up to full poly-isomorphism;
  * log-volumes (Prop 1.2 (iii));
  * ring structure on each side.
* **What it does not preserve:** Kummer isomorphisms (Prop 1.2 (iv)).

**Horizontal arrows of the Gaussian lattice.**

* **Arrows:** Θ^{×μ}-links (non-Gaussian) or Θ^{×μ}_gau-links (Gaussian), `n,m HT → n+1,m HT` (Def 1.4, page 45; IUTchII Cor 4.10 (iii)).
* **Level:** defined in IUTchII Cor 4.10 (iii), which was not read for this document. What IUT III states about them is listed below.
* **Induced on F^{⊢×μ}-prime-strips:** full poly-isomorphisms `n,m 𝔉^{⊢×μ}_△ ≅ n+1,m 𝔉^{⊢×μ}_△` (Thm 1.5 (ii), page 48).
* **Ring structures:** incompatible with the local ring structures (Rem 1.4.1 (i), page 46).

**Horizontal arrows of the LGP-Gaussian lattice.**

* **Arrows:** Θ^{×μ}_LGP-links `n,m HT → n+1,m HT` (Def 3.8 (ii), (iii), pages 112 to 114). The lgp-Gaussian lattice uses Θ^{×μ}_lgp-links instead.
* **What the link is:** the full poly-isomorphism of F^{⊩▶×μ}-prime-strips `n,m 𝔉^{⊩▶×μ}_LGP ≅ n+1,m 𝔉^{⊩▶×μ}_△`.
* **Dependence on the vertical arrow:** the arrow from (n,m) is defined relative to the full log-link `n,m−1 HT → n,m HT`. So each horizontal arrow depends on the vertical arrow arriving at its domain (page 114).
* **Level:** F^{⊩▶×μ}-prime-strips. The link splits into:
  * a unit portion on F^{⊢×μ}-prime-strips;
  * a value group portion on F^{⊩▶}-prime-strips.
  
  The value group portion maps Θ-pilot objects to q-pilot objects (Rem 3.8.1, page 114; Cor 3.12 Step (i), page 175).

**Kummer arrows to the vertical core.**

* **Arrows:** `n,m (Frobenius-like data) ≅ n,◦ (étale-like data)`. These are the Kummer isomorphisms of Prop 3.5 (i), Prop 3.10 (i) and Thm 3.11 (ii) (page 155).
* **Level:** labeled data (Ψ_cns, global Frobenioids, number fields).
* **Arrows into bi-cores:** `n,m 𝔉^{⊢×μ}_△ ≅ F^{⊢×μ}_△(n,m D^⊢_△)` (Thm 1.5 (iii), page 50).

**Permutation symmetries across columns.**

* **Maps:** `Prc(n,◦D^⊢_T) ≅ Prc(n',◦D^⊢_T)` and `n,◦R^LGP ≅ n',◦R^LGP`, induced by étale-picture permutation symmetries (Thm 3.11 (i), pages 154 to 155).
* **Level:** D^⊢-prime-strip processions and the étale-like data built from them.

## Diagrams and their commutativity

**Frobenius-picture of a column** (Prop 1.2 (x), page 34; Prop 1.3 (iv)).

* **Shape:** a chain of log-links with Kummer arrows from every vertex to the core ◦.
* **Commutativity:** it does **not** commute (Rem 1.2.2 (iii), text).
* **Weaker properties:**
  * the coric holomorphic log-shells satisfy upper semi-commutativity, i.e. containments (Rem 1.2.2 (iii); Rem 1.5.4 (iii), pages 56 to 57, text);
  * there is no lower semi-commutativity (Rem 1.2.2 (iv), text);
  * the diagram is described as commutative with respect to log-volumes (Rem 1.2.2 (v), text).
* **Forgetful step:** after forgetting to log-volumes, it commutes (asserted). After forgetting to coric log-shells, it commutes only up to containment.
* **Symmetry:** Z translation symmetry fixing ◦. No permutation symmetry swapping adjacent vertices (page 34).

**Squares of the log-theta-lattice** (Def 1.4, Rem 1.4.1 (i), page 46; Rem 3.11.3 (i), text).

* **Shape:** square `(n,m) → (n+1,m) → (n+1,m+1)` versus `(n,m) → (n,m+1) → (n+1,m+1)`.
* **Commutativity:** "far from being [1-]commutative" (page 46), because vertical arrows use ring structures and horizontal arrows are incompatible with them.
* **Forgetful step:** commutes after passing to bi-coric data (Rem 3.11.3 (i), text): the poly-isomorphisms of Thm 1.5 (iii) to (v) are invariant under both kinds of arrows. The vertical collection is strictly smaller than the horizontal one (page 49), so "commutes" means compatibility of poly-isomorphisms as sets, after restriction.

**Horizontal line with vertical shift** (Rem 1.4.1 (ii), page 46; Cor 3.12 Steps (iii), (iv), pages 176 to 177).

* **The constraint:** each horizontal arrow obligates a subsequent vertical arrow. Unit and value group portions must be related through a single horizontal arrow.
* **Resolution:** work with vertically coric structures, at the cost of Ind3.
* **Commutativity:** commutes after forgetting to vertically coric structures, up to Ind3 (containment).

**Log-Kummer correspondence on a column** (Thm 3.11 (ii), pages 155 to 156).

* **Shape:** Kummer arrows `(n,m) → (n,◦)` for all m, with log-links between consecutive m.
* **Commutativity:** it does not commute in general. It is exactly compatible for:
  * the splitting monoids (b);
  * the MOD lines of (c);
  
  and only upper semi-compatible (Ind3) for the local packets (a). It is not compatible for the mod lines (page 156).
* **Forgetful step:** commutes after taking log-volumes (Thm 3.11 (ii), final sentence, page 156; Prop 3.9 (iv)).

**Horizontal compatibility square** (Thm 3.11 (iii), pages 156 to 158).

* **Shape:** Kummer isomorphisms at columns n and n+1, the horizontal full poly-isomorphism, and the poly-isomorphism of cores.
* **Commutativity:** commutes for the F^{⊢×μ}-prime-strips (iii.a, iii.b), as an equality of poly-isomorphisms.
* **Theta and number field data (iii.c, iii.d):** commutes only up to Ind1, Ind2, Ind3. Here "commutes" means stabilized/equivariant/functorial with respect to arbitrary automorphisms of the domain and codomain.

**Remark 3.10.2 diagram** (pages 151 to 152, text).

* **Shape:** a commutative diagram `env → gau → LGP → lgp` of prime-strips, with vertical Kummer arrows. The lower arrows are conjugates of the upper ones.
* **Commutativity:** stated as commutative. Not checked against a render.

**Fig. 3.8** (page 185, rendered).

* **Two paths to the log-volume of the q-pilot object at (1,0).**
  * The first goes from the Θ-pilot object at (0,0), via Kummer-detachment and the log-Kummer correspondence, compatibly with the Θ^{×μ}_LGP-link, to the multiradial representation at (0,◦). From there the permutation symmetry leads to (1,◦), and the comparison uses the hull and the log-volume.
  * The second goes directly from the q-pilot object at (1,0), via the (−)^{⊩▶} and (−)^{⊢×μ} portions of the link.
* **Commutativity:** described as "two tautologically equivalent ways to compute" (Step (xi-g), page 184). The outputs are a region bound `R_{≤−|log(Θ)|}` and a number `−|log(q)|`. The relation asserted between them is the inclusion of Step (xi-f), not an equality. See `docs/COR312_ANALYSIS.md`.

**Fig. 3.9: 0-column versus 1-column** (Rem 3.12.2 (iv), (v), text).

* **What is compared:** the 1-column has no multiradiality.
* **What absorbs which indeterminacy:**
  * the O^×-multiple indeterminacy is absorbed by hulls;
  * the ring-structure indeterminacy is absorbed by log-volumes;
  * precise equalities hold in the 1-column, upper bounds in the 0-column.
* **Commutativity:** described in text. Not checked against a render.

## Ambiguities, with pages

* **Page 49.** "regarded up to a certain class of isomorphisms" for the bi-coric strip: the class is not described explicitly.
* **Rem 1.2.2 (v), text.** "commutative with respect to log-volumes" is not a defined property.
* **Remarks 1.5.1 to 1.5.3 (pages 52 to 55).** These were not read. Rem 1.5.4 cites Rem 1.5.2.
