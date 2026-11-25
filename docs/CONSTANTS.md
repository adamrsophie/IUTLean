# IUT IV: numerical constants of Sections 1 and 2

Every numerical constant that appears in Sections 1 and 2 of *Inter-universal Teichmüller
Theory IV* (April 2020 manuscript), with its PDF page, its definition or role, where it is used,
and whether its use is checked in Lean. "Kernel checked" means the arithmetic in which the
constant appears is proved in Lean; "conditional" means it is proved relative to named
hypotheses that encode unformalized inputs. Unless stated, Lean names are in the namespace
`IUT.PaperIV.Theorem1_10` (modules under `IUT/PaperIV/Theorem1_10/`).

## Section 1

| Constant | Page | Definition or role | Used in | Lean |
|---|---|---|---|---|
| `a_i = (1/e_i)·⌈e_i/(p−2)⌉` (`p > 2`), `a_i = 2` (`p = 2`) | 10 | exponent in Prop 1.2 (i) | Props 1.2, 1.4; Thm 1.10 Step (v) | `Proposition1_2.a`; properties kernel checked |
| `b_i = ⌊log(p·e_i/(p−1))/log p⌋ − 1/e_i` | 10 | exponent in Prop 1.2 (i) | Props 1.2, 1.4 | `Proposition1_2.b`; properties kernel checked |
| `p − 2` (threshold `e_i ≤ p − 2`) | 10, 13 | `a_i = 1/e_i = −b_i` below it | Props 1.2 (iii), 1.4 (iii); Thm 1.10 Step (v) | `Proposition1_2.a_b_of_le` |
| `1/(p−1)` | 11 | lower bound for `a_i` and `p^{b_i+1/e_i}/e_i` | Prop 1.2 (i) | `Proposition1_2.a_gt`, `rpow_b_gt` |
| `4/p`, `2/log p` | 14 | `a_i − 1/e_i ≤ 4/p ≤ 2/log p` | Prop 1.4 (iii) | `Proposition1_2.a_sub_le`, `four_div_le` |
| `1/(p−2) ≤ 4/p` (`p ≥ 3`), `p/(p−1) ≤ 2`, `2/p ≤ 1/log p` | 14 | auxiliary estimates | Prop 1.4 (iii) | inside `a_sub_le`, `b_add_le`, `four_div_le` |
| `log(2e_i) ≤ 1 + log e_i` | 14 | bound on `(b_i + 1/e_i)·log p` | Prop 1.4 (iii) | `Proposition1_2.b_add_le` |
| `3` in `∑_{i∈I*}{3 + log e_i}` | 13, 14 | `2 + 1` from the two estimates above | Prop 1.4 (iii); Thm 1.10 Step (v) | `Proposition1_4.a_add_b_le`, `iii_second` |
| `4·|I*|/p` | 13, 14 | first upper bound of (iii) | Prop 1.4 (iii) | `Proposition1_4.iii_first` (conditional on `μ^log` properties) |
| `+1` in `(−λ + 𝔡_I + 1)·log p` | 13, 14 | from the floor `⌊λ − 𝔡_I − a_I⌋` | Prop 1.4 (iii) | hypothesis `hfloor` of `iii_first` |
| `|I|`, `2·|I|` | 13, 14 | lower bounds for `𝔡_I + a_I` (`p > 2`, `p = 2`) | Prop 1.4 (iii); Thm 1.10 Step (v) | `Proposition1_4.dI_add_aI_ge` |
| `1/e_i + m_i/(e_i f_i)` | 13, 14 | `−μ^log(log_p(R_i^×))/log p` | Prop 1.4 (ii) | `Proposition1_4.ii_identity`, `ii_le` |
| `1/e_0`, `(e_{i/0} − 1)/e_i`, `n_i` | 11, 12 | bounds on differents | Prop 1.3; Thm 1.10 Steps (ii), (iii) | `Proposition1_3.i_min`, `ii_base`, `ii_step` |
| `(p−1)/(p·e*)`, `p/ε` | 12 | Kummer step bounds | Prop 1.3 (ii) | `Proposition1_3.ii_step` |
| `2` (metric factor), `√2` (lengths) | 15 | `ℂ ⊗_ℝ ℂ ≅ ℂ ⊕ ℂ` | Prop 1.5 (i) | `Proposition1_5.crt_normSq` |
| `2^{|I|−1}·|V|^{|I|}` | 15 | number of copies of `ℂ` in `M_I` | Prop 1.5 (iii) | `Proposition1_5.count_iii` |
| `2^{|I|−1}` (metric factor), `λ^{|I|}` | 15, 16 | metrics on `M_I`; Prop 1.5 (iv) | Thm 1.10 Step (vii) | not formalized |
| `4/3` | 16 | `n ≤ 4p_n/(3 log p_n)`, `π(η) ≤ 4η/(3 log η)` | Prop 1.6; Thm 1.10 Step (viii) | `Proposition1_6.proposition1_6` (both displays), with components `exists_n0`, `exists_eta_prm` (kernel checked from Mathlib's PNT) |
| `η_prm` | 16 | threshold of Prop 1.6 | Thm 1.10 statement and Step (viii); Cor 2.2 (`C_K = 40η_prm + 2B_K`) | `exists_eta_prm` and `proposition1_6` give `η_prm ≥ 2`; the paper says positive, which suffices since Step (viii) divides by `log(η_prm)` only when `1 < e*_mod·l < η_prm` |
| `n` (tuple length), `β_avg` | 16, 17 | weighted averages | Prop 1.7; Thm 1.10 Step (v) | `Proposition1_7.weighted_averages` |
| `log(q_v)`, `1` | 21 | weights of `deg_F` at finite and infinite places | Def 1.9 (i) | `degWeight` in `ArithmeticDivisor.lean` |
| `[F_v : ℚ_{v_ℚ}]` | 22 | denominator of `deg_E` | Def 1.9 (ii); Thm 1.10 Step (v) weights | `localDeg`, `degE` in `Definition1_9.lean` (`degE` takes a `PlaceSet`: a nonempty finite set of valuations over one place of `ℚ`) |
| `d_mod = [F_mod : ℚ]`, `e_mod` | 22 | degree and maximal ramification index | Thm 1.10, Cor 2.2 | variables |
| `d*_mod = 2¹²·3³·5·d_mod`, `e*_mod = 2¹²·3³·5·e_mod` | 22 | scaled degree and ramification | Thm 1.10 Steps (iii), (v), (viii); Rem 1.10.7 (i) | `R4`, `step_viii_constant` (with `e*_mod` as `2^12*3^3*5*e`) |
| `l ≥ 5`, `l ≠ 5` | 22 | hypotheses on `l` (IUT I Def 3.1 (c) gives `l ≠ 5`) | Thm 1.10 | hypotheses of all step lemmas |
| `12·d_mod/l`, `10`, `1/6`, `12/l²`, `(l+1)/4`, `−1` | 23 | the expression for `C_Θ` | Thm 1.10 | `constant` (existing) |
| `20·d_mod/l`, `20`, `l ≥ 7` | 23, 31 | final inequality | Thm 1.10; Cor 2.2 | `final_inequality` (existing; conditional on `C_Θ ≥ −1`) |
| `(n+1)/2`, `(2n+1)(n+1)/6` | 23 | (E1), (E2) | Thm 1.10 Step (v) | `E1`, `E2` (existing), `procession_sum` |
| `p(p+1)(p−1)²` | 23 | (E3) `|GL₂(𝔽_p)|` | Step (ii); Cor 2.2 | `card_GL2` (kernel checked) |
| `2·3`, `3·2⁴`, `5·2⁵·3` | 23 | (E4) | Step (ii) | `E4` |
| `2¹¹·3³·5` | 24 | `|GL₂(𝔽₂)|·|GL₂(𝔽₃)|·|GL₂(𝔽₅)|·2`, bound on `[F : F_mod]` | Steps (ii), (iii); Cor 2.2 (`[F : ℚ] ≤ δ`) | `E4_product` |
| `2` | 23 | (E5) `[F_mod(√−1) : F_mod] ≤ 2` | Step (ii) | not formalized (field theory) |
| `0, 1, 2` | 24 | (E6) `0 ≤ log 2 ≤ 1 ≤ log 3 ≤ log π ≤ log 5 ≤ 2` | Steps (ii), (iii), (vii); Cor 2.2 | `E6`, `log_two_le_one`, `one_le_log_three`, `log_five_le_two` |
| `2¹¹·3³·5²`, `21` | 24 | `log(2¹¹·3³·5²) ≤ 21` | Step (ii) | `log_E_ii`, `step_ii_F` |
| `2·log l`, `46` | 24 | `log l/l ≤ 1/2`, `1 + 4/l ≤ 2`; `2·21 + 4 = 46` | Step (ii) | `two_log_le_self`, `one_add_four_div_le_two`, `step_ii_final` |
| `2¹¹·3³·5·e_mod·l⁴` (R1), `2¹¹·3³·5·e_mod·l` (R2), `2¹¹·3³·5·e_mod` (R3) | 25 | ramification bounds | Step (iii) | hypotheses of `R4` |
| `−3 + 4·log(e*_mod·l)`, `e*_mod·l` | 26 | (R4) | Steps (iii), (v) | `R4` (kernel checked from (R1) to (R3)) |
| `1/2` | 26 | `(1/p)·log p ≤ 1/2` for `p = l ≥ 5` | Step (iii) | `step_iii_p_eq_l` |
| `2·3·5`, `5`, `8·d_mod/l`, `6` | 26 | `log(𝔰^ℚ) ≤ 2d_mod·D + 5 + log l`; `(4/l)log(𝔰^ℚ) ≤ (8d_mod/l)D + 6` | Step (iii) | `log_30_mul_le`, `step_iii_sQ` |
| `52` | 26 | `46 + 6` | Step (iii) final display | `step_iii_final` (needs `D ≥ 0`) |
| `l* = (l−1)/2` | 27, 29 | number of labels `j ∈ 𝔽_l^*` up to sign | Step (v) averaging | `procession_average`, `procession_average_l` |
| `l*_mod = log(e*_mod·l)` | 28 | logarithmic size | Steps (v), (viii) | `sum_Istar_le`, `step_viii_prime_count` |
| `4(j+1)·l*_mod` | 28 | `∑_{I*}{3 + log e_i}` bound | Step (v) | `sum_Istar_le` |
| `j²/(2l(j+1))`, `1/(j+1)`, `ι_{v_ℚ}` | 28 | terms of `β_e` | Step (v) | `step_v_weighted` |
| `(l*+3)/2`, `(2l*+1)(l*+1)/(12l)`, `2(l*+3)` | 29 | averaged coefficients | Step (v) | `procession_average` |
| `(l+5)/4`, `(l+1)/24`, `l+5` | 29 | same with `l = 2l*+1` | Steps (v), (vii) | `procession_average_l`, `step_vii_average` |
| `20/3`, `4(l+5)/(l+1) ≤ 20/3`, `1/(l+1) ≤ 1/l` | 29 | final display of Step (v) | Step (v) | `step_v_final` (kernel checked; needs `l ≥ 5`, nonnegativity) |
| `log π`, `4` | 29, 30 | archimedean bound `(l+5)/4·log π ≤ (l+1)/4·4` | Step (vii) | `step_vii_archimedean` (existing), `step_vii_average` |
| `0` | 29 | local bound at nondistinguished places | Step (vi) | none; the bound is `μ^log((R_I)^∼) = 0` with the inclusion of Prop 1.4 (iv), not formalized |
| `56` | 30 | `52 + 4` | Step (viii) | `step_viii_raw` |
| `(l+1)/4·(1/6)·(12/l²) ≥ 1/(2l)` | 30 | absorbs the `log 𝔮` term | Step (viii) | `step_viii_estimate` (existing), `step_viii_raw` |
| `4/3·(e*_mod·l + η_prm)` | 31 | bound on `l*_mod·log(𝔰^≤)` | Step (viii) | `step_viii_prime_count` (two cases), `step_viii_prime_count_prm` |
| `1/3·4/3`, `2¹²·3·5 ≥ 56` | 31 | absorbs `2 log l + 56` | Step (viii) | `step_viii_absorb` (existing) |
| `(20 + 1)/3·4/3 = 7·4/3 ≤ 10` | 31 | coefficient `10` of `e*_mod·l + η_prm` | Step (viii) | `step_viii_substitute` (existing), `step_viii_constant` |
| `(1 − 12/l²)^{−1} ≤ 2`, `(1 − 12/l²)^{−1}(1 + 12d_mod/l) ≤ 1 + 20d_mod/l` | 31 | final portion, `l ≥ 7`, `d_mod ≥ 1` | Thm 1.10 final | `final_estimate_one`, `final_estimate_two` (existing) |

## Section 2

| Constant | Page | Definition or role | Used in | Lean |
|---|---|---|---|---|
| `1` in `log x ≤ x` for `x ≥ 1` | 40 | Prop 2.1 (i) | Cor 2.2 | `Proposition2_1.log_le_self` |
| `ξ_prm ≥ 5`, `2/3`, `4/3` | 40 | Prop 2.1 (ii) | Cor 2.2 | `Proposition2_1.exists_xi_prm` (kernel checked from Mathlib) |
| `2(θ_A + ξ_prm)` | 40 | prime outside `A` | Cor 2.2 (P1) | `Proposition2_1.exists_prime_not_mem` |
| `1/6` | 41 | `(1/6)·log 𝔮 ≈ ht_{ω_X(D)}`; degree `6` of the divisor at infinity of `M̄_ell` and `1` of `ω_X(D)` | Cor 2.2 (i) | not formalized |
| `δ = 2¹²·3³·5·d` | 42 | bound for `[F : ℚ]` and `d*_mod` | Cor 2.2 | variable; `h_bound_Hunif` uses it explicitly |
| `ε_d ≤ 1`, `ε ≤ 1` | 42 | parameters of (ii), (iii) | Cor 2.2 | hypotheses |
| `10δ`, `log(2δh)` | 42 | (C1) | Cor 2.2 | `P1_upper`, `P1_lower` |
| `ε_E = (60δ)²·h^{−1/2}·log(2δh)` | 42, 47 | error term in (C2) | Cor 2.2 (ii), (iii) | `assembly`, `epsE_ge`, `h_lt_of_eps_lt_epsE` |
| `log(2l)` | 43 | `log-cond_D ≤ log 𝔣^{F_tpd} + log(2l)` | Cor 2.2 (C2) | not used in Lean |
| `H_unif`, `H_K`, `C_K` | 42, 43 | constants of (ii), (iii) | Cor 2.2 | `H_unif = 16³·(60·2¹²·3³·5)⁵` suffices for the `ε_E` step (`h_bound_Hunif`); other enlargements of the exceptional set are not formalized |
| `ε_d^{−3}·d^{4+ε_d}`, `ε^{−3}` | 42, 43 | shape of the bound on exceptional sets | Cor 2.2 (ii), (iii) | `h_lt_of_eps_lt_epsE`, `h_bound_Hunif` |
| `4` (four `j`-invariants) | 43 | curves without `F`-core ([CanLift] Prop 2.7) | Cor 2.2 proof | not formalized |
| `h^{1/2} ≥ ξ_prm ≥ 5` | 44 | enlargement of `Exc_d` | Cor 2.2 proof | hypotheses `hs`, `hξ` |
| `2·log p ≥ log 4 ≥ 1` | 44 | estimate in the `log h_v` sum | Cor 2.2 proof | `one_le_log_three` family; the sum is not formalized |
| `2h^{1/2} + δh^{1/2} + 2δh^{1/2}·log(2δh)`, `4δ`, `5δ` | 45 | bound on `θ_A` | Cor 2.2 (P1) | `thetaA_chain`, `S1_bound` |
| `20δ²h²` | 45 | upper bound for `l` | Cor 2.2 (P1) | `P1_bound` |
| `24`, `l − 2`, `T_K`, `48` | 45 | (P4) bound | Cor 2.2 (P4) | `P4_bound` (gives `log 𝔮^∀ ≤ 48(1 + T_K)`) |
| `20 ≤ 5²`, `5 ≤ 2⁴`, `8`, `16δ^{1/4}h^{3/4}` | 45, 46 | `h^{1/2}·log l` chain | Cor 2.2 (P5) | `sqrt_mul_log_l`, `sqrt_mul_log_l_steps` |
| `h^{3/4}` | 46 | (P5) boundedness | Cor 2.2 (P5) | `P5_bound` |
| `20·d_mod ≤ d*_mod ≤ δ`, `δ·h^{−1/2}`, `200δ²` | 46 | applying Thm 1.10 | Cor 2.2 | `apply_theorem_1_10` |
| `1/3`, `5 ≤ 2³` | 47 | `(1/6)log 𝔮^{∤2} − (1/6)log 𝔮 ≤ h^{1/2}·log(2δh)` | Cor 2.2 | `q_not2_step` |
| `B_K` | 47 | bounded discrepancy `(1/6)log 𝔮^∀ − (1/6)log 𝔮^{∤2}` | Cor 2.2 | hypothesis `hB` of `assembly` |
| `(15δ)²`, `6·5 ≤ 2·4²`, `1/2·C_K`, `C_K = 40η_prm + 2B_K` | 47 | assembly | Cor 2.2 | `fifteen_delta_step`, `assembly` |
| `5δ·h^{−1/2}`, `2/5`, `1/5` | 47 | `ε_E ≥ 5δh^{−1/2}`; coefficients in the assembled bound | Cor 2.2 | `epsE_ge`, `assembly` |
| `ε*_d = ε_d/16`, `1/2 − ε*_d`, `3`, `4 + ε_d ≤ 5` | 47 | real-power estimate | Cor 2.2 (ii), (iii) | `eps_star_estimates`, `h_lt_of_eps_lt_epsE` |
| `60δ ≥ 2δ ≥ 1` | 47 | base of the real power | Cor 2.2 | inside `h_lt_of_eps_lt_epsE` |
| `(1 + ε/5)/(1 − 2ε/5) ≤ 1 + ε`, `1 − 2ε/5 ≥ 1/2` | 48 | final step for `0 < ε ≤ 1` | Cor 2.2 (C2) | `final_step` |
| `d_mod ≤ d` | 55 | used in the proof of Cor 2.3 | Cor 2.3 | not formalized |
| `2·(deg E/deg ω_X)` | 55 | correction (v) to [GenEll] Thm 2.1 | Rem 2.3.1 (v) | not formalized |
