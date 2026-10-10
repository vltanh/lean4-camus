module

public import Camus.External.NMSC.ThreeCycle

/-!
# The anomaly zone of the 3-cycle above two taxa

Section 3.3 of CAMUS designs Quartet Filtering (Algorithm 1) on the presumption that, where a
level-1 network displays one quartet on four taxa, that quartet is the most probable. On the
3-cycle above two taxa `N₃₂` (`Brooqs.net32`: `x` and `y` below the hybrid node, with an edge of
length `ℓ` above their cherry; `z` on the side `S₁`, an edge of length `L` from the top node of the
cycle followed by the hybrid edge of length `h₁` and inheritance probability `γ`; the side `S₂` a
single hybrid edge of length `h₂`; `w` outside the cycle) the presumption fails for some parameters
(`Brooqs.net32_anomaly`) and holds for others (`Brooqs.net32_long`). This file finds the parameters
for which it fails. Write `u = e^{-ℓ}` and
`D = γ(1 - γ)(1 - e^{-L}) - γ²(1 - e^{-h₁}) - (1 - γ)²(1 - e^{-h₂})`. For all parameters,
`CF(xy|zw) = 1/3 + 2/3 (1 - u) - 2/3 u D` and `CF(xz|yw) = CF(xw|yz) = 1/3 - 1/3 (1 - u) + 1/3 u D`,
so the displayed quartet `xy|zw` is strictly less probable than the two others iff `1 - u < u D`,
that is,
`γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1) < γ(1 - γ)(1 - e^{-L})`,
strictly more probable iff the reverse strict inequality holds, and the three CFs are `1/3` on the
boundary. Given that the lineages of `x` and `y` reach the hybrid node apart, the right side is the
probability that the lineage of `x` takes `S₁`, that of `y` takes `S₂`, and the first coalesces
with the lineage of `z` on the edge of length `L`; the left side adds the probabilities that both
take the same side and coalesce on its hybrid edge, and the odds `e^ℓ - 1` against their reaching
the hybrid node apart.

For a metric `N₃₂` with `0 < γ < 1` and `L > 0`, the anomaly holds as soon as `ℓ`, `h₁` and `h₂`
are at most `log(1 + γ(1 - γ)(1 - e^{-L})/3)`, and it fails as soon as
`γ(1 - γ)(1 - e^{-L}) ≤ e^ℓ - 1`, whatever `h₁` and `h₂`, in particular for `ℓ ≥ log(5/4)`. For
given `γ` and `ℓ`, some positive `h₁`, `h₂`, `L` make `N₃₂` anomalous iff `e^ℓ < 1 + γ(1 - γ)`;
for given `ℓ`, some parameters do iff `ℓ < log(5/4)`.

## Relation to Ané, Fogg, Allman, Baños and Rhodes (2024)

Their Example 1 computes the CF of the displayed quartet of a 3₂-cycle under their model NMSC(ρ),
in which `ρ` is the correlation of the parental origins of two lineages at a hybrid node: the two
lineages take the parent edges `(e_i, e_j)` with probability `(1 - ρ)γ_iγ_j` for `i ≠ j` and
`(1 - ρ)γ_i² + ργ_i` for `i = j`. The NMSC of this library is `ρ = 0`, where the lineages choose
their parents independently; at `ρ = 1` all the lineages at a hybrid node take the same parent.
With `ρ = 0` and their `t`, `s₀`, `s₁`, `s₂`, `γ₁`, `γ₂` read as `ℓ`, `L`, `h₁`, `h₂`, `γ`, `1 - γ`,
their formula is the CF of `xy|zw` of `Brooqs.net32_quartetCF`, and for `s₁ = s₂ = 0` their
simplified formula is `Brooqs.net32_quartetCF_excess`. They observe that the CF is least for
`s₁ = s₂ = 0` and tends to `1/3 - (2/3)(1 - ρ)γ₁γ₂ < 1/3` as `t → 0` and `s₀ → ∞`, so that a
3₂-cycle is anomalous for some parameters, for every `ρ < 1` and `γ₁ ∈ (0, 1)`; their Theorem 8
extends this existence statement to every 4-taxon network of type 1 or 2 that contains a 3₂-cycle.
This file determines, for `ρ = 0` and the network `N₃₂` itself, the exact set of anomalous
parameters (`Brooqs.net32_anomalous_iff`). Their remark that the CFs of a 3₂-cycle are those of a
quartet tree whose internal edge may have negative length reads here: the internal edge has length
`τ` with `e^{-τ} = u (1 + D)`, and `N₃₂` is anomalous iff `τ < 0`.

## Main results

* `Brooqs.net32_quartetCF_sum`, `Brooqs.net32_quartetCF_excess`: the three CFs add up to `1`, and
  their expression in `u` and `D`.
* `Brooqs.net32_anomalous_iff`, `Brooqs.net32_anomalous_iff_u`: the anomaly zone.
* `Brooqs.net32_regular_iff`, `Brooqs.net32_boundary_iff`, `Brooqs.net32_boundary_iff_third`: the
  zone where the displayed quartet is strictly the most probable, and the boundary between the two
  zones, where the three CFs are `1/3`.
* `Brooqs.net32_anomalous_of_short`, `Brooqs.exists_net32_anomalous_of_short`: short edges at the
  hybrid node make `N₃₂` anomalous.
* `Brooqs.net32_not_anomalous_of_le`, `Brooqs.net32_regular_of_le`, `Brooqs.net32_regular_of_log`:
  a long edge below the hybrid node makes it regular.
* `Brooqs.net32_exists_anomalous_iff`, `Brooqs.net32_exists_anomalous_iff_log`: the edges below the
  hybrid node for which some parameters make `N₃₂` anomalous.

## Proof

By `Brooqs.net32_quartetCF`, `CF(xz|yw) - CF(xy|zw) = 3 CF(xz|yw) - 1 = u (1 + D) - 1`, which is
`u (D - (e^ℓ - 1))` (`Brooqs.net32_quartetCF_sub`); its sign is the sign of `D - (e^ℓ - 1)`.
-/

@[expose] public noncomputable section

namespace Brooqs

universe u

variable {X : Type u} [DecidableEq X]

/-- The three quartet CFs of `N₃₂` on `x, y, z, w` add up to `1`, for all parameters. -/
theorem net32_quartetCF_sum {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w +
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w +
      (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x w y z = 1 := by
  obtain ⟨h0, h1, h2⟩ := net32_quartetCF hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ L
  rw [h0, h1, h2]
  ring

/-- **The CFs of `N₃₂` in the form of Ané et al. (2024, Example 1).** For all parameters, with
`u = e^{-ℓ}` and `D = γ(1 - γ)(1 - e^{-L}) - γ²(1 - e^{-h₁}) - (1 - γ)²(1 - e^{-h₂})`:
`CF(xy|zw) = 1/3 + 2/3 (1 - u) - 2/3 u D` and `CF(xz|yw) = CF(xw|yz) = 1/3 - 1/3 (1 - u) + 1/3 u D`.
For `h₁ = h₂ = 0` the first is the formula of their Example 1 with `ρ = 0`. Equivalently
`CF(xy|zw) = 1 - 2/3 u (1 + D)` and `CF(xz|yw) = 1/3 u (1 + D)`: the CFs of a quartet tree whose
internal edge has length `τ`, with `e^{-τ} = u (1 + D)`. -/
theorem net32_quartetCF_excess {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w = 1 / 3 + 2 / 3 * (1 - Real.exp (-ℓ)) -
        2 / 3 * Real.exp (-ℓ) * (γ * (1 - γ) * (1 - Real.exp (-L)) -
          γ ^ 2 * (1 - Real.exp (-h₁)) - (1 - γ) ^ 2 * (1 - Real.exp (-h₂))) ∧
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w = 1 / 3 - 1 / 3 * (1 - Real.exp (-ℓ)) +
        1 / 3 * Real.exp (-ℓ) * (γ * (1 - γ) * (1 - Real.exp (-L)) -
          γ ^ 2 * (1 - Real.exp (-h₁)) - (1 - γ) ^ 2 * (1 - Real.exp (-h₂))) ∧
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x w y z =
      (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w := by
  obtain ⟨h0, h1, h2⟩ := net32_quartetCF hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ L
  refine ⟨?_, ?_, ?_⟩
  · rw [h0]
    ring
  · rw [h1]
    ring
  · rw [h1, h2]

/-- The difference `CF(xz|yw) - CF(xy|zw)` on `N₃₂`, for all parameters: `e^{-ℓ}` times the excess
of `γ(1 - γ)(1 - e^{-L})` over `γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1)`. -/
theorem net32_quartetCF_sub {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w -
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w =
      Real.exp (-ℓ) * (γ * (1 - γ) * (1 - Real.exp (-L)) -
        (γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) +
          (Real.exp ℓ - 1))) := by
  obtain ⟨h0, h1, -⟩ := net32_quartetCF hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ L
  have hk : Real.exp ℓ * Real.exp (-ℓ) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [h0, h1]
  linear_combination hk

/-- **The anomaly zone of `N₃₂`.** For all parameters, the quartet `xy|zw`, the only one of the
three quartets on `x, y, z, w` that `N₃₂` displays (`Brooqs.net32_displays`), has a strictly smaller
CF than `xz|yw`, which has the same CF as `xw|yz`, iff
`γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1) < γ(1 - γ)(1 - e^{-L})`.
This is the anomaly of Ané et al. (2024) on the 3₂-cycle `N₃₂` under their NMSC(0): their Example 1
shows that some parameters satisfy the inequality; here it is the exact condition. -/
theorem net32_anomalous_iff {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w <
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w ↔
      γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1) <
        γ * (1 - γ) * (1 - Real.exp (-L)) := by
  rw [← sub_pos, net32_quartetCF_sub hxy hxz hxw hyz hyw hzw,
    mul_pos_iff_of_pos_left (Real.exp_pos _), sub_pos]

/-- **The anomaly zone of `N₃₂`, with `u = e^{-ℓ}`.** For all parameters, `CF(xy|zw) < CF(xz|yw)`
iff `1 - u < u D`, where `D = γ(1 - γ)(1 - e^{-L}) - γ²(1 - e^{-h₁}) - (1 - γ)²(1 - e^{-h₂})`:
the probability `1 - u` that the lineages of `x` and `y` coalesce below the hybrid node is less than
the probability `u` that they do not, times the excess `D`. -/
theorem net32_anomalous_iff_u {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w <
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w ↔
      1 - Real.exp (-ℓ) < Real.exp (-ℓ) * (γ * (1 - γ) * (1 - Real.exp (-L)) -
        γ ^ 2 * (1 - Real.exp (-h₁)) - (1 - γ) ^ 2 * (1 - Real.exp (-h₂))) := by
  have hk : Real.exp ℓ * Real.exp (-ℓ) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have e : Real.exp (-ℓ) * (γ * (1 - γ) * (1 - Real.exp (-L)) -
      (γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1))) =
      Real.exp (-ℓ) * (γ * (1 - γ) * (1 - Real.exp (-L)) -
        γ ^ 2 * (1 - Real.exp (-h₁)) - (1 - γ) ^ 2 * (1 - Real.exp (-h₂))) -
          (1 - Real.exp (-ℓ)) := by
    linear_combination -hk
  rw [← sub_pos, net32_quartetCF_sub hxy hxz hxw hyz hyw hzw, e, sub_pos]

/-- **The regular zone of `N₃₂`.** For all parameters, the quartet `xy|zw` that `N₃₂` displays has
a strictly larger CF than `xz|yw` and `xw|yz` iff
`γ(1 - γ)(1 - e^{-L}) < γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1)`. -/
theorem net32_regular_iff {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w <
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w ↔
      γ * (1 - γ) * (1 - Real.exp (-L)) <
        γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1) := by
  have hu := Real.exp_pos (-ℓ)
  rw [← sub_neg, net32_quartetCF_sub hxy hxz hxw hyz hyw hzw]
  constructor
  · intro h
    by_contra hge
    exact absurd h (not_lt.2 (mul_nonneg hu.le (sub_nonneg.2 (not_lt.1 hge))))
  · intro h
    exact mul_neg_of_pos_of_neg hu (sub_neg.2 h)

/-- **The boundary between the two zones.** For all parameters, `CF(xy|zw) = CF(xz|yw)` iff
`γ(1 - γ)(1 - e^{-L}) = γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1)`. -/
theorem net32_boundary_iff {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w =
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w ↔
      γ * (1 - γ) * (1 - Real.exp (-L)) =
        γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1) := by
  rw [eq_comm, ← sub_eq_zero, net32_quartetCF_sub hxy hxz hxw hyz hyw hzw, mul_eq_zero,
    or_iff_right (Real.exp_pos _).ne', sub_eq_zero]

/-- On the boundary, the three quartet CFs are `1/3`: for all parameters, `CF(xy|zw) = CF(xz|yw)`
iff `CF(xy|zw) = CF(xz|yw) = CF(xw|yz) = 1/3`. -/
theorem net32_boundary_iff_third {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w =
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w ↔
      (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w = 1 / 3 ∧
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w = 1 / 3 ∧
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x w y z = 1 / 3 := by
  have hsum := net32_quartetCF_sum hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ L
  have h12 := (net32_quartetCF_excess hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ L).2.2
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h0, h1, -⟩
    rw [h0, h1]

/-! ### The zones for metric parameters -/

/-- **Short edges at the hybrid node make `N₃₂` anomalous.** Let `0 < γ < 1` and `L > 0`, and let
`ε = log(1 + γ(1 - γ)(1 - e^{-L})/3)`, a positive number. If `ℓ`, `h₁` and `h₂` are at most `ε`,
then `CF(xy|zw) < CF(xz|yw) = CF(xw|yz)`. So the anomaly needs no long edge in the cycle, unlike the
limit of Ané et al. (2024, Example 1): any `L > 0` will do, with short enough edges at the hybrid
node. -/
theorem net32_anomalous_of_short {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hL : 0 < L) (hℓ : ℓ ≤ Real.log (1 + γ * (1 - γ) * (1 - Real.exp (-L)) / 3))
    (hh₁ : h₁ ≤ Real.log (1 + γ * (1 - γ) * (1 - Real.exp (-L)) / 3))
    (hh₂ : h₂ ≤ Real.log (1 + γ * (1 - γ) * (1 - Real.exp (-L)) / 3)) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w <
      (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w := by
  rw [net32_anomalous_iff hxy hxz hxw hyz hyw hzw]
  set c := γ * (1 - γ) * (1 - Real.exp (-L)) with hc
  have hlam : Real.exp (-L) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hc0 : 0 < c := mul_pos (mul_pos hγ0 (by linarith)) (by linarith)
  set ε := Real.log (1 + c / 3) with hε
  have hεe : Real.exp ε = 1 + c / 3 := Real.exp_log (by linarith)
  -- `e^ℓ - 1 ≤ c/3`
  have e1 : Real.exp ℓ ≤ 1 + c / 3 := by
    rw [← hεe]
    exact Real.exp_le_exp.2 hℓ
  -- `1 - e^{-h} ≤ c/3` for `h ≤ ε`
  have key : ∀ h, h ≤ ε → 1 - Real.exp (-h) ≤ c / 3 := by
    intro h hh
    have k1 : Real.exp (-ε) ≤ Real.exp (-h) := Real.exp_le_exp.2 (by linarith)
    have k2 : Real.exp (-ε) * Real.exp ε = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have k3 : Real.exp (-ε) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.log_nonneg (by linarith)))
    rw [hεe] at k2
    nlinarith [mul_nonneg (sub_nonneg.2 k3) hc0.le]
  have k1 := mul_le_mul_of_nonneg_left (key h₁ hh₁) (sq_nonneg γ)
  have k2 := mul_le_mul_of_nonneg_left (key h₂ hh₂) (sq_nonneg (1 - γ))
  -- `γ² + (1 - γ)² ≤ 1`
  have hs : γ ^ 2 + (1 - γ) ^ 2 ≤ 1 := by nlinarith
  have k3 := mul_le_mul_of_nonneg_left hs hc0.le
  linarith

/-- For `0 < γ < 1` and `L > 0` there is `ε > 0` such that `N₃₂` is anomalous whenever `ℓ`, `h₁`
and `h₂` are at most `ε` (`Brooqs.net32_anomalous_of_short`). -/
theorem exists_net32_anomalous_of_short {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) {γ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hL : 0 < L) :
    ∃ ε > 0, ∀ ℓ h₁ h₂ : ℝ, ℓ ≤ ε → h₁ ≤ ε → h₂ ≤ ε →
      (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w <
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w := by
  refine ⟨Real.log (1 + γ * (1 - γ) * (1 - Real.exp (-L)) / 3), Real.log_pos ?_,
    fun ℓ h₁ h₂ hℓ hh₁ hh₂ =>
      net32_anomalous_of_short hxy hxz hxw hyz hyw hzw hγ0 hγ1 hL hℓ hh₁ hh₂⟩
  have hlam : Real.exp (-L) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hc0 : 0 < γ * (1 - γ) * (1 - Real.exp (-L)) :=
    mul_pos (mul_pos hγ0 (by linarith)) (by linarith)
  linarith

/-- **Outside the anomaly zone.** If `h₁, h₂ ≥ 0` and `γ(1 - γ)(1 - e^{-L}) ≤ e^ℓ - 1`, then
`N₃₂` is not anomalous: `CF(xz|yw) ≤ CF(xy|zw)`, whatever `γ`, `L`, `h₁` and `h₂`. -/
theorem net32_not_anomalous_of_le {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) {γ ℓ h₁ h₂ L : ℝ} (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂)
    (hle : γ * (1 - γ) * (1 - Real.exp (-L)) ≤ Real.exp ℓ - 1) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w ≤
      (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w := by
  rw [← not_lt, net32_anomalous_iff hxy hxz hxw hyz hyw hzw, not_lt]
  have a1 : 0 ≤ γ ^ 2 * (1 - Real.exp (-h₁)) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)))
  have a2 : 0 ≤ (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)))
  linarith

/-- **A long edge below the hybrid node makes `N₃₂` regular.** If `γ > 0`, `h₁ > 0`, `h₂ ≥ 0`
and `γ(1 - γ)(1 - e^{-L}) ≤ e^ℓ - 1`, the quartet `xy|zw` that `N₃₂` displays has a strictly larger
CF than the two others, whatever `L`. -/
theorem net32_regular_of_le {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hh₁ : 0 < h₁)
    (hh₂ : 0 ≤ h₂) (hle : γ * (1 - γ) * (1 - Real.exp (-L)) ≤ Real.exp ℓ - 1) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w <
      (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w := by
  rw [net32_regular_iff hxy hxz hxw hyz hyw hzw]
  have a1 : 0 < γ ^ 2 * (1 - Real.exp (-h₁)) :=
    mul_pos (pow_pos hγ0 2) (sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith)))
  have a2 : 0 ≤ (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)))
  linarith

/-- For metric parameters and `ℓ ≥ log(5/4)`, `N₃₂` is regular: `γ(1 - γ)(1 - e^{-L}) < 1/4`, while
`e^ℓ - 1 ≥ 1/4`. -/
theorem net32_regular_of_log {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hℓ : Real.log (5 / 4) ≤ ℓ) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w <
      (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w := by
  refine net32_regular_of_le hxy hxz hxw hyz hyw hzw hγ0 hh₁ hh₂.le ?_
  have h5 : 5 / 4 ≤ Real.exp ℓ := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 5 / 4)]
    exact Real.exp_le_exp.2 hℓ
  have hlam := Real.exp_pos (-L)
  nlinarith [sq_nonneg (γ - 1 / 2), mul_pos (mul_pos hγ0 (sub_pos.2 hγ1)) hlam]

/-- **The edge below the hybrid node bounds the anomaly zone.** Let `0 < γ < 1`. Some positive `h₁`,
`h₂` and `L` make `N₃₂` anomalous iff `e^ℓ < 1 + γ(1 - γ)`. -/
theorem net32_exists_anomalous_iff {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (ℓ : ℝ) :
    (∃ h₁ h₂ L : ℝ, 0 < h₁ ∧ 0 < h₂ ∧ 0 < L ∧
      (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w <
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w) ↔
      Real.exp ℓ < 1 + γ * (1 - γ) := by
  have hγ := mul_pos hγ0 (sub_pos.2 hγ1)
  constructor
  · rintro ⟨h₁, h₂, L, hh₁, hh₂, -, h⟩
    rw [net32_anomalous_iff hxy hxz hxw hyz hyw hzw] at h
    -- the left side is at least `e^ℓ - 1`, the right side less than `γ(1 - γ)`
    have a1 : 0 ≤ γ ^ 2 * (1 - Real.exp (-h₁)) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)))
    have a2 : 0 ≤ (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)))
    nlinarith [mul_pos hγ (Real.exp_pos (-L))]
  · intro hlt
    -- `δ = 1 + γ(1 - γ) - e^ℓ`; take `e^{-L} = δ/2` and `e^{-h₁} = e^{-h₂} = 1 - δ/2`
    set δ := 1 + γ * (1 - γ) - Real.exp ℓ with hδ
    have hδ0 : 0 < δ := by linarith
    have hδ1 : δ < 2 := by nlinarith [sq_nonneg (γ - 1 / 2), Real.exp_pos ℓ]
    have eL : Real.exp (-(-Real.log (δ / 2))) = δ / 2 := by
      rw [neg_neg, Real.exp_log (by linarith)]
    have eh : Real.exp (-(-Real.log (1 - δ / 2))) = 1 - δ / 2 := by
      rw [neg_neg, Real.exp_log (by linarith)]
    refine ⟨-Real.log (1 - δ / 2), -Real.log (1 - δ / 2), -Real.log (δ / 2),
      neg_pos.2 (Real.log_neg (by linarith) (by linarith)),
      neg_pos.2 (Real.log_neg (by linarith) (by linarith)),
      neg_pos.2 (Real.log_neg (by linarith) (by linarith)), ?_⟩
    rw [net32_anomalous_iff hxy hxz hxw hyz hyw hzw, eL, eh]
    nlinarith [mul_pos hγ hδ0, mul_pos (mul_pos hγ hγ) hδ0]

/-- **The edges below the hybrid node that allow the anomaly.** Some metric parameters `γ`, `h₁`,
`h₂`, `L` make `N₃₂` with the edge `ℓ` below its hybrid node anomalous iff `ℓ < log(5/4)`. -/
theorem net32_exists_anomalous_iff_log {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (ℓ : ℝ) :
    (∃ γ h₁ h₂ L : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < h₁ ∧ 0 < h₂ ∧ 0 < L ∧
      (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w <
        (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w) ↔
      ℓ < Real.log (5 / 4) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  constructor
  · rintro ⟨γ, h₁, h₂, L, hγ0, hγ1, hh₁, hh₂, hL, h⟩
    have := (net32_exists_anomalous_iff hxy hxz hxw hyz hyw hzw hγ0 hγ1 ℓ).1
      ⟨h₁, h₂, L, hh₁, hh₂, hL, h⟩
    nlinarith [sq_nonneg (γ - 1 / 2)]
  · intro h
    obtain ⟨h₁, h₂, L, hh₁, hh₂, hL, hlt⟩ :=
      (net32_exists_anomalous_iff hxy hxz hxw hyz hyw hzw (γ := 1 / 2) (by norm_num)
        (by norm_num) ℓ).2 (by linarith)
    exact ⟨1 / 2, h₁, h₂, L, by norm_num, by norm_num, hh₁, hh₂, hL, hlt⟩

end Brooqs
