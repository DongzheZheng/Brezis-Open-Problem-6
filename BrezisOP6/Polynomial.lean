import Mathlib

/-!
# The contact polynomial in the higher-dimensional Brezis OP6 argument

This file formalizes the complete parameter-domain positivity certificate in
the paper's appendix. It does not import a two-dimensional result. The
variables `M`, `X`, `Y` are independent real numbers and later correspond to
the profile contrast, normalized ratio growth, and logarithmic slope defect.
-/

namespace BrezisOP6

noncomputable section

private def A0 (X Y : ℝ) : ℝ := X ^ 3 * Y * (2 - Y)
private def A1 (X Y : ℝ) : ℝ :=
  X ^ 2 * (X * Y ^ 2 + 4 * X * Y + 2 * Y ^ 2 - 2 * Y + 1)
private def A2 (X Y : ℝ) : ℝ :=
  X * (5 * X ^ 2 * Y ^ 2 + 2 * X ^ 2 * Y - X * Y ^ 2 +
    2 * X * Y + X - 2 * Y ^ 2 - 4 * Y)
private def A3 (X Y : ℝ) : ℝ :=
  Y * (3 * X ^ 3 * Y - 3 * X ^ 2 * Y + 4 * X ^ 2 + 4 * Y + 6)
private def A4 (X Y : ℝ) : ℝ :=
  2 * (X * Y ^ 2 + 2 * X * Y - 2 * Y ^ 2 + Y + 6)

/-- The degree-four contact polynomial `N` in Appendix A. -/
def contactPolynomial (M X Y : ℝ) : ℝ :=
  A0 X Y + A1 X Y * M + A2 X Y * M ^ 2 +
    A3 X Y * M ^ 3 + A4 X Y * M ^ 4

private theorem A0_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hY1 : Y < 1) : 0 < A0 X Y := by
  unfold A0
  have : 0 < 2 - Y := by linarith
  positivity

private theorem A1_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    0 < A1 X Y := by
  have hid : X * Y ^ 2 + 4 * X * Y + 2 * Y ^ 2 - 2 * Y + 1 =
      X * Y * (Y + 4) + 2 * (Y - 1 / 2) ^ 2 + 1 / 2 := by ring
  unfold A1
  rw [hid]
  positivity

private theorem A3_pos {X Y : ℝ} (hX : 0 < X) (hX1 : X < 1)
    (hY : 0 < Y) (hY1 : Y < 1) : 0 < A3 X Y := by
  have hprod : Y * X > 0 := mul_pos hY hX
  have hcore : 0 < 4 - 3 * Y * (1 - X) := by nlinarith
  have hid : 3 * X ^ 3 * Y - 3 * X ^ 2 * Y + 4 * X ^ 2 + 4 * Y + 6 =
      6 + 4 * Y + X ^ 2 * (4 - 3 * Y * (1 - X)) := by ring
  unfold A3
  rw [hid]
  positivity

private theorem A4_pos {X Y : ℝ} (hX : 0 < X)
    (hY : 0 < Y) (hY1 : Y < 1) : 0 < A4 X Y := by
  have h1Y : 0 < 1 - Y := by linarith
  have hid : X * Y ^ 2 + 2 * X * Y - 2 * Y ^ 2 + Y + 6 =
      5 + (1 - Y) * (2 * Y + 1) + X * Y * (Y + 2) := by ring
  unfold A4
  rw [hid]
  positivity

private theorem A2_add_XA3_pos {X Y : ℝ} (hX : 0 < X) (hX1 : X < 1)
    (hY : 0 < Y) : 0 < A2 X Y + X * A3 X Y := by
  have hX2 : X < 2 := by linarith
  have h2X : 0 < 2 - X := by linarith
  have hid : A2 X Y + X * A3 X Y =
      X * (X + 2 * Y + (2 - X) * Y ^ 2 + 2 * X * Y +
        6 * X ^ 2 * Y + 2 * X ^ 2 * Y ^ 2 + 3 * X ^ 3 * Y ^ 2) := by
    unfold A2 A3
    ring
  rw [hid]
  positivity

private def B0 (_X Y : ℝ) : ℝ := Y * (2 - Y)
private def B1 (X Y : ℝ) : ℝ :=
  (1 + X * Y * (Y + 4) + 2 * Y * (3 - Y)) / 4
private def B2 (X Y : ℝ) : ℝ :=
  (3 + X * (1 + 14 * Y + 2 * Y ^ 2) +
    X ^ 2 * (2 * Y + 5 * Y ^ 2) + 2 * Y * (1 - Y)) / 6
private def B3 (X Y : ℝ) : ℝ :=
  (3 + 2 * X + X * (16 * Y + Y ^ 2) +
    X ^ 2 * (8 * Y + 7 * Y ^ 2) + 3 * X ^ 3 * Y ^ 2 + 2 * Y ^ 2) / 4
private def B4 (X Y : ℝ) : ℝ :=
  1 + 13 * X + 2 * Y + 3 * Y ^ 2 + 4 * X * Y * (2 - Y) +
    X ^ 2 * (10 * Y + 4 * Y ^ 2) + 3 * X ^ 3 * Y ^ 2

private def bernsteinForm (Z X Y : ℝ) : ℝ :=
  (1 - Z) ^ 4 * B0 X Y +
  4 * Z * (1 - Z) ^ 3 * B1 X Y +
  6 * Z ^ 2 * (1 - Z) ^ 2 * B2 X Y +
  4 * Z ^ 3 * (1 - Z) * B3 X Y +
  Z ^ 4 * B4 X Y

private theorem bernsteinForm_pos {Z X Y : ℝ} (hZ : 0 < Z) (hZ1 : Z < 1)
    (hX : 0 < X) (hY : 0 < Y) (hY1 : Y < 1) :
    0 < bernsteinForm Z X Y := by
  have h1Z : 0 < 1 - Z := by linarith
  have h2Y : 0 < 2 - Y := by linarith
  have h3Y : 0 < 3 - Y := by linarith
  have h1Y : 0 < 1 - Y := by linarith
  have hb0 : 0 < B0 X Y := by unfold B0; positivity
  have hb1 : 0 < B1 X Y := by unfold B1; positivity
  have hb2 : 0 < B2 X Y := by unfold B2; positivity
  have hb3 : 0 < B3 X Y := by unfold B3; positivity
  have hb4 : 0 < B4 X Y := by unfold B4; positivity
  unfold bernsteinForm
  positivity

private theorem bernstein_identity (Z X Y : ℝ) :
    contactPolynomial (X * Z) X Y = X ^ 3 * bernsteinForm Z X Y := by
  unfold contactPolynomial A0 A1 A2 A3 A4 bernsteinForm
    B0 B1 B2 B3 B4
  ring

/-- For every `M > 0` and `0 < X,Y < 1`, the contact polynomial is strictly
positive. The two proof regions are `M ≥ X` and `M < X`; in the second region
the change of variable `Z = M/X` exposes five positive Bernstein coefficients. -/
theorem contactPolynomial_pos {M X Y : ℝ} (hM : 0 < M)
    (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1) :
    0 < contactPolynomial M X Y := by
  have hA0 := A0_pos hX hY hY1
  have hA1 := A1_pos hX hY
  have hA3 := A3_pos hX hX1 hY hY1
  have hA4 := A4_pos hX hY hY1
  by_cases hXM : X ≤ M
  · have hQ := A2_add_XA3_pos hX hX1 hY
    have hMXnonneg : 0 ≤ M - X := by linarith
    calc
      contactPolynomial M X Y =
          A0 X Y + A1 X Y * M + M ^ 2 * (A2 X Y + X * A3 X Y) +
          M ^ 2 * (M - X) * A3 X Y + A4 X Y * M ^ 4 := by
            unfold contactPolynomial
            ring
      _ > 0 := by positivity
  · have hMX' : M < X := lt_of_not_ge hXM
    let Z : ℝ := M / X
    have hZ : 0 < Z := div_pos hM hX
    have hZ1 : Z < 1 := (div_lt_one hX).2 hMX'
    have hXZ : X * Z = M := by
      dsimp [Z]
      field_simp
    rw [← hXZ, bernstein_identity]
    have hB := bernsteinForm_pos hZ hZ1 hX hY hY1
    positivity

end

end BrezisOP6
