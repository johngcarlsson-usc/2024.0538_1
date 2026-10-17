"""Generate the certified numeric tables for `envelope_le` (BHH/Numerics.lean).

Scheme: envelope U = ∫_0^c (c-τ) ∫_0^U √(u²+τ²) e^{-a u} du dτ, a = 1.7319, c = 1.7321.
* τ-grid t_j = c j / M (M τ-cells); u-grid u_i = i²/75 (N = 30 cells, U0 = 12), tail [12, V].
* On cell (j,i): √X ≤ (X + w²)/(2w) (AM-GM), integrate (u²+K) e^{-au} exactly:
  ∫_{u0}^{u1} (u²+K)e^{-au} = e^{-a u0} Q(u0,K) - e^{-a u1} Q(u1,K),
  Q(u,K) = (u²+K)/a + 2u/a² + 2/a³.
* e^{-a u_i} = r^{i²}, r = e^{-a/75}; certified by chains hi_{i+1} ≥ hi_i rU^{2i+1}, lo likewise.
* Per τ-cell: inner integral ≤ α_j + β_j τ²; then ∫_{t_j}^{t_{j+1}} (c-τ)(α_j+β_jτ²) in closed form.
All inequalities are re-verified here in exact rational arithmetic.
"""
from fractions import Fraction as F
import math

a = F(17319, 10000)
c = F(17321, 10000)
N = 30          # u-cells
M = 8           # τ-cells
U0 = F(12)
SIG = 14


def u(i):
    return F(i * i, 75)


def Q(uu, K):
    return (uu * uu + K) / a + 2 * uu / a**2 + 2 / a**3


def round_up(x, sig=SIG):
    """smallest decimal with `sig` significant digits that is ≥ x (x > 0)"""
    e = math.floor(math.log10(x)) - sig + 1
    if e >= 0:
        q = F(10) ** e
        return F(math.ceil(x / q)) * q
    q = F(10) ** (-e)
    return F(math.ceil(x * q)) / q


def round_down(x, sig=SIG):
    e = math.floor(math.log10(x)) - sig + 1
    if e >= 0:
        q = F(10) ** e
        return F(math.floor(x / q)) * q
    q = F(10) ** (-e)
    return F(math.floor(x * q)) / q


# base r = exp(-a/75) via Taylor with remainder (Real.exp_bound, n = NT terms)
NT = 8
x = -a / 75
S = sum(x**m / math.factorial(m) for m in range(NT))
R = abs(x) ** NT * F(NT + 1, math.factorial(NT) * NT)
rU = round_up(S + R, 18)
rL = round_down(S - R, 18)
assert rL <= S - R and S + R <= rU and 0 < rL

hi = [F(1)]
lo = [F(1)]
for i in range(N):
    hi.append(round_up(hi[i] * rU ** (2 * i + 1)))
    lo.append(round_down(lo[i] * rL ** (2 * i + 1)))
for i in range(N):
    assert hi[i] * rU ** (2 * i + 1) <= hi[i + 1]
    assert lo[i + 1] <= lo[i] * rL ** (2 * i + 1)
for i in range(N + 1):
    ex = math.exp(-float(a * u(i)))
    assert float(lo[i]) <= ex * (1 + 1e-12) and ex <= float(hi[i]) * (1 + 1e-12)

t = [c * j / M for j in range(M + 1)]


def w_of(j, i):
    u0, u1, t0, t1 = u(i), u(i + 1), t[j], t[j + 1]
    m2 = (u0 * u0 + u0 * u1 + u1 * u1) / 3 + (t0 * t0 + t0 * t1 + t1 * t1) / 3
    return round_up(F(math.sqrt(float(m2))), 4)


W = [[w_of(j, i) for i in range(N)] for j in range(M)]
WT = U0  # tail AM-GM parameter

alpha, beta, aT, bT = [], [], [], []
DP = 14  # decimal places for per-term bounds


def ceil_dp(x, dp=DP):
    q = F(10) ** dp
    return F(math.ceil(x * q)) / q


for j in range(M):
    At = [(hi[i] * Q(u(i), W[j][i] ** 2) - lo[i + 1] * Q(u(i + 1), W[j][i] ** 2)) / (2 * W[j][i])
          for i in range(N)] + [hi[N] * Q(u(N), WT ** 2) / (2 * WT)]
    Bt = [(hi[i] - lo[i + 1]) / (a * (2 * W[j][i])) for i in range(N)] + [hi[N] / (a * (2 * WT))]
    aT.append([ceil_dp(v) for v in At])
    bT.append([ceil_dp(v) for v in Bt])
    alpha.append(sum(aT[j]))
    beta.append(sum(bT[j]))
    assert sum(At) <= alpha[j] and sum(Bt) <= beta[j]


def G(al, be, tt):
    return c * al * tt - al * tt**2 / 2 + c * be * tt**3 / 3 - be * tt**4 / 4


total = sum(G(alpha[j], beta[j], t[j + 1]) - G(alpha[j], beta[j], t[j]) for j in range(M))
print("certified total =", float(total))
assert total <= F(802, 1000)


def dec(q):
    """exact decimal literal for a Fraction with power-of-10 denominator"""
    q = F(q)
    num, den = q.numerator, q.denominator
    k = 0
    while 10**k % den != 0:
        k += 1
        assert k < 80, q
    n = num * (10**k // den)
    sgn = "-" if n < 0 else ""
    n = abs(n)
    if k == 0:
        return sgn + str(n)
    s = str(n).rjust(k + 1, "0")
    return sgn + s[:-k] + "." + s[-k:]


def table(name, vals, doc):
    lines = [f"/-- {doc} -/", f"def {name} : ℕ → ℝ"]
    for i, v in enumerate(vals):
        lines.append(f"  | {i} => {dec(v)}")
    lines.append("  | _ => 0")
    return "\n".join(lines)



# ---------------------------------------------------------------- Lean emission
GENERIC = open(__file__.replace("gen_numerics.py", "numerics_generic.lean.txt"), encoding="utf-8").read()

out = []
out.append(f"/-! ### Generated tables (BHH/gen_numerics.py); certified total = {float(total):.9f} -/")
out.append(f"def rU : ℝ := {dec(rU)}")
out.append(f"def rL : ℝ := {dec(rL)}")
out.append(table("hiT", hi, "upper bounds for `exp (-(1.7319 * (i^2/75)))`"))
out.append(table("loT", lo, "lower bounds for `exp (-(1.7319 * (i^2/75)))`"))
for j in range(M):
    out.append(table(f"wT{j}", W[j], f"AM-GM parameters for τ-cell {j}"))
for j in range(M):
    out.append(table(f"aT{j}", aT[j], f"per-cell bounds (constant part), τ-cell {j}"))
    out.append(table(f"bT{j}", bT[j], f"per-cell bounds (τ² part), τ-cell {j}"))
out.append(table("alT", alpha, "constant coefficients of the per-τ-cell bounds"))
out.append(table("beT", beta, "τ² coefficients of the per-τ-cell bounds"))
SEP = chr(10) * 2
tables = SEP.join(out)

per_j = []
for j in range(M):
    per_j.append(f"""lemma hw_{j} : ∀ i < 30, 0 < wT{j} i := by
  intro i hi; interval_cases i <;> norm_num [wT{j}]

set_option maxHeartbeats 1000000 in
lemma hAi_{j} : ∀ i < 30, (hiT i * Qf (uF i) (wT{j} i ^ 2) -
    loT (i + 1) * Qf (uF (i + 1)) (wT{j} i ^ 2)) / (2 * wT{j} i) ≤ aT{j} i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT{j}, Qf, uF, aT{j}]

set_option maxHeartbeats 1000000 in
lemma hBi_{j} : ∀ i < 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * wT{j} i)) ≤ bT{j} i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT{j}, bT{j}]

lemma inner_poly_{j} (τ V : ℝ) (hV : 12 ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT {j} + beT {j} * τ ^ 2 :=
  inner_poly τ V wT{j} hw_{j} _ _ aT{j} bT{j} hAi_{j}
    (by norm_num [hiT, Qf, uF, aT{j}]) hBi_{j} (by norm_num [hiT, bT{j}])
    (by norm_num [Finset.sum_range_succ, aT{j}, alT])
    (by norm_num [Finset.sum_range_succ, bT{j}, beT]) hV""")
cases = ", ".join(f"inner_poly_{j}" for j in range(M))
per_j.append(f"""lemma inner_poly_all : ∀ j < {M}, ∀ τ V : ℝ, 12 ≤ V →
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT j + beT j * τ ^ 2 := by
  intro j hj
  interval_cases j
  exacts [{cases}]""")

final = f"""theorem envelope_le (U : ℝ) (hU : 0 ≤ U) : envelope U ≤ 0.802 := by
  refine (envelope_le_sum U hU inner_poly_all).trans ?_
  norm_num [Finset.sum_range_succ, Gpoly, tF, alT, beT]"""

body = GENERIC.replace("--TABLES--", tables).replace("--PERJ--", SEP.join(per_j)).replace("--FINAL--", final)
open(__file__.replace("gen_numerics.py", "Numerics.lean"), "w", encoding="utf-8").write(body)
print("wrote Numerics.lean")
