"""
Stage 3b: UNTRUSTED exact-rational certificate generator.

Input system   C b >= d     (C: m x n, d: m, all rational, b free)

Output, exactly one of
  YES            b   with  C b >= d
  NO             lam with  lam >= 0, C^T lam = 0, d^T lam > 0
  SOLVER_FAILURE resource limit hit; says NOTHING about feasibility

Method: Phase I primal simplex over Fractions on
    sigma*(C(u-v) - s) + a = sigma*d  = |d|,   u,v,s,a >= 0
(b = u - v, s = slacks, sigma_i = sign(d_i), a = artificials, min sum a).
  optimum 0  -> b = u - v                         (YES)
  optimum >0 -> y = 1 - (reduced cost of artificial i),
                lam_i = sigma_i * y_i             (NO)
Pivoting: Dantzig's rule; Bland's rule only after a run of degenerate
pivots (anti-cycling), switching back after a strict objective decrease.

Nothing here is trusted: every answer goes through verify_yes/verify_no
(an exact mirror of the Lean checker) before being emitted, and the Lean
checker is the final authority.
"""
from fractions import Fraction
import json, re, sys, time

Q = Fraction
YES, NO, FAIL = "YES", "NO", "SOLVER_FAILURE"


class InputError(ValueError):
    pass

_RAT = re.compile(r"^-?\d+(/\d+)?$")

def parse_q(x):
    """Exact rational from a JSON value: int (not bool) or 'p' / 'p/q' string.
    JSON floats, bools, decimals-as-strings, and zero denominators are rejected,
    so no binary-float rounding can enter the system."""
    if isinstance(x, bool) or isinstance(x, float):
        raise InputError(f"not an exact rational: {x!r}")
    if isinstance(x, int):
        return Q(x)
    if isinstance(x, str) and _RAT.match(x.strip()):
        num, _, den = x.strip().partition("/")
        if den and int(den) == 0:
            raise InputError(f"zero denominator: {x!r}")
        return Q(int(num), int(den)) if den else Q(int(num))
    raise InputError(f"not an exact rational: {x!r}")

def _is_dim(k):
    return isinstance(k, int) and not isinstance(k, bool) and k >= 0

def _is_rat(x):
    return isinstance(x, (Fraction, int)) and not isinstance(x, bool)

def fmt_q(x):
    x = Q(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


# ---------- exact verifier (mirror of the Lean array checker) ----------
def well_formed(C, d, m, n):
    return (_is_dim(m) and _is_dim(n)
            and len(C) == m and len(d) == m
            and all(len(r) == n and all(_is_rat(x) for x in r) for r in C)
            and all(_is_rat(x) for x in d))

def verify_yes(C, d, m, n, b):
    if not well_formed(C, d, m, n) or len(b) != n or not all(_is_rat(x) for x in b):
        return False
    return all(sum(C[i][j] * b[j] for j in range(n)) >= d[i] for i in range(m))

def verify_no(C, d, m, n, lam):
    if not well_formed(C, d, m, n) or len(lam) != m or not all(_is_rat(x) for x in lam):
        return False
    if any(l < 0 for l in lam):
        return False
    if any(sum(C[i][j] * lam[i] for i in range(m)) != 0 for j in range(n)):
        return False
    return sum(d[i] * lam[i] for i in range(m)) > 0


# ---------- solver ----------
def solve(C, d, m, n, max_pivots=100_000, time_limit=None, stall_limit=50, rule="hybrid"):
    """Returns (status, payload, stats). payload = b | lam | reason."""
    t0 = time.monotonic()
    if not well_formed(C, d, m, n):
        return FAIL, "malformed input", {}
    if m == 0:
        return YES, [Q(0)] * n, {"pivots": 0}

    sigma = [1 if d[i] >= 0 else -1 for i in range(m)]
    # columns: u(0..n-1) v(n..2n-1) s(2n..2n+m-1) a(2n+m..2n+2m-1)
    ncols = 2 * n + 2 * m
    a0 = 2 * n + m
    T = []
    for i in range(m):
        row = [Q(0)] * ncols
        for j in range(n):
            c = C[i][j] * sigma[i]
            row[j] = c
            row[n + j] = -c
        row[2 * n + i] = Q(-sigma[i])
        row[a0 + i] = Q(1)
        T.append(row)
    rhs = [abs(d[i]) for i in range(m)]
    basis = [a0 + i for i in range(m)]
    # reduced costs, cost 1 on artificials, basis = all artificials
    rc = [Q(0)] * ncols
    for j in range(a0):
        rc[j] = -sum(T[i][j] for i in range(m))
    obj = sum(rhs)

    # Pivot rule. rule="bland": Bland's rule throughout (smallest-index entering variable and
    # smallest-index tie-break on leaving), which cannot cycle. rule="hybrid" (default): Dantzig,
    # with a switch to Bland after `stall_limit` consecutive degenerate pivots, back to Dantzig
    # after a strictly improving pivot. Termination argument for the hybrid:
    #   * a degenerate pivot (ratio 0) leaves the objective unchanged, a strict pivot lowers it;
    #   * a cycle of bases has constant objective, so it consists only of degenerate pivots and the
    #     counter is never reset while it runs; after at most `stall_limit` pivots Bland is on;
    #   * Bland never cycles, so it leaves the degenerate vertex set by a strict pivot or stops;
    #   * each strict pivot lowers the objective, so no basis seen before a strict pivot can recur;
    #     there are finitely many bases, hence finitely many strict pivots.
    # Cycle length < stall_limit is therefore not a hole. Regardless, max_pivots bounds every run
    # and exhaustion is SOLVER_FAILURE, never NO.
    if rule not in ("hybrid", "bland"):
        return FAIL, f"unknown pivot rule {rule!r}", {}
    pivots = degenerate_run = 0
    bland = rule == "bland"
    stats = {}
    while True:
        # entering variable
        ent = -1
        if bland:
            for j in range(ncols):
                if rc[j] < 0:
                    ent = j; break
        else:
            best = Q(0)
            for j in range(ncols):
                if rc[j] < best:
                    best, ent = rc[j], j
        if ent < 0:
            break  # optimal
        if (pivots >= max_pivots
                or (time_limit is not None and time.monotonic() - t0 >= time_limit)):
            return FAIL, "resource limit (pivots/time)", {"pivots": pivots}
        # ratio test, ties -> smallest basic variable index
        lv, ratio = -1, None
        for i in range(m):
            a = T[i][ent]
            if a > 0:
                r = rhs[i] / a
                if ratio is None or r < ratio or (r == ratio and basis[i] < basis[lv]):
                    lv, ratio = i, r
        if lv < 0:
            # cannot happen in Phase I (objective bounded below by 0)
            return FAIL, "unbounded Phase I (internal error)", {"pivots": pivots}
        # pivot
        p = T[lv][ent]
        prow = [x / p for x in T[lv]]
        prhs = rhs[lv] / p
        nz = [j for j, x in enumerate(prow) if x != 0]
        T[lv], rhs[lv] = prow, prhs
        for i in range(m):
            if i != lv:
                f = T[i][ent]
                if f != 0:
                    row = T[i]
                    for j in nz:
                        row[j] -= f * prow[j]
                    rhs[i] -= f * prhs
        f = rc[ent]
        for j in nz:
            rc[j] -= f * prow[j]
        obj += f * prhs            # f<0, so obj decreases by |f|*prhs
        basis[lv] = ent
        pivots += 1
        if rule == "hybrid":
            if ratio == 0:
                degenerate_run += 1
                if degenerate_run >= stall_limit:
                    bland = True
            else:
                degenerate_run, bland = 0, False

    stats = {"pivots": pivots, "bland_used": bland}
    if obj == 0:
        x = [Q(0)] * ncols
        for i in range(m):
            x[basis[i]] = rhs[i]
        b = [x[j] - x[n + j] for j in range(n)]
        return YES, b, stats
    y = [1 - rc[a0 + i] for i in range(m)]
    lam = [sigma[i] * y[i] for i in range(m)]
    return NO, lam, stats


def solve_and_verify(C, d, m, n, **kw):
    """Solve, then check with the exact verifier. A certificate that fails
    verification is a SOLVER_FAILURE, never a verdict."""
    status, payload, stats = solve(C, d, m, n, **kw)
    if status == YES and not verify_yes(C, d, m, n, payload):
        return FAIL, "YES witness failed verification", stats
    if status == NO and not verify_no(C, d, m, n, payload):
        return FAIL, "NO certificate failed verification", stats
    return status, payload, stats


# ---------- JSON CLI ----------
def load(path):
    with open(path) as f:
        return parse_system(json.load(f))

def parse_system(j):
    if not isinstance(j, dict) or not {"m", "n", "C", "d"} <= j.keys():
        raise InputError("expected object with keys m, n, C, d")
    m, n = j["m"], j["n"]
    if not (_is_dim(m) and _is_dim(n)):
        raise InputError("m and n must be nonnegative integers")
    if not (isinstance(j["C"], list) and all(isinstance(r, list) for r in j["C"])
            and isinstance(j["d"], list)):
        raise InputError("C must be a list of lists, d a list")
    C = [[parse_q(x) for x in r] for r in j["C"]]
    d = [parse_q(x) for x in j["d"]]
    return C, d, m, n

def dump_result(status, payload, stats, m, n):
    out = {"status": status, "m": m, "n": n, "stats": stats}
    if status == YES:
        out["b"] = [fmt_q(x) for x in payload]
    elif status == NO:
        out["lambda"] = [fmt_q(x) for x in payload]
    else:
        out["reason"] = payload     # NOT a mathematical verdict
    return out

if __name__ == "__main__":
    try:
        C, d, m, n = load(sys.argv[1])
    except (InputError, OSError, json.JSONDecodeError) as e:
        # malformed input is a failure to run, never a verdict
        print(json.dumps({"status": FAIL, "reason": f"invalid input: {e}"}, indent=1))
        sys.exit(2)
    s, p, st = solve_and_verify(C, d, m, n)
    print(json.dumps(dump_result(s, p, st, m, n), indent=1))
    sys.exit({YES: 0, NO: 0, FAIL: 2}[s])
