"""
Stage 3c (Python side, UNTRUSTED): sequential Spec -> dense system C b >= d, with the SAME
enumeration as ContinualFeasibility/Export.lean, plus a direct semantic checker of Feasible.

The Lean file `SpecCerts.lean` compares this exporter with the Lean `exportSys` on each concrete
spec (`ArrSys.beq ... = true` by `decide +kernel`); the Lean theorems `exportSys_encodes`,
`export_feasible_iff`, `export_infeasible_iff` are what make that exporter correct in general.

Enumeration (must match Export.lean):
  variables  W t k j     -> index (t*K + k)*p + j
  rows       blocks Z, I, P, N, O in this order; inside a block lexicographic in the components of
             the Lean index type, Bool as false=0, true=1 (so sign -1 first, then +1):
               Z (t,k,j,s)  I (k,j,s)  P (t,e,k,s)  N (e,k)  O (t,e,k)
"""
from fractions import Fraction as Q
from exact_solver import parse_q, InputError

SPEC_KEYS = {"p", "K", "T", "N", "ct", "W0", "x", "y", "et", "isRef", "gamma"}


def _dim(v, name, lo=0):
    if isinstance(v, bool) or not isinstance(v, int) or v < lo:
        raise InputError(f"{name} must be an integer >= {lo}")
    return v

def parse_spec(j):
    if not isinstance(j, dict) or not SPEC_KEYS <= j.keys():
        raise InputError(f"spec needs keys {sorted(SPEC_KEYS)}")
    p, K, T, N = (_dim(j[k], k, 1 if k != "T" else 1) for k in ("p", "K", "T", "N"))
    ct = [_dim(v, "ct") for v in j["ct"]]
    y = [_dim(v, "y") for v in j["y"]]
    et = [_dim(v, "et") for v in j["et"]]
    if not (len(ct) == K and len(y) == N and len(et) == N and len(j["isRef"]) == N):
        raise InputError("shape mismatch in ct/y/et/isRef")
    if not all(c <= T for c in ct) or not all(e <= T for e in et) or not all(v < K for v in y):
        raise InputError("index out of range")
    isRef = []
    for v in j["isRef"]:
        if not isinstance(v, bool):
            raise InputError("isRef entries must be booleans")
        isRef.append(v)
    W0 = [[parse_q(v) for v in r] for r in j["W0"]]
    x = [[parse_q(v) for v in r] for r in j["x"]]
    if not (len(W0) == K and all(len(r) == p for r in W0)
            and len(x) == N and all(len(r) == p for r in x)):
        raise InputError("shape mismatch in W0/x")
    gamma = parse_q(j["gamma"])
    if gamma <= 0:
        raise InputError("gamma must be > 0")
    if any(ct[y[e]] != et[e] for e in range(N)):          # Spec.hy
        raise InputError("hy violated: ct (y e) must equal et e")
    return dict(p=p, K=K, T=T, N=N, ct=ct, W0=W0, x=x, y=y, et=et, isRef=isRef, gamma=gamma)


def export_system(S):
    """Returns (C, d, m, n)."""
    p, K, T, N = S["p"], S["K"], S["T"], S["N"]
    ct, W0, x, y, et, isRef, g = (S[k] for k in ("ct", "W0", "x", "y", "et", "isRef", "gamma"))
    n = (T + 1) * K * p
    v = lambda t, k, j: (t * K + k) * p + j
    sg = lambda s: Q(1) if s else Q(-1)
    rows, rhs = [], []

    def add(coefs, r):
        row = [Q(0)] * n
        for idx, c in coefs:
            row[idx] += c
        rows.append(row); rhs.append(Q(r))

    for t in range(T + 1):                                # (Z)
        for k in range(K):
            for j in range(p):
                for s in (False, True):
                    add([(v(t, k, j), sg(s))] if t < ct[k] else [], 0)
    for k in range(K):                                    # (I)
        for j in range(p):
            for s in (False, True):
                if ct[k] == 0:
                    add([(v(0, k, j), sg(s))], sg(s) * W0[k][j])
                else:
                    add([], 0)
    for t in range(T + 1):                                # (P)
        for e in range(N):
            for k in range(K):
                for s in (False, True):
                    if isRef[e] and et[e] < t and ct[k] < t:
                        add([(v(t, k, j), sg(s) * x[e][j]) for j in range(p)] +
                            [(v(t - 1, k, j), -sg(s) * x[e][j]) for j in range(p)], 0)
                    else:
                        add([], 0)
    for e in range(N):                                    # (N)
        for k in range(K):
            if 0 < et[e] and k != y[e] and ct[k] <= et[e]:
                t = et[e]
                add([(v(t, y[e], j), x[e][j]) for j in range(p)] +
                    [(v(t, k, j), -x[e][j]) for j in range(p)], g)
            else:
                add([], 0)
    for t in range(T + 1):                                # (O)
        for e in range(N):
            for k in range(K):
                if isRef[e] and et[e] < t and ct[k] == t:
                    add([(v(t, y[e], j), x[e][j]) for j in range(p)] +
                        [(v(t, k, j), -x[e][j]) for j in range(p)], g)
                else:
                    add([], 0)
    return rows, rhs, len(rows), n


def expected_m(S):
    p, K, T, N = S["p"], S["K"], S["T"], S["N"]
    return ((T + 1) * (K * (p * 2)) + K * (p * 2) + (T + 1) * (N * (K * 2))
            + N * K + (T + 1) * (N * K))


def unflat(b, S):
    p, K, T = S["p"], S["K"], S["T"]
    return [[[b[(t * K + k) * p + j] for j in range(p)] for k in range(K)] for t in range(T + 1)]


def semantic_feasible(S, W):
    """Direct transcription of `Feasible` (zero, init, pres, new, old). W[t][k][j]."""
    p, K, T, N = S["p"], S["K"], S["T"], S["N"]
    ct, W0, x, y, et, isRef, g = (S[k] for k in ("ct", "W0", "x", "y", "et", "isRef", "gamma"))
    logit = lambda t, e, k: sum(x[e][j] * W[t][k][j] for j in range(p))
    for t in range(T + 1):
        for k in range(K):
            if t < ct[k] and any(W[t][k][j] != 0 for j in range(p)):
                return False
    for k in range(K):
        if ct[k] == 0 and any(W[0][k][j] != W0[k][j] for j in range(p)):
            return False
    for t in range(T + 1):
        for e in range(N):
            for k in range(K):
                if isRef[e] and et[e] < t and ct[k] < t and logit(t, e, k) != logit(t - 1, e, k):
                    return False
                if isRef[e] and et[e] < t and ct[k] == t and \
                        g > logit(t, e, y[e]) - logit(t, e, k):
                    return False
    for e in range(N):
        for k in range(K):
            if 0 < et[e] and k != y[e] and ct[k] <= et[e] and \
                    g > logit(et[e], e, y[e]) - logit(et[e], e, k):
                return False
    return True


def rows_satisfied(C, d, b):
    return all(sum(c * z for c, z in zip(r, b)) >= di for r, di in zip(C, d))
