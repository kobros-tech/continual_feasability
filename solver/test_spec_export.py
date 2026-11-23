import json, os, random, sys
from fractions import Fraction as Q
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exact_solver import solve_and_verify, YES, NO
from spec_export import *

def rand_spec(rng):
    p, K, T = rng.randint(1, 3), rng.randint(1, 4), rng.randint(1, 3)
    N = rng.randint(1, 4)
    ct = [rng.randint(0, T) for _ in range(K)]
    y = [rng.randrange(K) for _ in range(N)]
    et = [ct[y[e]] for e in range(N)]
    return dict(p=p, K=K, T=T, N=N, ct=ct,
                W0=[[Q(rng.randint(-2, 2)) for _ in range(p)] for _ in range(K)],
                x=[[Q(rng.randint(-2, 2)) for _ in range(p)] for _ in range(N)],
                y=y, et=et, isRef=[rng.random() < 0.6 for _ in range(N)],
                gamma=Q(rng.choice([1, 2, 1])))

def test_shape_matches_lean_counts():
    rng = random.Random(0)
    for _ in range(100):
        S = rand_spec(rng)
        C, d, m, n = export_system(S)
        assert m == expected_m(S) and n == (S["T"] + 1) * S["K"] * S["p"]
        assert len(C) == len(d) == m and all(len(r) == n for r in C)

def test_rows_equal_semantics_on_random_W():
    """Python analogue of `feasible_iff` + `coef_dot`: rows satisfied <=> Feasible, for all W."""
    rng = random.Random(1)
    hits = [0, 0]
    for _ in range(400):
        S = rand_spec(rng)
        C, d, m, n = export_system(S)
        st, pay, _ = solve_and_verify(C, d, m, n)
        cands = []
        if st == YES:
            cands.append(pay)
            for _ in range(3):                       # perturbed witnesses
                b = list(pay); b[rng.randrange(n)] += rng.choice([-1, 1, Q(1, 2)]); cands.append(b)
        for _ in range(4):                           # random vectors
            cands.append([Q(rng.randint(-2, 2)) for _ in range(n)])
        for b in cands:
            a = rows_satisfied(C, d, b); s = semantic_feasible(S, unflat(b, S))
            assert a == s, (S, b)
            hits[a] += 1
    assert hits[0] > 100 and hits[1] > 50, hits       # both outcomes exercised

def test_decision_agrees_on_random_specs():
    """Feasible (by direct search for a witness) iff exporter system is YES, certified either way."""
    rng = random.Random(2)
    ny = nn = 0
    for _ in range(300):
        S = rand_spec(rng)
        C, d, m, n = export_system(S)
        st, pay, _ = solve_and_verify(C, d, m, n)
        assert st in (YES, NO)
        if st == YES:
            assert semantic_feasible(S, unflat(pay, S)); ny += 1
        else:
            nn += 1
    assert ny > 30 and nn > 30, (ny, nn)

def test_parse_spec_rejects():
    good = dict(p=1, K=2, T=1, N=2, ct=[0, 1], W0=[[1], [0]], x=[[1], [1]], y=[0, 1],
                et=[0, 1], isRef=[True, False], gamma=1)
    parse_spec(good)
    from exact_solver import InputError
    for bad in [dict(good, gamma=0), dict(good, gamma=0.5), dict(good, isRef=[1, 0]),
                dict(good, et=[1, 1]),                     # violates hy
                dict(good, ct=[0, 5]), dict(good, p=True), dict(good, x=[[1], [1, 1]])]:
        try: parse_spec(bad)
        except InputError: continue
        raise AssertionError(bad)

def test_committed_speccerts_is_current():
    import spec_pipeline
    text, report, _ = spec_pipeline.build()
    assert os.path.exists(spec_pipeline.OUT), "run python3 solver/spec_pipeline.py"
    assert open(spec_pipeline.OUT).read() == text, "SpecCerts.lean is stale"
    st = {n: s for n, s, *_ in report}
    assert set(st.values()) == {YES, NO}
    body = text.split("-/", 1)[1]
    assert "native_decide" not in body and "sorry" not in body

if __name__ == "__main__":
    fails = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            try: f(); print("ok  ", k)
            except AssertionError as e: fails += 1; print("FAIL", k, e)
    sys.exit(fails)
