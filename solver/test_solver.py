import random, itertools
from fractions import Fraction as Q
from exact_solver import *

def mk(C, d): return [[Q(x) for x in r] for r in C], [Q(x) for x in d], len(C), len(C[0]) if C else 0

def test_yes_known():
    C, d, m, n = mk([[1, 0], [0, 1], [1, 1]], [1, 1, 2])
    s, b, _ = solve_and_verify(C, d, m, n)
    assert s == YES and verify_yes(C, d, m, n, b)

def test_no_known():            # b>=1 and -b>=0
    C, d, m, n = mk([[1], [-1]], [1, 0])
    s, lam, _ = solve_and_verify(C, d, m, n)
    assert s == NO and verify_no(C, d, m, n, lam)

def test_zero_row():            # 0>=0 feasible, 0>=1 infeasible
    assert solve_and_verify(*mk([[0, 0]], [0]))[0] == YES
    assert solve_and_verify(*mk([[0, 0]], [1]))[0] == NO

def test_free_negative_witness():   # forces b<0 (needs u/v split)
    C, d, m, n = mk([[-1]], [3])
    s, b, _ = solve_and_verify(C, d, m, n)
    assert s == YES and b[0] <= -3

def test_empty_rows():
    assert solve_and_verify([], [], 0, 3)[0] == YES

def test_resource_failure_is_not_no():
    # needs pivots, and is feasible: pivot limit 0 must be SOLVER_FAILURE
    C, d, m, n = mk([[1, 0], [0, 1], [1, 1]], [1, 1, 2])
    s, why, _ = solve_and_verify(C, d, m, n, max_pivots=0)
    assert s == FAIL and "resource" in why
    # needs pivots, and is infeasible: still FAIL, never a bare NO
    C, d, m, n = mk([[1, 0], [-1, 0], [0, 1], [0, -1]], [1, -3, 1, 0])
    assert solve_and_verify(C, d, m, n)[0] == NO            # sanity: it is NO
    s, why, st = solve_and_verify(C, d, m, n, max_pivots=0)
    assert st["pivots"] == 0                                # really needed a pivot
    assert s == FAIL and "resource" in why

def test_zero_time_limit_is_a_limit():
    C, d, m, n = mk([[1, 0], [0, 1], [1, 1]], [1, 1, 2])    # needs a pivot
    s, why, _ = solve_and_verify(C, d, m, n, time_limit=0)
    assert s == FAIL and "resource" in why
    C, d, m, n = mk([[1, 0], [-1, 0], [0, 1], [0, -1]], [1, -3, 1, 0])
    assert solve_and_verify(C, d, m, n, time_limit=0)[0] == FAIL
    # no time limit at all still solves
    assert solve_and_verify(C, d, m, n, time_limit=None)[0] == NO

def test_already_optimal_needs_no_pivot():
    # honest boundary: a limit is only consulted when a pivot is required
    C, d, m, n = mk([[1], [-1]], [1, 0])
    assert solve_and_verify(C, d, m, n, max_pivots=0, time_limit=0)[0] == NO

def test_malformed():
    assert solve_and_verify([[Q(1)]], [Q(1), Q(2)], 1, 1)[0] == FAIL
    assert solve_and_verify([[Q(1), Q(1)], [Q(1)]], [Q(0), Q(0)], 2, 2)[0] == FAIL

def test_tampered_certificates_rejected():
    C, d, m, n = mk([[1], [-1]], [1, 0])
    s, lam, _ = solve_and_verify(C, d, m, n)
    assert not verify_no(C, d, m, n, [l + 1 for l in lam][:1] + lam[1:])
    assert not verify_no(C, d, m, n, [-l for l in lam])
    assert not verify_yes(C, d, m, n, [Q(0)])

def brute_feasible_2var(C, d):
    # independent oracle for n<=2: LP vertex check via all pairs of tight rows
    # TEST ORACLE ONLY, n<=2, bounded-box trick (|b|<=10^6): valid for the small
    # bounded-coefficient instances generated below, NOT a general LP oracle.
    # (feasible region of a feasibility system is nonempty iff it contains a
    #  point of the arrangement or is unbounded in a lineality direction;
    #  we use a bounded box trick to stay exact)
    m = len(C)
    rows = [(C[i], d[i]) for i in range(m)]
    BIG = Q(10**6)
    box = [([1, 0], -BIG), ([-1, 0], -BIG), ([0, 1], -BIG), ([0, -1], -BIG)]
    allr = rows + [([Q(a) for a in r], Q(c)) for r, c in box]
    for (r1, c1), (r2, c2) in itertools.combinations(allr, 2):
        det = r1[0]*r2[1] - r1[1]*r2[0]
        if det == 0: continue
        x = (c1*r2[1] - c2*r1[1]) / det
        y = (r1[0]*c2 - r2[0]*c1) / det
        if all(r[0]*x + r[1]*y >= c for r, c in allr):
            return True
    return False

def test_random_vs_oracle_and_exclusivity():
    rng = random.Random(0)
    yes = no = bland = 0
    for _ in range(1500):
        m = rng.randint(1, 7)
        C = [[Q(rng.randint(-2, 2)) for _ in range(2)] for _ in range(m)]
        d = [Q(rng.randint(-3, 3), rng.randint(1, 3)) for _ in range(m)]
        s, p, st = solve_and_verify(C, d, m, 2)
        assert s in (YES, NO), (C, d, s, p)
        # exact verifier already ran inside; cross-check against the oracle
        assert (s == YES) == brute_feasible_2var(C, d), (C, d, s)
        yes += s == YES; no += s == NO; bland += bool(st.get("bland_used"))
    assert yes > 100 and no > 100

def test_random_larger_degenerate():
    rng = random.Random(1)
    for _ in range(150):
        m, n = rng.randint(5, 14), rng.randint(3, 8)
        C = [[Q(rng.choice([-1, 0, 0, 1])) for _ in range(n)] for _ in range(m)]
        d = [Q(rng.choice([0, 0, 0, 1])) for _ in range(m)]
        s, p, _ = solve_and_verify(C, d, m, n, stall_limit=3)   # force Bland paths
        assert s in (YES, NO), (s, p)

def test_planted_feasible_always_yes():
    rng = random.Random(2)
    for _ in range(100):
        m, n = rng.randint(4, 12), rng.randint(2, 6)
        b0 = [Q(rng.randint(-3, 3)) for _ in range(n)]
        C = [[Q(rng.randint(-3, 3)) for _ in range(n)] for _ in range(m)]
        d = [sum(C[i][j]*b0[j] for j in range(n)) - rng.randint(0, 2) for i in range(m)]
        assert solve_and_verify(C, d, m, n)[0] == YES

def test_greedy_trap_shape():
    # joint YES though a bad early choice kills the next step: x1 free, 
    # step2 needs x2 >= 1 - x1 ... and x1 <= 0 is a valid first-step choice
    # (here: feasible jointly, infeasible once x1 is pinned to 5 with x2 <= -x1)
    C, d, m, n = mk([[1, 0], [1, 1], [-1, -1]], [0, 1, -3])
    assert solve_and_verify(C, d, m, n)[0] == YES
    Cp, dp, mp, np_ = mk([[1, 0], [-1, 0], [1, 1], [-1, -1]], [5, -5, 1, -3 + 4])
    assert solve_and_verify(Cp, dp, mp, np_)[0] == NO   # pinned b1=5, b1+b2>=1 and <=-1

def test_bland_only_rule_agrees_and_is_verified():
    rng = random.Random(7)
    for _ in range(400):
        m, n = rng.randint(1, 10), rng.randint(1, 5)
        C = [[Q(rng.choice([-2, -1, 0, 0, 1, 2])) for _ in range(n)] for _ in range(m)]
        d = [Q(rng.choice([-1, 0, 0, 1, 2])) for _ in range(m)]
        sb = solve_and_verify(C, d, m, n, rule="bland")
        sh = solve_and_verify(C, d, m, n, rule="hybrid", stall_limit=1)
        sd = solve_and_verify(C, d, m, n, rule="hybrid", stall_limit=50)
        assert sb[0] in (YES, NO) and sh[0] in (YES, NO) and sd[0] in (YES, NO)
        assert sb[0] == sh[0] == sd[0], (C, d)       # feasibility is rule-independent (exclusivity)

def test_unknown_rule_is_failure_not_verdict():
    C, d, m, n = mk([[1], [-1]], [1, 0])
    assert solve_and_verify(C, d, m, n, rule="dantzig_forever")[0] == FAIL

import json, os, tempfile, subprocess, sys

def _run_cli(obj):
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
        json.dump(obj, f)
    r = subprocess.run([sys.executable, os.path.join(os.path.dirname(__file__), "exact_solver.py"), f.name],
                       capture_output=True, text=True)
    os.unlink(f.name)
    return r.returncode, json.loads(r.stdout)

def test_parse_q_strict():
    assert parse_q(3) == 3 and parse_q("1/10") == Q(1, 10) and parse_q("-7") == -7
    for bad in [0.1, 1.0, True, False, None, "0.1", "1e3", "1/0", "", " ", "1/-2", "a", [1]]:
        try: parse_q(bad)
        except InputError: continue
        raise AssertionError(f"accepted {bad!r}")

def test_cli_rejects_bad_input():
    good = {"m": 1, "n": 1, "C": [[1]], "d": ["1/10"]}
    rc, out = _run_cli(good); assert rc == 0 and out["status"] == YES
    for bad in [dict(good, d=[0.1]), dict(good, m=True), dict(good, n=-1),
                dict(good, m=1.0), dict(good, C=[1]), {"m": 1}, [1, 2]]:
        rc, out = _run_cli(bad)
        assert rc == 2 and out["status"] == FAIL and "invalid input" in out["reason"], (bad, out)

def test_api_rejects_floats_and_bad_dims():
    assert solve_and_verify([[0.1]], [Q(0)], 1, 1)[0] == FAIL
    assert solve_and_verify([[Q(1)]], [Q(0)], True, 1)[0] == FAIL
    assert solve_and_verify([[Q(1)]], [Q(0)], 1, -1)[0] == FAIL
    assert not verify_yes([[Q(1)]], [Q(0)], 1, 1, [0.5])


def test_lean_literals():
    import pipeline
    assert pipeline.lq(Q(3)) == "3" and pipeline.lq(Q(-3)) == "-3"
    assert pipeline.lq(Q(1, 3)) == "(1/3)" and pipeline.lq(Q(-1, 3)) == "(-1/3)"
    assert pipeline.larr([Q(1), Q(-1, 2)]) == "#[1, (-1/2)]"
    assert pipeline.lmat([[Q(1)], [Q(0)]]) == "#[#[1], #[0]]"

def test_pipeline_cases_and_no_theorem_for_failure():
    import pipeline
    text, report, nthm = pipeline.build()
    st = {n: s for n, s, _ in report}
    assert st["limit_failure"] == FAIL
    assert "limit_failure_accepted" not in text and "s_limit_failure" not in text
    assert "SOLVER_FAILURE" in text and nthm > 50
    import re as _re
    for m_ in _re.finditer(r"theorem (\w+) : (\w+) (\w+) (.*) = (true|false) :=", text):
        nm, _chk, _sys, _cert, val = m_.groups()
        if nm.endswith("_rejected"):    assert val == "false", nm
        if nm.endswith("_still_valid"): assert val == "true", nm
    for n_, s_, _ in report:
        if s_ in (YES, NO):
            kind = "checkYes" if s_ == YES else "checkNo"
            assert _re.search(rf"theorem {n_}_len_plus_rejected : {kind} .* = false", text), n_
            assert _re.search(rf"theorem {n_}_(ones_as_no|zeros_as_yes)_rejected", text), n_
    body = text.split("-/", 1)[1]            # skip the header comment, which names native_decide
    assert "native_decide" not in body and "sorry" not in body and "axiom" not in body.replace("#print axioms", "")

def test_committed_certs_lean_is_current():
    import pipeline
    text, _, _ = pipeline.build()
    assert os.path.exists(pipeline.OUT), "run python3 solver/pipeline.py"
    assert open(pipeline.OUT).read() == text, "Certs.lean is stale"


if __name__ == "__main__":
    import sys
    fails = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            try: f(); print("ok  ", k)
            except AssertionError as e: fails += 1; print("FAIL", k, e)
    sys.exit(fails)
