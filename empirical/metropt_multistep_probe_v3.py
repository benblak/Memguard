#!/usr/bin/env python3
from __future__ import annotations

import json
import math
import os
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.preprocessing import StandardScaler

import metropt_direct_actionability_v2 as v2

SEED = 20260914
np.random.seed(SEED)
OUT = Path(os.environ.get('INSACERMO_OUT', 'empirical/metropt_multistep_v3_results'))
OUT.mkdir(parents=True, exist_ok=True)
MAX_PROBES = 4
SHORTLIST = 6
FIRST_SAMPLES = 48
SECOND_SAMPLES = 32


def posterior_p(score: float) -> float:
    z = max(min(float(score), 40.0), -40.0)
    return 1.0 / (1.0 + math.exp(-z))


def deterministic_sample(a: np.ndarray, n: int) -> np.ndarray:
    if len(a) == 0:
        return np.zeros(1, dtype=float)
    a = np.sort(np.asarray(a, dtype=float))
    if len(a) <= n:
        return a
    q = (np.arange(n) + 0.5) / n
    idx = np.minimum((q * len(a)).astype(int), len(a) - 1)
    return a[idx]


def build_pools(y, cal_mask, evid):
    pools = {}
    for g, ev in evid.items():
        pools[g] = {
            0: deterministic_sample(ev[cal_mask & (y == 0)], SECOND_SAMPLES),
            1: deterministic_sample(ev[cal_mask & (y == 1)], SECOND_SAMPLES),
            'first0': deterministic_sample(ev[cal_mask & (y == 0)], FIRST_SAMPLES),
            'first1': deterministic_sample(ev[cal_mask & (y == 1)], FIRST_SAMPLES),
        }
    return pools


def terminal_prob(score: float, g: str, pools, low: float, high: float) -> float:
    p1 = posterior_p(score)
    e0 = pools[g][0]
    e1 = pools[g][1]
    r0 = float(np.mean((score + e0 <= low) | (score + e0 >= high)))
    r1 = float(np.mean((score + e1 <= low) | (score + e1 >= high)))
    return (1.0 - p1) * r0 + p1 * r1


def myopic_rank(score, remaining, pools, low, high):
    vals = [(terminal_prob(score, g, pools, low, high), g) for g in remaining]
    vals.sort(key=lambda x: (-x[0], x[1]))
    return vals


def two_step_value(score: float, g: str, remaining: list[str], pools, low: float, high: float) -> float:
    p1 = posterior_p(score)
    branches = [(1.0 - p1, pools[g]['first0']), (p1, pools[g]['first1'])]
    rem2 = [h for h in remaining if h != g]
    total = 0.0
    for wcls, arr in branches:
        if wcls <= 0 or len(arr) == 0:
            continue
        branch_sum = 0.0
        for e in arr:
            s1 = score + float(e)
            if s1 <= low or s1 >= high:
                branch_sum += 1.0
            elif rem2:
                ranked = myopic_rank(s1, rem2, pools, low, high)
                branch_sum += ranked[0][0]
        total += wcls * branch_sum / len(arr)
    return float(total)


def choose_multistep(score: float, remaining: list[str], pools, low: float, high: float):
    my = myopic_rank(score, remaining, pools, low, high)
    shortlist = [g for _, g in my[:min(SHORTLIST, len(my))]]
    vals = [(two_step_value(score, g, remaining, pools, low, high), g) for g in shortlist]
    vals.sort(key=lambda x: (-x[0], x[1]))
    return vals[0][1], vals, my


def choose_myopic(score: float, remaining: list[str], pools, low: float, high: float):
    ranked = myopic_rank(score, remaining, pools, low, high)
    return ranked[0][1]


def diagnostic_two_real(score, remaining, first_g, row, truth, evid, pools, low, high):
    s1 = score + float(evid[first_g][row])
    a1 = v2.act_from_score(s1, low, high, 1, require_probe=True)
    if a1 is not None:
        return bool(v2.correct_act(a1, truth))
    rem = [g for g in remaining if g != first_g]
    if not rem:
        return False
    second_g, _, _ = choose_multistep(s1, rem, pools, low, high)
    s2 = s1 + float(evid[second_g][row])
    a2 = v2.act_from_score(s2, low, high, 2, require_probe=True)
    return bool(a2 is not None and v2.correct_act(a2, truth))


def run_adaptive(kind, rows, y, evid, groups, prior_logodds, low, high, pools):
    records = []
    events = []
    all_groups = list(groups)
    for i in rows:
        truth = int(y[i])
        score = prior_logodds
        remaining = list(all_groups)
        probes = 0
        terminal = None
        while probes < MAX_PROBES and remaining:
            if kind == 'MULTISTEP_VOI_PROBE':
                g, _, _ = choose_multistep(score, remaining, pools, low, high)
            elif kind == 'MYOPIC_CONTRACT_PROBE':
                g = choose_myopic(score, remaining, pools, low, high)
            else:
                raise ValueError(kind)

            immediate = []
            for cand in remaining:
                s2 = score + float(evid[cand][i])
                a2 = v2.act_from_score(s2, low, high, probes + 1, require_probe=True)
                immediate.append(bool(a2 is not None and v2.correct_act(a2, truth)))

            chosen_two = diagnostic_two_real(score, remaining, g, i, truth, evid, pools, low, high)
            if kind == 'MULTISTEP_VOI_PROBE':
                all_two = [diagnostic_two_real(score, remaining, cand, i, truth, evid, pools, low, high) for cand in remaining]
                random_two = float(np.mean(all_two))
            else:
                random_two = float('nan')

            chosen_idx = remaining.index(g)
            events.append({
                'row': int(i), 'truth': truth, 'policy': kind, 'probe_number': probes + 1,
                'chosen_group': g,
                'chosen_immediate_correct_resolution': bool(immediate[chosen_idx]),
                'random_available_immediate_correct_fraction': float(np.mean(immediate)),
                'chosen_two_real_probe_correct_resolution': bool(chosen_two),
                'random_first_then_policy_two_probe_correct_fraction': random_two,
                'available_groups': len(remaining),
            })

            score += float(evid[g][i])
            probes += 1
            remaining.remove(g)
            terminal = v2.act_from_score(score, low, high, probes, require_probe=True)
            if terminal is not None:
                break
        if terminal is None:
            terminal = 'REFUSE'
        records.append((i, terminal, probes, score))
    return records, events


def main():
    print('[1/8] Load official MetroPT-3 and reproduce V2 contract', flush=True)
    raw, archive_sha, _ = v2.load_raw()
    feat, feature_cols = v2.engineer_5min(raw)
    del raw
    index = pd.DatetimeIndex(feat.index)
    train_mask, cal_mask, test_mask = v2.masks(index)
    y, excluded, _ = v2.warning_labels(index)
    X = feat[feature_cols].to_numpy(float)
    Xz = StandardScaler().fit(X[train_mask]).transform(X)
    groups = v2.sensor_groups(feature_cols)
    fit_nb = cal_mask & (~excluded)
    prior, prior_logodds, _, evid = v2.fit_nb_evidence(Xz, y, fit_nb, groups)
    full_score = prior_logodds + np.sum(np.column_stack([evid[g] for g in groups]), axis=1)
    q_pos5 = float(np.quantile(full_score[fit_nb & (y == 1)], 0.05))
    q_neg99 = float(np.quantile(full_score[fit_nb & (y == 0)], 0.99))
    low, high = min(q_pos5, q_neg99), max(q_pos5, q_neg99)
    fixed_order = v2.build_fixed_order(prior_logodds, list(groups), y, fit_nb, evid, low, high)
    pools = build_pools(y, fit_nb, evid)
    print(f'[2/8] groups={len(groups)} low={low:.6f} high={high:.6f}', flush=True)

    rows = np.where(test_mask & (~excluded))[0]
    summaries = {}
    dec_tables = []
    all_events = []

    for kind in ['MULTISTEP_VOI_PROBE', 'MYOPIC_CONTRACT_PROBE']:
        rec, ev = run_adaptive(kind, rows, y, evid, groups, prior_logodds, low, high, pools)
        sm, df = v2.summarize(rec, index, y)
        summaries[kind] = sm
        df['policy'] = kind
        dec_tables.append(df)
        all_events.extend(ev)
        print(f"[3/8] {kind}: coverage={sm['act_coverage']:.4f} refuse={sm['refuse_rate']:.4f} unsafe={sm['unsafe_act_rate_among_acts']:.4f} probes={sm['mean_probes']:.4f}", flush=True)

    for kind_v2, label in [('FIXED_ORDER_PROBE','FIXED_ORDER_PROBE'),('NO_PROBE','NO_PROBE'),('FULL_SENSOR','FULL_SENSOR')]:
        rec, _ = v2.run_policy(kind_v2, rows, y, evid, groups, prior_logodds, low, high, fit_nb, fixed_order)
        sm, df = v2.summarize(rec, index, y)
        summaries[label] = sm
        df['policy'] = label
        dec_tables.append(df)
        print(f"[4/8] {label}: coverage={sm['act_coverage']:.4f} refuse={sm['refuse_rate']:.4f} unsafe={sm['unsafe_act_rate_among_acts']:.4f} probes={sm['mean_probes']:.4f}", flush=True)

    evdf = pd.DataFrame(all_events)
    m = evdf[evdf.policy == 'MULTISTEP_VOI_PROBE']
    my = evdf[evdf.policy == 'MYOPIC_CONTRACT_PROBE']
    chosen2 = float(m.chosen_two_real_probe_correct_resolution.mean()) if len(m) else 0.0
    rand2 = float(m.random_first_then_policy_two_probe_correct_fraction.mean()) if len(m) else 0.0
    gain2 = chosen2 - rand2
    my2 = float(my.chosen_two_real_probe_correct_resolution.mean()) if len(my) else 0.0
    chosen1 = float(m.chosen_immediate_correct_resolution.mean()) if len(m) else 0.0
    rand1 = float(m.random_available_immediate_correct_fraction.mean()) if len(m) else 0.0

    M = summaries['MULTISTEP_VOI_PROBE']
    Y = summaries['MYOPIC_CONTRACT_PROBE']
    safe = M['unsafe_act_rate_among_acts'] <= Y['unsafe_act_rate_among_acts'] + 0.005
    coverage = M['act_coverage'] >= Y['act_coverage'] - 0.005
    cost = M['mean_probes'] <= Y['mean_probes'] + 0.10
    direct5 = gain2 >= 0.05
    beats_myopic = chosen2 > my2
    if safe and coverage and cost and direct5 and beats_myopic:
        verdict = 'MULTISTEP_PROBE_SUPPORT_V3'
    elif ((gain2 > 0) or beats_myopic) and M['unsafe_act_rate_among_acts'] <= Y['unsafe_act_rate_among_acts'] + 0.02:
        verdict = 'PARTIAL_MULTISTEP_SUPPORT_V3'
    else:
        verdict = 'NO_MULTISTEP_SUPPORT_V3'

    diag = {
        'multistep_probe_events': int(len(m)),
        'chosen_immediate_correct_resolution_rate': chosen1,
        'random_available_immediate_correct_fraction': rand1,
        'chosen_two_real_probe_correct_resolution_rate': chosen2,
        'random_first_then_policy_two_probe_correct_fraction': rand2,
        'two_probe_gain_vs_random_first': gain2,
        'myopic_chosen_two_real_probe_correct_resolution_rate': my2,
        'multistep_minus_myopic_two_probe': chosen2 - my2,
    }
    results = {
        'schema':'INSACERMO_METROPT_MULTISTEP_PROBE_V3',
        'status':'EXPLORATORY_NOT_BLIND',
        'dataset':{'doi':'10.24432/C5VW3R','archive_sha256':archive_sha,'valid_5min_bins':int(len(feat))},
        'frozen':{'max_probes':MAX_PROBES,'lookahead_depth':2,'shortlist':SHORTLIST,'first_samples_per_class':FIRST_SAMPLES,'second_samples_per_class':SECOND_SAMPLES},
        'thresholds':{'act_continue_max':low,'act_alert_min':high},
        'policies':summaries,
        'probe_diagnostic':diag,
        'support_components':{'safe':safe,'coverage':coverage,'cost':cost,'gain_ge_5pp':direct5,'beats_myopic':beats_myopic},
        'overall_verdict':verdict,
        'repair_scored':False,
    }
    (OUT/'METROPT_MULTISTEP_PROBE_V3_RESULTS.json').write_text(json.dumps(results, indent=2), encoding='utf-8')
    pd.concat(dec_tables, ignore_index=True).to_csv(OUT/'METROPT_MULTISTEP_PROBE_V3_DECISIONS.csv', index=False)
    evdf.to_csv(OUT/'METROPT_MULTISTEP_PROBE_V3_PROBES.csv', index=False)
    report = [
        '# INSACERMO — MetroPT-3 Multi-Step PROBE Audit V3','',f'**{verdict}**','',
        '**Status:** exploratory mechanism audit; the MetroPT holdout was already inspected in V1/V2.','',
        f"- Two-real-probe correct resolution, V3 chosen first probe: **{100*chosen2:.2f}%**",
        f"- Random-first + same V3 continuation reference: **{100*rand2:.2f}%**",
        f"- V3 gain over random first probe: **{100*gain2:.2f} percentage points**",
        f"- Myopic chosen-first two-probe resolution: **{100*my2:.2f}%**",
        f"- V3 minus myopic: **{100*(chosen2-my2):.2f} percentage points**",'',
        '## Policies'
    ]
    for k, sm in summaries.items():
        report.append(f"- {k}: ACT coverage **{100*sm['act_coverage']:.2f}%**, REFUSE **{100*sm['refuse_rate']:.2f}%**, unsafe ACT **{100*sm['unsafe_act_rate_among_acts']:.2f}%**, mean probes **{sm['mean_probes']:.2f}**, episode alerts **{sm['episode_hits']}/{sm['episode_total']}**.")
    report += ['', '## Boundary', 'V3 tests two-step contract-directed sensing only. REPAIR remains unscored because MetroPT contains no intervention counterfactuals.']
    (OUT/'METROPT_MULTISTEP_PROBE_V3_REPORT.md').write_text('\n'.join(report), encoding='utf-8')
    print('[7/8] '+verdict, flush=True)
    print(json.dumps(diag, indent=2), flush=True)
    print('[8/8] done', flush=True)

if __name__ == '__main__':
    main()
