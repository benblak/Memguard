#!/usr/bin/env python3
from __future__ import annotations

import json
import math
import os
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.preprocessing import StandardScaler

from metropt_belief_policy_audit_v1 import (
    SEED, load_raw, engineer_5min, masks, warning_labels,
    TRAIN_START, TRAIN_END, CAL_START, CAL_END, TEST_START, TEST_END,
    FAILURES, WARNING_HOURS,
)

np.random.seed(SEED)
OUT = Path(os.environ.get('INSACERMO_OUT', 'empirical/metropt_actionability_v2_results'))
OUT.mkdir(parents=True, exist_ok=True)
MAX_PROBES = 4
EPS = 1e-6


def sensor_groups(feature_cols: list[str]) -> dict[str, list[int]]:
    suffixes = ('_mean', '_std', '_min', '_max')
    groups: dict[str, list[int]] = {}
    for j, c in enumerate(feature_cols):
        base = c
        for s in suffixes:
            if c.endswith(s):
                base = c[:-len(s)]
                break
        groups.setdefault(base, []).append(j)
    return dict(sorted(groups.items()))


def fit_nb_evidence(Xz, y, fit_mask, groups):
    prior = float((y[fit_mask].sum() + 0.5) / (fit_mask.sum() + 1.0))
    prior_logodds = math.log(prior / (1.0 - prior))
    params = {}
    evid = {}
    for g, idxs in groups.items():
        Xi = Xz[:, idxs]
        p = {}
        for cls in (0, 1):
            Z = Xi[fit_mask & (y == cls)]
            mu = Z.mean(axis=0)
            var = Z.var(axis=0) + EPS
            p[cls] = (mu, var)
        params[g] = p
        mu1, v1 = p[1]
        mu0, v0 = p[0]
        ll1 = -0.5 * (((Xi - mu1) ** 2) / v1 + np.log(2 * np.pi * v1)).sum(axis=1)
        ll0 = -0.5 * (((Xi - mu0) ** 2) / v0 + np.log(2 * np.pi * v0)).sum(axis=1)
        evid[g] = ll1 - ll0
    return prior, prior_logodds, params, evid


def act_from_score(score, low, high, probes_used, require_probe=True):
    if require_probe and probes_used < 1:
        return None
    if score <= low:
        return 'ACT_CONTINUE'
    if score >= high:
        return 'ACT_ALERT'
    return None


def correct_act(action, truth):
    return (action == 'ACT_ALERT' and truth == 1) or (action == 'ACT_CONTINUE' and truth == 0)


def probe_resolution_utility(score, group, cal_y, cal_mask, evid, low, high):
    # Model-estimated probability of entering either ACT region after this probe.
    p1 = 1.0 / (1.0 + math.exp(-max(min(score, 40), -40)))
    ev = evid[group]
    e0 = ev[cal_mask & (cal_y == 0)]
    e1 = ev[cal_mask & (cal_y == 1)]
    r0 = float(np.mean((score + e0 <= low) | (score + e0 >= high))) if len(e0) else 0.0
    r1 = float(np.mean((score + e1 <= low) | (score + e1 >= high))) if len(e1) else 0.0
    return (1.0 - p1) * r0 + p1 * r1


def choose_adaptive(score, remaining, y, cal_mask, evid, low, high):
    scored = [(probe_resolution_utility(score, g, y, cal_mask, evid, low, high), g) for g in remaining]
    scored.sort(key=lambda x: (-x[0], x[1]))
    return scored[0][1], scored


def build_fixed_order(prior_logodds, groups, y, cal_mask, evid, low, high):
    scored = [(probe_resolution_utility(prior_logodds, g, y, cal_mask, evid, low, high), g) for g in groups]
    scored.sort(key=lambda x: (-x[0], x[1]))
    return [g for _, g in scored]


def run_policy(kind, rows, y, evid, groups, prior_logodds, low, high, cal_mask, fixed_order=None):
    records = []
    probe_events = []
    all_groups = list(groups)
    for i in rows:
        truth = int(y[i])
        if kind == 'NO_PROBE':
            records.append((i, 'REFUSE', 0, prior_logodds))
            continue
        if kind == 'FULL_SENSOR':
            s = prior_logodds + sum(float(evid[g][i]) for g in all_groups)
            a = act_from_score(s, low, high, len(all_groups), require_probe=False)
            records.append((i, a if a else 'REFUSE', len(all_groups), s))
            continue

        score = prior_logodds
        remaining = list(all_groups)
        probes = 0
        terminal = None
        while probes < MAX_PROBES and remaining:
            if kind == 'ADAPTIVE_CONTRACT_PROBE':
                g, _ = choose_adaptive(score, remaining, y, cal_mask, evid, low, high)
            else:
                g = next(x for x in fixed_order if x in remaining)

            # Retrospective probe-selection audit before revealing chosen group.
            correct_options = []
            for cand in remaining:
                s2 = score + float(evid[cand][i])
                a2 = act_from_score(s2, low, high, probes + 1, require_probe=True)
                correct_options.append(bool(a2 is not None and correct_act(a2, truth)))
            chosen_idx = remaining.index(g)
            probe_events.append({
                'row': int(i), 'truth': truth, 'policy': kind, 'probe_number': probes + 1,
                'chosen_group': g,
                'chosen_immediate_correct_resolution': bool(correct_options[chosen_idx]),
                'any_immediate_correct_resolution': bool(any(correct_options)),
                'random_available_correct_resolution_fraction': float(np.mean(correct_options)),
                'available_groups': len(remaining),
            })

            score += float(evid[g][i])
            probes += 1
            remaining.remove(g)
            terminal = act_from_score(score, low, high, probes, require_probe=True)
            if terminal is not None:
                break
        if terminal is None:
            terminal = 'REFUSE'
        records.append((i, terminal, probes, score))
    return records, probe_events


def summarize(records, index, y):
    df = pd.DataFrame(records, columns=['row','decision','probes','score'])
    truth = y[df.row.to_numpy()]
    act = df.decision != 'REFUSE'
    unsafe = np.zeros(len(df), dtype=bool)
    unsafe[(df.decision == 'ACT_ALERT').to_numpy() & (truth == 0)] = True
    unsafe[(df.decision == 'ACT_CONTINUE').to_numpy() & (truth == 1)] = True
    pos = truth == 1
    neg = truth == 0
    alert = (df.decision == 'ACT_ALERT').to_numpy()
    episodes = []
    for start, end, name in FAILURES:
        if not (TEST_START <= start <= TEST_END):
            continue
        times = index[df.row.to_numpy()]
        m = (times >= start - pd.Timedelta(hours=WARNING_HOURS)) & (times < start)
        hit = bool(np.any(m & alert))
        episodes.append({'episode': name, 'hit': hit})
    return {
        'n': int(len(df)),
        'act_coverage': float(act.mean()),
        'refuse_rate': float((~act).mean()),
        'unsafe_act_rate_among_acts': float(unsafe[act.to_numpy()].mean()) if act.any() else 0.0,
        'positive_alert_recall': float(alert[pos].mean()) if pos.any() else 0.0,
        'negative_false_alert_burden': float(alert[neg].mean()) if neg.any() else 0.0,
        'mean_probes': float(df.probes.mean()),
        'median_probes': float(df.probes.median()),
        'episode_hits': int(sum(x['hit'] for x in episodes)),
        'episode_total': int(len(episodes)),
        'episodes': episodes,
    }, df


def main():
    print('[1/7] Load official MetroPT-3', flush=True)
    raw, archive_sha, _ = load_raw()
    feat, feature_cols = engineer_5min(raw)
    del raw
    index = pd.DatetimeIndex(feat.index)
    train_mask, cal_mask, test_mask = masks(index)
    y, excluded, episodes = warning_labels(index)

    X = feat[feature_cols].to_numpy(float)
    scaler = StandardScaler().fit(X[train_mask])
    Xz = scaler.transform(X)
    groups = sensor_groups(feature_cols)
    print(f'[2/7] {len(groups)} sensor groups, {len(feature_cols)} engineered features', flush=True)

    fit_nb = cal_mask & (~excluded)
    prior, prior_logodds, params, evid = fit_nb_evidence(Xz, y, fit_nb, groups)
    full_score = prior_logodds + np.sum(np.column_stack([evid[g] for g in groups]), axis=1)
    pos_cal = full_score[fit_nb & (y == 1)]
    neg_cal = full_score[fit_nb & (y == 0)]
    q_pos5 = float(np.quantile(pos_cal, 0.05))
    q_neg99 = float(np.quantile(neg_cal, 0.99))
    low, high = min(q_pos5, q_neg99), max(q_pos5, q_neg99)
    print(f'[3/7] prior={prior:.6f}; ACT_CONTINUE <= {low:.6f}; ACT_ALERT >= {high:.6f}', flush=True)

    fixed_order = build_fixed_order(prior_logodds, list(groups), y, fit_nb, evid, low, high)
    print('[4/7] fixed probe order: ' + ', '.join(fixed_order[:8]), flush=True)

    audit_mask = test_mask & (~excluded)
    rows = np.where(audit_mask)[0]
    summaries = {}
    decision_tables = []
    all_probe_events = []
    for kind in ['ADAPTIVE_CONTRACT_PROBE','FIXED_ORDER_PROBE','NO_PROBE','FULL_SENSOR']:
        recs, pe = run_policy(kind, rows, y, evid, groups, prior_logodds, low, high, fit_nb, fixed_order)
        sm, ddf = summarize(recs, index, y)
        summaries[kind] = sm
        ddf['policy'] = kind
        ddf['timestamp'] = index[ddf.row.to_numpy()].astype(str)
        ddf['truth'] = y[ddf.row.to_numpy()]
        decision_tables.append(ddf)
        all_probe_events.extend(pe)
        print(f"[5/7] {kind}: coverage={sm['act_coverage']:.3f} refuse={sm['refuse_rate']:.3f} unsafe={sm['unsafe_act_rate_among_acts']:.3f} probes={sm['mean_probes']:.3f}", flush=True)

    pe_df = pd.DataFrame(all_probe_events)
    ad_pe = pe_df[pe_df.policy == 'ADAPTIVE_CONTRACT_PROBE']
    chosen_rate = float(ad_pe.chosen_immediate_correct_resolution.mean()) if len(ad_pe) else 0.0
    random_ref = float(ad_pe.random_available_correct_resolution_fraction.mean()) if len(ad_pe) else 0.0
    any_rate = float(ad_pe.any_immediate_correct_resolution.mean()) if len(ad_pe) else 0.0
    probe_gain = chosen_rate - random_ref

    A = summaries['ADAPTIVE_CONTRACT_PROBE']
    F = summaries['FIXED_ORDER_PROBE']
    safe_ok = A['unsafe_act_rate_among_acts'] <= F['unsafe_act_rate_among_acts'] + 1e-12
    efficiency_adv = (A['refuse_rate'] < F['refuse_rate'] - 1e-12) or (
        A['mean_probes'] < F['mean_probes'] - 1e-12 and A['act_coverage'] >= F['act_coverage'] - 0.02
    )
    direct_probe_adv = probe_gain >= 0.05
    if safe_ok and efficiency_adv and direct_probe_adv:
        verdict = 'DIRECT_MECHANISM_SUPPORT_V2'
    elif (efficiency_adv or direct_probe_adv) and A['unsafe_act_rate_among_acts'] <= F['unsafe_act_rate_among_acts'] + 0.02:
        verdict = 'PARTIAL_MECHANISM_SUPPORT_V2'
    else:
        verdict = 'NO_DIRECT_MECHANISM_SUPPORT_V2'

    results = {
        'schema': 'INSACERMO_METROPT_DIRECT_ACTIONABILITY_V2',
        'status': 'EXPLORATORY_NOT_BLIND',
        'dataset': {'doi':'10.24432/C5VW3R','archive_sha256':archive_sha,'valid_5min_bins':int(len(feat))},
        'sensor_groups': list(groups),
        'prior_failure_probability': prior,
        'thresholds': {'q_pos5':q_pos5,'q_neg99':q_neg99,'act_continue_max':low,'act_alert_min':high},
        'max_probes': MAX_PROBES,
        'fixed_order': fixed_order,
        'policies': summaries,
        'adaptive_probe_diagnostic': {
            'probe_events': int(len(ad_pe)),
            'chosen_immediate_correct_resolution_rate': chosen_rate,
            'any_available_immediate_correct_resolution_rate': any_rate,
            'random_available_correct_resolution_fraction': random_ref,
            'chosen_minus_random': probe_gain,
        },
        'support_components': {'safe_vs_fixed':safe_ok,'efficiency_advantage':efficiency_adv,'direct_probe_advantage_ge_5pp':direct_probe_adv},
        'overall_verdict': verdict,
        'repair_scored': False,
        'repair_reason': 'Observational dataset lacks intervention counterfactuals.',
    }
    (OUT/'METROPT_DIRECT_ACTIONABILITY_V2_RESULTS.json').write_text(json.dumps(results, indent=2), encoding='utf-8')
    pd.concat(decision_tables, ignore_index=True).to_csv(OUT/'METROPT_DIRECT_ACTIONABILITY_V2_DECISIONS.csv', index=False)
    pe_df.to_csv(OUT/'METROPT_DIRECT_ACTIONABILITY_V2_PROBES.csv', index=False)

    report = [
        '# INSACERMO — MetroPT-3 Direct Actionability Audit V2', '',
        f'**{verdict}**', '',
        '**Status:** exploratory mechanism audit, not blind confirmation (V1 already inspected this holdout).', '',
        f'- Sensor groups: **{len(groups)}**',
        f'- Maximum probes: **{MAX_PROBES}**',
        f'- Adaptive chosen-probe immediate correct-resolution rate: **{100*chosen_rate:.2f}%**',
        f'- Random available-probe reference: **{100*random_ref:.2f}%**',
        f'- Probe-selection gain: **{100*probe_gain:.2f} percentage points**', '',
        '## Policies',
    ]
    for k, m in summaries.items():
        report.append(f"- {k}: ACT coverage **{100*m['act_coverage']:.2f}%**, REFUSE **{100*m['refuse_rate']:.2f}%**, unsafe ACT among ACTs **{100*m['unsafe_act_rate_among_acts']:.2f}%**, mean probes **{m['mean_probes']:.2f}**, episode alerts **{m['episode_hits']}/{m['episode_total']}**.")
    report += ['', '## Boundary', 'REPAIR is not scored because MetroPT contains no counterfactual maintenance intervention outcomes. A positive result here would support the ACT/PROBE/REFUSE mechanism only; it would not prove equivalence to the Lean canonical future state.']
    (OUT/'METROPT_DIRECT_ACTIONABILITY_V2_REPORT.md').write_text('\n'.join(report), encoding='utf-8')
    print('[6/7] ' + verdict, flush=True)
    print(json.dumps(results['adaptive_probe_diagnostic'], indent=2), flush=True)
    print('[7/7] done', flush=True)


if __name__ == '__main__':
    main()
