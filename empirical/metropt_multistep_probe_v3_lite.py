#!/usr/bin/env python3
from __future__ import annotations

import json
import os
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.preprocessing import StandardScaler

import metropt_direct_actionability_v2 as v2
import metropt_multistep_probe_v3 as v3

OUT = Path(os.environ.get('INSACERMO_OUT', 'metropt_v3_lite_results'))
OUT.mkdir(parents=True, exist_ok=True)
N_PER_CLASS = 240


def evenly_spaced(rows: np.ndarray, n: int) -> np.ndarray:
    rows = np.asarray(rows, dtype=int)
    if len(rows) <= n:
        return rows
    idx = np.linspace(0, len(rows) - 1, n, dtype=int)
    return rows[idx]


def main():
    print('[1/6] load and reproduce frozen V3 contract', flush=True)
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
    pools = v3.build_pools(y, fit_nb, evid)

    audit = test_mask & (~excluded)
    pos_rows = evenly_spaced(np.where(audit & (y == 1))[0], N_PER_CLASS)
    neg_rows = evenly_spaced(np.where(audit & (y == 0))[0], N_PER_CLASS)
    rows = np.sort(np.concatenate([pos_rows, neg_rows]))
    print(f'[2/6] diagnostic rows={len(rows)} positives={len(pos_rows)} negatives={len(neg_rows)}', flush=True)

    summaries = {}
    events = []
    for kind in ['MULTISTEP_VOI_PROBE', 'MYOPIC_CONTRACT_PROBE']:
        rec, ev = v3.run_adaptive(kind, rows, y, evid, groups, prior_logodds, low, high, pools)
        sm, _ = v2.summarize(rec, index, y)
        summaries[kind] = sm
        events.extend(ev)
        print(f"[3/6] {kind}: coverage={sm['act_coverage']:.4f} unsafe={sm['unsafe_act_rate_among_acts']:.4f} probes={sm['mean_probes']:.4f}", flush=True)

    evdf = pd.DataFrame(events)
    m = evdf[evdf.policy == 'MULTISTEP_VOI_PROBE']
    my = evdf[evdf.policy == 'MYOPIC_CONTRACT_PROBE']
    chosen2 = float(m.chosen_two_real_probe_correct_resolution.mean()) if len(m) else 0.0
    rand2 = float(m.random_first_then_policy_two_probe_correct_fraction.mean()) if len(m) else 0.0
    my2 = float(my.chosen_two_real_probe_correct_resolution.mean()) if len(my) else 0.0

    result = {
        'schema': 'INSACERMO_METROPT_V3_LITE_SMOKE',
        'status': 'DIAGNOSTIC_ONLY_NOT_SCIENTIFIC_VERDICT',
        'dataset_sha256': archive_sha,
        'rows': int(len(rows)),
        'positive_rows': int(len(pos_rows)),
        'negative_rows': int(len(neg_rows)),
        'multistep_two_probe_correct_resolution': chosen2,
        'random_first_reference': rand2,
        'multistep_minus_random': chosen2 - rand2,
        'myopic_two_probe_correct_resolution': my2,
        'multistep_minus_myopic': chosen2 - my2,
        'policies': summaries,
    }
    (OUT/'METROPT_V3_LITE_RESULTS.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    evdf.to_csv(OUT/'METROPT_V3_LITE_EVENTS.csv', index=False)
    print('[5/6] diagnostic', json.dumps(result, indent=2), flush=True)
    print('[6/6] done — diagnostic only; official V3 remains authoritative', flush=True)


if __name__ == '__main__':
    main()
