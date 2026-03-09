#!/usr/bin/env python3
"""
memguard CLI
============
    memguard trainer_state.json
    memguard logs.csv --steps 21000
    memguard trainer_state.json --json
    memguard audit --limit 5000 --out results.csv
"""
import argparse, json, sys


_ICONS = {
    "EARLY_STOP"      : "🔴 EARLY_STOP",
    "MONITOR_CLOSELY" : "🟡 MONITOR_CLOSELY",
    "HEALTHY"         : "🟢 HEALTHY",
    "HEALTHY_OR_NEUTRAL":"🟢 HEALTHY_OR_NEUTRAL",
    "MONITOR"         : "🔵 MONITOR",
    "INSUFFICIENT_DATA":"⚪ INSUFFICIENT_DATA",
}


def _cmd_analyze(args):
    from . import analyze_file
    try:
        rep = analyze_file(args.path, total_steps_scheduled=args.steps)
    except Exception as e:
        print(f"Erreur : {e}", file=sys.stderr)
        sys.exit(1)

    if args.json:
        print(json.dumps(rep, indent=2))
        return

    action  = rep["recommended_action"]
    verdict = _ICONS.get(action, action)
    saved   = rep.get("compute_saved_pct")
    reason  = rep.get("risk_reason") or "—"

    print()
    print(f"  {verdict}")
    print(f"  risk_reason       : {reason}")
    print(f"  compute_saved_pct : {saved if saved is not None else '—'}")
    print(f"  n_points          : {rep['n_points']}")
    print(f"  final_gap         : {rep.get('final_gap', '—')}")
    print(f"  final_mem         : {rep.get('final_mem', '—')}")
    if rep.get("stop_t"):
        print(f"  stop_t            : {rep['stop_t']}")
    print()
    sys.exit(0 if action in ("HEALTHY", "HEALTHY_OR_NEUTRAL", "MONITOR", "INSUFFICIENT_DATA") else 1)


def _cmd_audit(args):
    from .audit import run_audit
    run_audit(
        limit      = args.limit,
        filter_tag = args.filter,
        out_csv    = args.out,
        verbose    = not args.quiet,
        workers    = args.workers,
    )


def main():
    p = argparse.ArgumentParser(prog="memguard")
    sub = p.add_subparsers(dest="cmd")

    # ── memguard <file> ──────────────────────────────────────────────────────
    # (pas de subcommand = analyse directe pour rétrocompat)
    p.add_argument("path",  nargs="?", help="trainer_state.json ou logs.csv")
    p.add_argument("--steps", type=int, default=None)
    p.add_argument("--json",  action="store_true")

    # ── memguard audit ───────────────────────────────────────────────────────
    pa = sub.add_parser("audit", help="Scan HuggingFace Hub")
    pa.add_argument("--limit",   type=int, default=5000)
    pa.add_argument("--filter",  type=str, default="tensorboard")
    pa.add_argument("--out",     type=str, default="memguard_audit.csv")
    pa.add_argument("--workers", type=int, default=4)
    pa.add_argument("--quiet",   action="store_true")

    args = p.parse_args()

    if args.cmd == "audit":
        _cmd_audit(args)
    elif args.path:
        _cmd_analyze(args)
    else:
        p.print_help()
        sys.exit(1)


if __name__ == "__main__":
    main()

