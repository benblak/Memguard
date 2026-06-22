"""Command-line interface."""

from __future__ import annotations

import argparse
import json
import sys

from .core import analyze_file


def _analyze(args) -> int:
    try:
        report = analyze_file(args.path, total_steps_scheduled=args.steps)
    except Exception as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(f"action: {report['recommended_action']}")
        print(f"reason: {report['risk_reason']}")
        print(f"compute_saved_pct: {report.get('compute_saved_pct')}")
        print(f"best_val: {report.get('best_val')}")
        print(f"final_val: {report.get('final_val')}")
        print(f"relative_degradation: {report.get('relative_degradation')}")
    if args.fail_on_stop and report["recommended_action"] == "EARLY_STOP":
        return 1
    return 0


def _audit(args) -> int:
    from .audit import run_audit

    frame = run_audit(
        limit=args.limit,
        filter_tag=args.filter,
        out_csv=args.out,
        verbose=not args.quiet,
        workers=args.workers,
    )
    return 0 if not frame.empty else 1


def main(argv=None):
    parser = argparse.ArgumentParser(prog="insacermo-memguard")
    sub = parser.add_subparsers(dest="command", required=True)

    analyze_parser = sub.add_parser("analyze", help="Analyze trainer_state.json or CSV logs")
    analyze_parser.add_argument("path")
    analyze_parser.add_argument("--steps", type=float, default=None)
    analyze_parser.add_argument("--json", action="store_true")
    analyze_parser.add_argument("--fail-on-stop", action="store_true")
    analyze_parser.set_defaults(func=_analyze)

    audit_parser = sub.add_parser("audit", help="Audit public Hugging Face trainer_state.json files")
    audit_parser.add_argument("--limit", type=int, default=5000)
    audit_parser.add_argument("--filter", default="tensorboard")
    audit_parser.add_argument("--out", default="memguard_audit.csv")
    audit_parser.add_argument("--workers", type=int, default=4)
    audit_parser.add_argument("--quiet", action="store_true")
    audit_parser.set_defaults(func=_audit)

    args = parser.parse_args(argv)
    raise SystemExit(args.func(args))


if __name__ == "__main__":
    main()
