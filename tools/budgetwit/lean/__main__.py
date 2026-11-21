"""Regenerate a reviewed Lean range manifest."""
import argparse
import json
from pathlib import Path
import sys

from .emitter import generate
from .units import load
from .about_check import probe, validate_pairs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--unit", required=True, help="project/harness")
    parser.add_argument("--out", type=Path, required=True, help="unit namespace directory")
    parser.add_argument("--about", type=Path, help="emit the farm-run discharged-type probe")
    args = parser.parse_args()
    try:
        unit = load(args.unit, args.repo)
        for path in generate(args.manifest, unit, args.out):
            print(path)
        if args.about:
            public, paired, fresh = validate_pairs(json.loads(args.manifest.read_text()), unit, args.out)
            print(f"budgetwit type coverage: {public} public = {paired} paired + {fresh} fresh")
            args.about.parent.mkdir(parents=True, exist_ok=True)
            args.about.write_text(probe(json.loads(args.manifest.read_text()), unit))
            print(args.about)
    except (ValueError, OSError, KeyError) as error:
        print(f"budgetwit lean: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
