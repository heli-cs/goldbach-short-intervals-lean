"""Regenerate the prime ladders that connect ten billion to the analytic range."""

from pathlib import Path
from subprocess import run
from sys import executable


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "Goldbach" / "Explicit" / "CutoffData"
GENERATOR = ROOT / "scripts" / "generate_interval_certificate.py"

INNER_LEFT = 1_800_003
INNER_RIGHT = 27_500_003
OUTER_LEFT = 10_000_000_000 - INNER_RIGHT
OUTER_RIGHT = 1_500_000_000_000 - INNER_RIGHT
PARTS = 8


def generate_ladder(kind, left, right, width):
    for index in range(PARTS):
        start = left + (right - left) * index // PARTS
        end = left + (right - left) * (index + 1) // PARTS
        source = OUTPUT / f"{kind}{index}.lean"
        name = f"cutoff_{kind.lower()}_{index}"
        run(
            [
                executable, str(GENERATOR), str(source), "--prime", "--modular",
                "--name", name, "--block", str(start), str(end), str(width),
            ],
            cwd=ROOT,
            check=True,
        )


def main():
    OUTPUT.mkdir(exist_ok=True)
    generate_ladder("Inner", INNER_LEFT, INNER_RIGHT, 510)
    generate_ladder("Outer", OUTER_LEFT, OUTER_RIGHT, INNER_RIGHT - 3)


if __name__ == "__main__":
    main()
