"""Generate candidate Goldbach interval certificates. Lean verifies all rows."""

from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import count
from math import gcd
from pathlib import Path
from time import perf_counter


TRIAL_LIMIT = 4096


def small_primes(limit):
    primes = []
    for n in range(2, limit + 1):
        if all(n % p for p in primes if p * p <= n):
            primes.append(n)
    return primes


SMALL_PRIMES = small_primes(TRIAL_LIMIT)


def prime_candidate(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    odd_part = n - 1
    twos = 0
    while odd_part % 2 == 0:
        odd_part //= 2
        twos += 1
    for base in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if base % n == 0:
            continue
        value = pow(base, odd_part, n)
        if value in (1, n - 1):
            continue
        for _ in range(twos - 1):
            value = value * value % n
            if value == n - 1:
                break
        else:
            return False
    return True


def rho_factor(n):
    for constant in count(1):
        slow = fast = 2
        for _ in range(200000):
            slow = (slow * slow + constant) % n
            fast = (fast * fast + constant) % n
            fast = (fast * fast + constant) % n
            divisor = gcd(abs(slow - fast), n)
            if divisor == n:
                break
            if divisor > 1:
                return divisor


@cache
def factors_of(n):
    factors = []
    for p in SMALL_PRIMES:
        if p * p > n:
            break
        while n % p == 0:
            factors.append(p)
            n //= p
    if n > 1:
        if prime_candidate(n):
            factors.append(n)
        else:
            divisor = rho_factor(n)
            factors.extend(factors_of(divisor))
            factors.extend(factors_of(n // divisor))
    return tuple(factors)


@cache
def lucas_data(n):
    multiplicities = sorted(Counter(factors_of(n - 1)).items())
    for base in range(2, n):
        if pow(base, n - 1, n) == 1 and all(
            pow(base, (n - 1) // p, n) != 1 for p, _ in multiplicities
        ):
            return base, multiplicities
    raise ValueError(f"No Lucas witness for {n}")


def emit_prime(lines, n, emitted, modular):
    name = f"prime_{n}"
    if n in emitted:
        return name
    if n <= TRIAL_LIMIT:
        if n not in SMALL_PRIMES:
            raise ValueError(f"{n} is not a prime leaf")
        lines += [f"private theorem {name} : Nat.Prime {n} := by norm_num", ""]
    else:
        base, factors = lucas_data(n)
        children = [emit_prime(lines, p, emitted, modular) for p, _ in factors]
        factor_list = ", ".join(f"({p}, {e})" for p, e in factors)
        lines.append(f"private theorem {name} : Nat.Prime {n} := by")
        if modular:
            factor_tests = ", ".join(f"{child}, by decide" for child in children)
            lines += [
                f"  exact prime_of_pratt_modular (base := {base}) (fuel := {n.bit_length()})",
                f"    (factors := [{factor_list}]) (by decide) (by decide) (by decide) (by decide)",
                f"    ⟨{factor_tests}, True.intro⟩",
            ]
        else:
            factor_tests = ", ".join(f"{child}, ?_" for child in children)
            lines += [
                f"  refine prime_of_lucas_factorization (base := {base}) (factors := [{factor_list}]) (by decide) ?_ ?_",
                f"  · change ({base} : ZMod {n}) ^ ({n - 1} : ℕ) = 1",
                "    reduce_mod_char",
                f"  · refine ⟨{factor_tests + ', ' if factors else ''}True.intro⟩",
            ]
            for index, (p, _) in enumerate(factors):
                indent = "    · " if index or len(factors) > 1 else "    "
                body_indent = "      " if len(factors) > 1 else "    "
                lines += [
                    f"{indent}change ({base} : ZMod {n}) ^ ({(n - 1) // p} : ℕ) ≠ 1",
                    f"{body_indent}reduce_mod_char",
                    f"{body_indent}all_goals decide",
                ]
        lines.append("")
    emitted.add(n)
    return name


def next_pair(left, width):
    high = (left + width) // 2 * 2
    for p in SMALL_PRIMES[1:25]:
        for total in range(high, left, -2):
            q = total - p
            if q >= 3 and prime_candidate(q):
                return p, q
    raise ValueError(f"No candidate pair in ({left}, {left + width}]")


def next_prime(left, width):
    high = (left + width - 1) // 2 * 2 + 1
    for p in range(high, max(left, 2), -2):
        if prime_candidate(p):
            return (p,)
    raise ValueError(f"No candidate odd prime in ({left}, {left + width}]")


def coverage_type(left, right, width, primes_only):
    predicate = "HasOddPrime" if primes_only else "GoldbachConcrete.HasGoldbach"
    return (
        f"∀ x : ℝ, ({left} : ℕ) ≤ x → x < ({right} : ℕ) → "
        f"{predicate} x ({width} : ℕ)"
    )


def join_shards(names, width, primes_only, indent="  "):
    if len(names) == 1:
        return names[0]
    mid = len(names) // 2
    join = "join_prime_interval_covers" if primes_only else (
        f"join_goldbach_interval_covers (H := fun _ => ({width} : ℕ))"
    )
    deeper = indent + "  "
    left = join_shards(names[:mid], width, primes_only, deeper)
    right = join_shards(names[mid:], width, primes_only, deeper)
    return f"({join}\n{deeper}{left}\n{deeper}{right})"


def emit_block(lines, name, left, right, width, shard_size, primes_only, emitted, modular):
    if not (0 <= left < right and width > 0 and right + width < 2**64):
        raise ValueError("Invalid block boundaries or width")
    cursor = left
    row_count = 0
    names = []
    choose = next_prime if primes_only else next_pair
    row_type = "CertifiedOddPrime" if primes_only else "PairCertificate"
    theorem = "prime_interval_cover_of_check" if primes_only else "interval_cover_of_check"
    while cursor < right:
        start = cursor
        rows = []
        while cursor < right and len(rows) < shard_size:
            nums = choose(cursor, width)
            primes = [emit_prime(lines, p, emitted, modular) for p in nums]
            items = [f"⟨{p}, {proof}, by decide⟩" for p, proof in zip(nums, primes)]
            rows.append("  " + (items[0] if primes_only else f"⟨{items[0]}, {items[1]}⟩"))
            cursor = sum(nums)
        end = min(cursor, right)
        row_count += len(rows)
        shard = f"{name}_shard_{len(names)}"
        lines += [
            f"private def {shard}_rows : List {row_type} := [",
            ",\n".join(rows),
            "]",
            "",
            f"private theorem {shard} :",
            f"    {coverage_type(start, end, width, primes_only)} :=",
            f"  {theorem} (width := {width}) (left := {start}) (right := {end})",
            f"    (rows := {shard}_rows) (by decide +kernel)",
            "",
        ]
        names.append(shard)
    lines += [
        f"theorem {name} :",
        f"    {coverage_type(left, right, width, primes_only)} :=",
        f"  {join_shards(names, width, primes_only)}",
        "",
    ]
    print(f"[{left}, {right}), width {width}, {row_count} rows, {len(names)} shards")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--name", required=True)
    parser.add_argument("--block", nargs=3, type=int, action="append", required=True,
                        metavar=("LEFT", "RIGHT", "WIDTH"))
    parser.add_argument("--shard-size", type=int, default=16)
    parser.add_argument("--prime", action="store_true", help="Generate odd-prime ladders")
    parser.add_argument("--modular", action="store_true", help="Check Lucas powers by kernel reduction")
    args = parser.parse_args()
    if not args.name.isidentifier() or not 1 <= args.shard_size:
        parser.error("Use a Lean identifier and a positive shard size")
    then = perf_counter()
    proof_import = (
        "import Goldbach.Explicit.PrattModPow" if args.modular else
        "import Mathlib.Tactic.ReduceModChar"
    )
    lines = [
        "import Goldbach.Explicit.IntervalCertificate",
        proof_import,
        "",
        "/-! Generated by scripts/generate_interval_certificate.py. -/",
        "",
    ]
    if args.modular:
        lines += ["set_option maxRecDepth 4096", ""]
    lines += ["namespace GoldbachExplicit", ""]
    emitted = set()
    for index, block in enumerate(args.block):
        name = args.name if len(args.block) == 1 else f"{args.name}_{index}"
        emit_block(lines, name, *block, args.shard_size, args.prime, emitted, args.modular)
    args.output.write_text("\n".join(lines + ["end GoldbachExplicit", ""]), encoding="utf-8", newline="\n")
    print(f"{len(emitted)} distinct prime proofs including factors")
    print(f"{args.output.stat().st_size} source bytes in {perf_counter() - then:.3f} s")


if __name__ == "__main__":
    main()
