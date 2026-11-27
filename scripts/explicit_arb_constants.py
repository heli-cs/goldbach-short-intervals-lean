"""Independent Arb enclosures for selected constants in Section 8 of v6."""

from flint import arb, ctx, __version__


def prove_lt(label: str, enclosure: arb, upper: arb) -> None:
    if not enclosure < upper:
        raise ArithmeticError(f"{label}: did not prove {enclosure} < {upper}")
    print(f"{label}: {enclosure} < {upper}")


def prove_gt(label: str, enclosure: arb, lower: arb) -> None:
    if not enclosure > lower:
        raise ArithmeticError(f"{label}: did not prove {enclosure} > {lower}")
    print(f"{label}: {enclosure} > {lower}")


def main() -> None:
    ctx.prec = 192
    print(f"python-flint {__version__}, {ctx.prec}-bit Arb precision")
    one = arb(1)
    two = arb(2)
    pi = arb.pi()
    euler = arb.const_euler()
    ell = arb(42)
    log_ell = ell.log()
    x = ell.exp()
    delta = ell**2 / x
    bandwidth = (3 * ell).sqrt()
    cutoff = x / ell**2
    loss = pi**2 * (two.log()**2 + 2 * two.log() + 2) / 6
    prove_lt("quadratic weight loss coefficient", loss, arb(6361) / 1000)
    prove_lt("delta at 42", delta, arb(11) / 10**16)
    prove_lt("delta exp(V/2) at 42", delta * (bandwidth / 2).exp(), arb(3) / 10**13)
    prove_lt("delta exp(V) at 42", delta * bandwidth.exp(), one / 10**10)
    theta_error = (two * x).sqrt() * (ell + 1)**2 / (8 * pi)
    prove_lt("first-moment relative error at 42", 4 * theta_error * ell**2 / x, one / 1000)
    prove_gt("trimmed endpoint", cutoff, arb(599))
    prove_lt("prime-power bound divided by delta", 4 * ell**3 * (ell + 1) * (-ell / 2).exp(),
             arb(967) / 100000)
    gap = 4 * ell * log_ell - 4 * log_ell**2 - 10 * ell - 7
    prove_gt("variance margin at 42", gap, arb(145))
    reciprocal_sum = 2 + euler - (4 * pi).log()
    prove_lt("reciprocal zero-sum constant", reciprocal_sum, arb(47) / 1000)
    prove_lt("original prime coefficient", 6 * (arb(103883) / 100000) / pi**2, arb(633) / 1000)
    prove_lt("relaxed prime coefficient", (arb(624) / 100) / pi**2, arb(633) / 1000)
    a1 = 1 - euler
    a2 = a1**2 + 1 + pi**2 / 12
    prove_lt("twice the normalized first Mellin log moment", 2 * a1, one)
    prove_lt("normalized second Mellin log moment", a2, arb(3))
    a = (2 * pi).log()
    prove_lt("corrected rational-term integral", (a**2 + 2 * a + 2) / pi**2, one)
    prove_lt("adapted counting remainder at 42", 15000 * delta * (ell + 5)**2, one / 1000000)


if __name__ == "__main__":
    main()
