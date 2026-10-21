[![](logo.svg)](https://axiommath.ai/)

# Explicit Positive-Density Collatz Convergence in Logarithmic Time

This is a Lean formalization of an explicit positive-density theorem for Collatz convergence in logarithmic time, refining [Lech Mazur's Theorem 1.1](https://x.com/LechMazur/status/2096464472973975782).

## Main Results

* For every `N`, at least `⌊N/2^2^2^163⌋` of the `n < N` reach `1` within `⌊10.46 log n⌋` Collatz steps.
* For every `N`, at least `⌊N/2^2^2^163⌋` of the `n < N` are odd and reach `1` within `⌊10.46 log n⌋` Collatz steps and within `⌊3.4881 log n⌋` accelerated Collatz steps.
* For every `s` coprime to `6` and every `N`, at least `⌊N/(s^(25/11) · 2^2^2^163)⌋` of the `n < N` are odd and reach `s` within `⌊10.46 log(n/s)⌋` Collatz steps and within `⌊3.4881 log(n/s)⌋` accelerated Collatz steps.
* For every `t` not divisible by `3` and every `N`, at least `⌊N/(t^(25/11) · 2^2^2^163)⌋` of the `n < N` are odd and reach `t` within `⌊10.46 log(n/t)⌋` Collatz steps and reach the odd part of `t` within `⌊3.4881 log(n/t)⌋` accelerated Collatz steps.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only depends on Mathlib. It contains formal statements of [§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:
```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
