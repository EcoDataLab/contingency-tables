# Complete reserved-bit comparison

`python3 research/physical-trace-reservation-comparison/reserved_bits.py` reproduces [the exact integers](reserved-bits.json). It compares complete reserved word lengths on identical positive margin inputs and requested accuracy 2^-20. The old and stronger algorithms use their own checked scales. It also compares the previous and linear outer schedules of the stronger algorithm.

These are arithmetic evaluations of the stated Lean formulas, independently recalculated by a separate AI reviewer. They are not sampled runs, wall-clock timings, expected inspected bits, or a complete runtime-exponent theorem. The main interpretation and rounded table are in [the reservation comparison guide](../../docs/reservation-comparison.md).

The calculator only changes its output path from the locally reviewed script; reproduced JSON matches that reviewed artifact exactly. The current unmodified stronger construction uses the degree-85 uniform inner-completion allowance. Later tighter allowance/adapters have their own proof packets and are not silently substituted here.

`python3 research/physical-trace-reservation-comparison/tight_reserved_bits.py`
reproduces the checked alternative typed sampler's [exact complete reservations](tight-reserved-bits.json).
Its final word law equals the current hybrid law, with no larger complete width.
The ordinary raw sampler still uses its old reservation. The calculator retains
the same walk/exit/retry parameters; separate shape, numerator and singleton
refinements are excluded. No timing or inspected-bit result is inferred.
