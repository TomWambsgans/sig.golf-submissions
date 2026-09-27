# 128-bit security study (FORS+C submission)

What does it cost, in S × C, to move our best FORS+C submission (#35: S = 6404, C = 11573,
S × C = 74,113,492, 127-bit security) to 128-bit security with 129-bit values?

**Answer: S = 6720, W = 6900, C = 13,914, S × C = 93,502,080 (+26.2%).** A variant that keeps
the FORS internal nodes at 128 bits reaches 88,881,480 (+19.9%), but it needs new proof work.

- `SEC128-STUDY.md`: parameters, formats, the pen-and-paper security argument (with the budget
  per term) and the measurements.
- `SEC128-RISCV-EXPLAINED.md`: a guided tour of the RISC-V instructions that handle the 129th bit.
- `py-128/`: the reference scheme (`ref.py`), the four RISC-V programs (`gen.py`; the verifier is
  the optimized one), the emulator (`vm.py`) and the differential tests (`test.py`); program
  listings in `out/`.

This is a study only. The security argument is on paper, and there is no Lean proof for this
variant. The submission under `submission/` is unchanged (the verified FORS+C record).
