# Handling the 129th bit in RISC-V: a guided tour

This covers the 128-bit-security variant of the FORS submission (`work/py-128`, `SEC128-STUDY.md`).
Moving from 128-bit to 129-bit values costs about +20% verify cycles. Almost none of that comes
from extra hashing (788 vs 803 compressions). It comes from a few extra instructions that move
one byte around at every hash. This note explains why they are needed and what they are.

## 1. The one rule that causes all of it

The only hash primitive is the HASH system call:

```
HASH(a0 = input address, a1 = length (multiple of 64), a2 = output address)
  -> writes the full 32-byte answer at a2 .. a2+32
```

Two constraints matter here:
- **Alignment:** `a2` must be a multiple of 8.
- **Output size:** the answer is always 32 bytes, even when we only keep 16 (128 bits) or 17 (129 bits) of it.

The 127-bit verifier gets its speed from one trick: **hash in place**. Each hash input is a
64-byte block, such as `tweak (16) | 0 (32) | value (16)` for a WOTS chain step. The verifier
sets `a2` to the *value slot* of the next block, so the answer lands exactly where the next
hash will read it:

```
128-bit chain step (9 cycles):
    sb   MU, 4(a0)      ; patch the tweak byte "step number"   (1)
    ecall               ; answer bytes 0..15 -> CB+48 (value)  (8)
                        ; answer bytes 16..31 -> CB+64..80: junk, lands past the block
```

Answer bytes 0..15 are exactly the next value, and bytes 16..31 fall *outside* the block, so
nothing has to be copied.

With 129-bit values the value is answer bytes 0..15 plus **bit 0 of answer byte 16**. That
byte lands at `a2 + 16`. Because `a2` can only move in steps of 8, you cannot place the answer so
that 17 bytes fall exactly where the next block wants them. The 17th byte always lands one
byte past the 16-byte slot, which is either outside the block or on top of something else.
**Every hash therefore needs its 17th byte moved by hand.** That is the entire story; the rest
is choosing the cheapest way to do the move in each kind of block.

## 2. Chain steps: 2 extra instructions per step (9 → 11 cycles)

**Layout.** The new chain block is `tweak | 0^31 | hi | lo`, with `lo` (16 bytes) at `CB+48` as
before and the extra byte `hi` at `CB+47`, just *before* the value. `hi` is placed before `lo`
because the answer write covers `CB+48 .. CB+80`, so anything stored after `lo` would be
destroyed.

**Code.**
```
chain step (11 cycles):
    sb   MU, 4(a0)      ; tweak: step number                      (1)
    ecall               ; answer -> CB+48 .. CB+80                (8)
                        ;   bytes 0..15 = new lo (in place)
                        ;   byte 16     = new hi, sitting at CB+64 (outside the block)
    lbu  T, 64(a0)      ; fetch answer byte 16                    (1)
    sb   T, 47(a0)      ; store it in the hi slot, before lo      (1)
```

**Why chain values are 136 bits.** The copy moves the *whole* byte. The design therefore treats
WOTS chain values as **136 bits** (16 bytes + a full byte), not 129. A strict 129-bit value
would need `andi T, T, 1` to clear the other 7 bits, one more cycle per step.

**The trade.** There are about 106 steps per layer and 5 layers, so that cycle adds up. The
full byte costs 7 extra signature bits per chain (215 chains ≈ +188 bytes) and saves ≈ 745
cycles. That trade improves S×C by 2.4%.

**Last step (12 cycles).** The last step of a chain writes its answer directly into the OTS
leaf block (`a2 = LB+80+16i`). Its hi byte then goes to the leaf block's hi area:
`lbu T, LB+96+16i ; sb T, LB+16+i`. The leaf block stores all 43 hi bytes first, then all 43 lo
values, so the lo values stay contiguous for in-place writing.

**Starting a chain.** The table entry that starts a chain stores the value's 16 bytes and then
its hi byte, `sd v0; sd v1; sb HI, CB+47`. That is 1 instruction more than before, plus
`lbu HI` to load it from the witness.

## 3. Merkle folds: 5 extra instructions per level (17 → 22 cycles)

**Layout.** A node block is `tweak | L.b R.b 0^14 | L.lo | R.lo`: the two children's 129th bits
sit in the old zero "P" area, as bytes `NB+16` (left) and `NB+17` (right).

**The problem.** The current node V was just written by the previous hash into its slot
`NB+32+16t`, where t = 0 means V is the left child and t = 1 the right child. Its answer byte 16
landed at `NB+48+16t`:
- **t = 1:** V is at `NB+48`, and its byte 16 is at `NB+64`, outside the block.
- **t = 0:** V is at `NB+32`, and its byte 16 is at `NB+48`, *inside the sibling's slot*. That
  slot is about to be overwritten by the sibling, so the bit must be rescued first.

**Code.**
```
fold level (22 = 14 instructions + 8):
    lbu  T, NB+48+16t        ; V's answer byte 16 (rescued before the sibling overwrites it)
    andi T, T, 1             ; keep only bit 128: node values are true 129-bit values
    sb   T, NB+16+t          ; V.b -> its b-byte position
    ld/ld/sd/sd              ; sibling lo (16 bytes) from the witness -> slot 1-t   (as before)
    lbu  T, <sibling b byte in the witness>
    sb   T, NB+17-t          ; sibling.b -> its b-byte position
    srli/sw                  ; heap index into the tweak                            (as before)
    slli/branch              ; track selection for the next level                   (as before)
    addi a2, NB+32+16t'; ecall                                                       (as before)
```

**Why `andi` is kept here.** Node values are hashed into the tree and compared with the public
key, and the proof treats them as exactly 129 bits. Here the mask is cheaper than the
alternative: a full-byte node value would add bytes to every stored authentication node.

**Where the cost lands.** FORS (14 trees × 10 levels) pays 5 × 154 ≈ 771 extra cycles, and the
hypertree paths (34 levels) ≈ 170.

**The witness side.** The sibling's b-bit is stored in the witness as a **whole byte**, 0 or 1,
at a fixed address, so a single `lbu` fetches it. The verifier never unpacks bit fields; see §5
for why that is safe.

## 4. Smaller spots

- **FORS roots hash.** The 14 roots are hashed together in one block `tweak | b_0..b_13 0^2 |
  lo_0..lo_13`. Each root's bit costs `lbu; andi; sb` (3 cycles).
- **Encoding (WOTS digit decoding).** The 129 answer bits are split into 43 base-8 digits. 42
  come from the two 64-bit words as before (SWAR digit sum). Digit 42 is `lbu X, EO+16 ; andi X,
  X, 7`, added into the sum. The message fed to the encoding hash carries its b bit in a
  dword: `lbu; andi; sd EB+48`.
- **Final comparison with the public key.** The public key stays 16 bytes. The root's 129th bit
  must additionally be 0 (keygen grinds an 8-bit "root salt" σ until it is):
  ```
  ld/ld/bne ×2              ; root.lo == pk          (as before)
  lbu  T, FO+16 ; andi T, T, 1 ; bne T, x0, reject   ; root.b == 0  (+3)
  ```
- **Top root.** Its tweak carries the salt: `lwu T, σ ; sw T, NB+4` (+2).

## 5. Why verify never touches packed bits

The signature size S counts bytes, so the signature is **bit-packed**. All 16-byte parts and the
215 chain hi bytes are byte-aligned. Everything that is really a single bit goes into a 41-byte
bit field: ρ.b, the 154 FORS b-bits, the 34 path b-bits, the counters, the salt and the digest
trial counter. That brings S to within one byte of the information-theoretic minimum.

Unpacking a bit costs about 3 instructions (`lbu; srli; andi`). Done in verify, that would add
hundreds of cycles, so it happens in **expand**, which is unscored. expand copies the aligned
parts and writes every packed bit as a whole byte (0/1) at a fixed witness address. verify
reads each one with a single `lbu`.

The witness grows by a few hundred bytes, but W costs only ⌈W/256⌉ cycles (27 here). The one
subtlety: expand must reject a signature whose spare padding bit is set. Otherwise two
signatures would expand to the same witness, which is a trivial strong forgery.

## 6. The bill

| where | per unit | units | extra cycles |
|---|---:|---:|---:|
| chain step (copy hi byte) | +2 | ~530 steps + chain starts, net of the higher T and the 43rd chain | ≈ +1,335 |
| FORS fold (rescue V.b + mask + sibling b) | +5 | 154 | ≈ +771 |
| hypertree fold | +5 | 34 | ≈ +170 |
| OTS leaf hash (12 blocks instead of 11) | +8 | 5 | +40 |
| roots, encoding, compare, salt, digest | small | – | ≈ +22 |
| **total** | | | **≈ +2,340 (11,573 → 13,914 incl. witness charge)** |

Hashing itself is slightly *cheaper* (788 vs 803 compressions: a 43rd chain, but a higher target
sum). **The 128-bit tax is entirely data movement caused by the 8-byte alignment of HASH's
output: one `lbu` / `sb` pair, sometimes with an `andi`, per hash.**

## 7. What could still be squeezed (not implemented)

- **Store the 129th bit where the answer puts it.** A block format where the extra byte *follows*
  the value, at `slot+16`, could let some hashes write it in place. For chains this fails,
  because the block ends at `CB+64` and the extra byte would fall outside it.
- **Keep FORS internal nodes at 128 bits.** This removes the fold cost and gives 88.9M (+19.9%)
  instead of 93.5M. It needs a new proof component: FORS structural matches as second-order
  events.
- **Batch the b-bits of a path.** A path's b-bits could be stored in one dword and consumed by
  shifting. That saves the `lbu` of the sibling b per level but needs a shift per level, so the
  gain is ≈ 0.
