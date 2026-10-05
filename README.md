# contract-lean-deform-exact

A Lean 4 proof that sampling a feature map at a bounded learned offset equals a fixed sum of integer shifts weighted by a tent kernel.

## What it is for

Deformable attention samples at a data-dependent position, and an edge accelerator's compiler refuses that operator. Bilinear interpolation is a separable tent kernel that vanishes beyond one pixel, so the same sample is a sum of static shifts whose weights carry everything that depends on the image. The theorems prove that rewrite exact in one and two dimensions, for any finite window containing the shifts at 0 and 1, with no admitted goals. RFD 1131 owns the operator emulation this proof backs.

## Build and run

    lake exe cache get
    lake build

`scripts/check_no_sorry.py` confirms that no goal is admitted.

## Licence

MIT; see `LICENSE`.
