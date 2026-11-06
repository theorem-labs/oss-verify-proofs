From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
Open Scope Z_scope.

(* A footprint that is decided byte by byte (every non-wrapping range whose bytes are all in it is in it).
   ExecF.fp_ok is one (fp_ok_rng_bytes).  A footprint statement proved by route 1 (ROUTE1.md (a working note, not in this delivery)) takes
   this as a premise, because route 1's byte-wise footprint is weakened to a union of rng ranges and an access
   may straddle two adjacent ranges.  The text is MemNormP.v's; this leaf over lib.Lib.ExecF carries it alone,
   so a statement file does not pull MemNormP's require-closure (lib/Reusable), whose short module names clash
   with the ones the Seg files import (a Theorem Labs lane, 2026-10-27: 58 modules, 69 basename collisions on image B).
   A and B use this same file. *)
Definition rng_bytes (RNG : ExecF.footprint) : Prop :=
  forall b j, 0 <= b -> b + Z.of_nat j <= 2^64 ->
    (forall k, (k < j)%nat -> RNG (b + Z.of_nat k) 1%nat) -> RNG b j.

Lemma fp_ok_rng_bytes : forall lz AL, rng_bytes (ExecF.fp_ok lz AL).
Proof.
  intros lz AL b j Hb Hj H k Hk Hr.
  specialize (H k Hk 0%nat ltac:(lia) ltac:(lia)).
  change (Z.of_nat 0) with 0 in H. rewrite Z.add_0_r in H. exact H.
Qed.
