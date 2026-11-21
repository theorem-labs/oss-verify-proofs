(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtLenFastLeg — THE MOUNTAIN
      DISCHARGE: model-rt's fast-path residue [ZrLenFastLeg], at the
      amendment-window-2 interface, holds OUTRIGHT.

    Amendment window 2, q7-decode per TL grant 2026-08-20 (owner review
    trails).  The proof is the W1-W5 chain's [w5_leg]; its local
    statement [W5LenFastLeg] is delta-convertible to the amended
    [ZrLenFastLeg] — every local definition copy in the W-chain is
    byte-identical to its landed twin (w3_len_ents/w3_dist_ents =
    the amended zr_len_ents/zr_dist_ents, w3_root_own = zr_root_own,
    w4_syms_prefix = zr_syms_prefix, w5_root_opshape =
    GtDecHsel.lcode_root_opshape, br_haligned shared via W2Stream). *)

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6Q W5Bridge.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Theorem zr_len_fast_leg_holds : ZrLenFastLeg.
Proof. exact w5_leg. Qed.

Print Assumptions zr_len_fast_leg_holds.
