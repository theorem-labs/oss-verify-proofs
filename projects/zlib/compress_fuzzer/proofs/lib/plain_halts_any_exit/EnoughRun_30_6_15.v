(** * EnoughRun_30_6_15 — the enough.c oracle cell (30, 6, 15), from EnoughCheck.v.

    SPLIT by tools/split_enough_cells.py: one VM certificate per file,
    moved verbatim (statement and proof) so that no file builds for more than
    5 minutes.  Do not edit by hand: edit the script and re-run it. *)

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From Stdlib Require Import ZArith.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Example c_30_6_15 : enough_run 30 6 15 = Some (4309772, Some 592).
Proof. vm_cast_no_check (@eq_refl (option (Z * option Z)) (Some (4309772, Some 592))). Qed.
