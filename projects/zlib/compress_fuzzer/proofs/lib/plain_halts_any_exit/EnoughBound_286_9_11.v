(** * EnoughBound_286_9_11 — enough_bound 286 9 11, from EnoughFitsB10.v's oracle cells.

    SPLIT by tools/split_enough_cells.py: one VM certificate per file,
    moved verbatim (statement and proof) so that no file builds for more than
    5 minutes.  Do not edit by hand: edit the script and re-run it. *)

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From Stdlib Require Import ZArith.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma eb_286_9_11 : enough_bound 286 9 11 = Some 796.
Proof. vm_cast_no_check (eq_refl (Some 796)). Qed.
