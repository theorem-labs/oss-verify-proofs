(* the callee specification of the walk's one fill call, from the callee's own run lemma through the kit's glue.
   The callee's entry is a field of the layout text; the proof takes its machine word from the callee's own run
   lemma. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatSim Hoare ZStores.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require S9Memset S9Memset7168R.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require Import ZStep IGlueMemset.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import i9s_code.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance fx0.


Notation A_MEMSET := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_MEMSET (only parsing).

Lemma w64_lit' : forall z (w : word), bv_unsigned w = z -> w64 z = w. Proof. intros z w <-. apply w64_of_word. Qed. Lemma msteps_memset_S9 {RCa1 : RunCtx}  : msteps_memset (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMSET 7168.
Proof.
  intros regs mem0 rom dst ret H1 Hret H10 H11 H12 Hal Hnw Hok. change (Z.of_nat 7168) with 7168%Z in H12, Hnw. change (store_ok (run_segments R_segs rc_inp rc_sp rc_mb) mem0 dst 7168 = true) with (store_ok (run_segments R_segs rc_inp rc_sp rc_mb) mem0 dst (7 * 1024) = true) in Hok.
  destruct (S9Memset7168R.memset7168_run regs mem0 rom dst ret H1 Hret H10 H11 H12 Hal Hnw Hok)
    as (r' & m' & RUN & EQ & AG).
  exists r'. subst m'. split; [| exact AG]. unfold R_segs. erewrite (w64_lit' A_MEMSET); [ exact RUN | reflexivity ].
Qed.

Theorem memset7168_ok {RCa1 : RunCtx}  : memset_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMSET 7168.
Proof. pose proof (memset_glue (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMSET 7168 msteps_memset_S9) as G. change (Z.of_nat 7168) with 7168%Z in G. exact G. Qed.
