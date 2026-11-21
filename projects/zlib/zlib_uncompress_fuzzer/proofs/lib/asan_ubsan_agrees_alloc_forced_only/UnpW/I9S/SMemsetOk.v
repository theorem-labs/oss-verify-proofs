(* (uncompress 1.4): the memset spec the I9S walks call, for this binary: musl memset at 0x20518
   (132376) with n = 7168 (inflateInit_'s memset of the inflate_state from state + 8), from
   S9Memset7168R.memset7168_run through IGlueMemset.memset_glue. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatSim Hoare ZStores.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW Require S9Memset S9Memset7168R.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import ZStep IGlueMemset.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S Require Import i9s_code.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
(* [comment removed for export] *)

Definition A_MEMSET : Z := 132532.   (* memset, 0x20560 *)

Lemma w64_lit' : forall z (w : word), bv_unsigned w = z -> w64 z = w. Proof. intros z w <-. apply w64_of_word. Qed. Lemma msteps_memset_S9 : msteps_memset R_segs A_MEMSET 7168.
Proof.
  intros regs mem0 rom dst ret H1 Hret H10 H11 H12 Hal Hnw Hok. change (Z.of_nat 7168) with 7168%Z in H12, Hnw. change (store_ok R_segs mem0 dst 7168 = true) with (store_ok R_segs mem0 dst (7 * 1024) = true) in Hok.
  destruct (S9Memset7168R.memset7168_run regs mem0 rom dst ret H1 Hret H10 H11 H12 Hal Hnw Hok)
    as (r' & m' & RUN & EQ & AG).
  exists r'. subst m'. split; [| exact AG]. unfold A_MEMSET, R_segs. rewrite (w64_lit' 132532 (0x205b4%bv : word)) by reflexivity. exact RUN.
Qed.

Theorem memset7168_ok : memset_spec_at R_segs A_MEMSET 7168.
Proof. pose proof (memset_glue R_segs A_MEMSET 7168 msteps_memset_S9) as G. change (Z.of_nat 7168) with 7168%Z in G. exact G. Qed.
End FXG.
