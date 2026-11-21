(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* the memset spec the I8S walks call, for this binary: musl memset at 0x20518
   (132376) with n = 7168 (inflateInit_'s memset of the inflate_state from state + 8), from
   S8Memset7168R.memset7168_run through IGlueMemset.memset_glue. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import PropExec CatSim Hoare ZStores.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require S8Memset S8Memset7168R.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import ZStep IGlueMemset.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require Import i8s_code.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Definition A_MEMSET : Z := 132592.   (* memset, 0x20518 *)

Lemma w64_lit' : forall z (w : word), bv_unsigned w = z -> w64 z = w. Proof. intros z w <-. apply w64_of_word. Qed. Lemma msteps_memset_S8 : msteps_memset R_segs A_MEMSET 7168.
Proof.
  intros regs mem0 rom dst ret H1 Hret H10 H11 H12 Hal Hnw Hok. change (Z.of_nat 7168) with 7168%Z in H12, Hnw. change (store_ok R_segs mem0 dst 7168 = true) with (store_ok R_segs mem0 dst (7 * 1024) = true) in Hok.
  destruct (S8Memset7168R.memset7168_run regs mem0 rom dst ret H1 Hret H10 H11 H12 Hal Hnw Hok)
    as (r' & m' & RUN & EQ & AG).
  exists r'. subst m'. split; [| exact AG]. unfold A_MEMSET, R_segs. rewrite (w64_lit' 132592 (0x205f0%bv : word)) by reflexivity. exact RUN.
Qed.

Theorem memset7168_ok : memset_spec_at R_segs A_MEMSET 7168.
Proof. pose proof (memset_glue R_segs A_MEMSET 7168 msteps_memset_S8) as G. change (Z.of_nat 7168) with 7168%Z in G. exact G. Qed.
End FXG.
