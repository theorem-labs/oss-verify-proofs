(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list MallocBlocks.block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis RM : rmalloc_rz_stmt HK.
Hypothesis RF : rfree_rz_stmt HK.
Hypothesis RR : rrealloc_rz_stmt HK.
Hypothesis RRN : rrealloc_null_rz_stmt HK.

(* [comment removed for export] *)
Ltac rz_to TGT HKx :=
  let Hh := fresh "Hh" in let Hl := fresh "Hl" in
  destruct (HKS _ _ _ _ HKx) as [Hh Hl];
  eapply (rz_evt (fun ms' => ms' = TGT)); [ | exact Hh | exact Hl | intros ? ->; clear Hh Hl ].

Lemma ywrap_malloc_spec : ywrap_malloc_stmt HK.
Proof.
  unfold ywrap_malloc_stmt. intros until K. intros K0 HK0 AX SPB STK CEIL LO ERR MI TP A1 N NR CONT. unfold NUSERc in N.
  subst a1. unfold RY_MALLOC_W, wz in *.
  rz_to (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom usegs)) HK0.
  { zstep. zstep. rewrite (land_M32_small n) by lia. zstep. apply evt_done. unfold RMALLOC_SYM. reflexivity. }
  eapply RM; try eassumption; try reflexivity.
  unfold RY_WRAP_STACK, RMALLOC_STACK in *. lia.
Qed.

Lemma ywrap_free_spec : ywrap_free_stmt HK.
Proof.
  unfold ywrap_free_stmt. intros until K. intros K0 HK0 IN AX SPB STK CEIL LO ERR MI TP A1 CONT.
  subst a1. unfold RY_FREE_W, wz in *.
  rz_to (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom usegs)) HK0.
  { zstep. zstep. apply evt_done. unfold RFREE_SYM. reflexivity. }
  eapply RF; try eassumption; try reflexivity.
  unfold RY_WRAP_STACK, RFREE_STACK in *. lia.
Qed.

Lemma ywrap_free_null_spec : ywrap_free_null_stmt.
Proof.
  unfold ywrap_free_null_stmt. intros until m. intros A1. subst a1. unfold RY_FREE_W, wz.
  zstep. zstep. eapply evt_cut; [eapply rfree_null_spec; reflexivity|].
  intros ms' ->. apply evt_done. unfold ywrap_free_null_rpost. repeat eexists.
Qed.

Lemma ywrap_realloc_spec : ywrap_realloc_stmt HK.
Proof.
  unfold ywrap_realloc_stmt. intros until K. intros K0 HK0 IN OLD OLEN AX SPB STK CEIL LO ERR MI TP A1 A2 N NR CONT. unfold NUSERc in N.
  subst a1 a2. unfold RY_REALLOC_W, wz in *.
  rz_to (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom usegs)) HK0.
  { zstep. zstep. rewrite (land_M32_small n) by lia. zstep. zstep. zstep. apply evt_done. unfold RREALLOC_SYM. reflexivity. }
  eapply RR; try eassumption; try reflexivity.
  all: unfold RY_WRAP_STACK, RREALLOC_STACK in *; lia.
Qed.

Lemma ywrap_realloc_null_spec : ywrap_realloc_null_stmt HK.
Proof.
  unfold ywrap_realloc_null_stmt. intros until K. intros K0 HK0 AX SPB STK CEIL LO ERR MI TP A1 A2 N NR CONT. unfold NUSERc in N.
  subst a1 a2. unfold RY_REALLOC_W, wz in *.
  rz_to (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom usegs)) HK0.
  { zstep. zstep. rewrite (land_M32_small n) by lia. zstep. zstep. zstep. apply evt_done. unfold RREALLOC_SYM. reflexivity. }
  eapply RRN; try eassumption; try reflexivity.
  all: unfold RY_WRAP_STACK, RREALLOC_STACK in *; lia.
Qed.
End S.
End RC__1.
