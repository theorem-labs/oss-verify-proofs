(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep ECH_LibState ECH_C1_stmt ECH_C7_stmt ECH_C14_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition RP_R1 : Z := 0x2b2d68.          (* [comment removed for export] *)
Definition A_ECHS_FILE_RP : Z := 0x36488.  (* [comment removed for export] *)
Definition OSSL_ECH_BUFCHUNK : Z := 512.
Definition OSSL_ECH_MAXITER : Z := 32.
(* [comment removed for export] *)
Definition rp_saves (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma rp_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st mb lo : Z),
      0 < st < 2^64 -> 0 < mb < 2^64 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 2368 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 (j1 j2 : list byte),
          ms' = MS (mkR (Z_to_bv 64 RP_R1) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2
                       sp s1 (Z_to_bv 64 OSSL_ECH_BUFCHUNK) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 115) (Z_to_bv 64 0) a4 a5 a6 a7
                       (Z_to_bv 64 mb) (Z_to_bv 64 0) (Z_to_bv 64 st) (Z_to_bv 64 0) s6 s7 s8 s9 s10 (Z_to_bv 64 (bv_unsigned sp + -2296)) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -2368, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -2368)
          /\ rw_cells usegs m1 (bv_unsigned sp + -2368) (CB 72 j1 :: C8 (Z_to_bv 64 0) :: CB 2184 j2 :: rp_saves s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 st) (Z_to_bv 64 mb) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros STR MBR ST CEIL LO MI.
    unfold P_OSSL_ECHSTORE_read_echconfiglist, P_CRYPTO_zalloc, RP_R1, A_ECHS_FILE_RP, OSSL_ECH_BUFCHUNK.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -2368, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. carve_frame 2368%nat ST.
    do 2 st1. do 3 step. do 2 step. step. step.
    (* [comment removed for export] *)
    step. do 13 st1. step. step.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    do 5 step. st1. do 5 step. step.
    finish. unfold rp_saves. exact FR.
  Qed.

  (* [comment removed for export] *)
  Definition RP_R2 : Z := 0x2b2d7c.
  Lemma rp_seg2 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z),
      0 < A < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 RP_R2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) s2 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RP_R1) fc None m (seg_rom usegs)).
  Proof.
    intros until A. intros AR MI. unfold RP_R1, RP_R2, P_BIO_eof.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition RP_R3 : Z := 0x2b2ec8.
  Lemma rp_seg3 :
    forall (rax sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s9 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st mb A lo : Z) (j1 j2 : list byte) (saves : list cell),
      0 <= st < 2^64 -> cells_size saves = 104%nat ->
      rw_cells usegs m (bv_unsigned sp + -2368) (CB 72 j1 :: C8 (Z_to_bv 64 0) :: CB 2184 j2 :: saves) ->
      stk usegs m lo (bv_unsigned sp + -2368) -> hceil <= lo -> lo <= bv_unsigned sp - 2368 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 (j0 : list byte),
          ms' = MS (mkR (Z_to_bv 64 RP_R3) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2
                       sp (Z_to_bv 64 A) (Z_to_bv 64 mb) (Z_to_bv 64 A) (Z_to_bv 64 OSSL_ECH_BUFCHUNK) (Z_to_bv 64 (bv_unsigned sp + -2296)) a4 a5 a6 a7
                       (Z_to_bv 64 mb) (Z_to_bv 64 32) (Z_to_bv 64 1) (Z_to_bv 64 OSSL_ECH_BUFCHUNK) (Z_to_bv 64 A_ECHS_FILE_RP) s7 (Z_to_bv 64 A)
                       (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -2296)) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_read_ex) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -2320, bv_unsigned sp + -2296)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -2368)
          /\ rw_cells usegs m1 (bv_unsigned sp + -2368)
               (CB 48 j0 :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 st) :: C8 (Z_to_bv 64 0) :: CB 2184 j2 :: saves))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 mb) (Z_to_bv 64 0) (Z_to_bv 64 st) (Z_to_bv 64 0) s6 s7 s3 s9 s10 (Z_to_bv 64 (bv_unsigned sp + -2296)) t3 t4 t5 t6)
            F (Z_to_bv 64 RP_R2) fc None m (seg_rom usegs)).
  Proof.
    intros until saves. intros STR SZ FR ST CEIL LO MI. unfold RP_R2, RP_R3, P_BIO_read_ex, A_ECHS_FILE_RP, OSSL_ECH_BUFCHUNK.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -2320, bv_unsigned sp + -2296)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_lit.
    do 2 step. replace (bv_unsigned sp - 4096) with (bv_unsigned sp + -2368 + -1728) by lia. st1.
    do 2 step. replace (bv_unsigned sp - 4096) with (bv_unsigned sp + -2368 + -1728) by lia. st1.
    do 2 step. replace (bv_unsigned sp - 4096) with (bv_unsigned sp + -2368 + -1728) by lia. st1.
    (* [comment removed for export] *)
    do 5 step. step. step. step.
    step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0). try if_lit.
    (* [comment removed for export] *)
    do 5 step. step. step.
    finish.
    all: try exact FR.
  Qed.

  (* [comment removed for export] *)
End S.
