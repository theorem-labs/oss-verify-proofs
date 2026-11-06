(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_UbKit ECH_C1_stmt ECH_C7_stmt ECH_C14_stmt ECH_C14_bio2buf.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LD_HEAD : Z := 0x2b2ea4. (* [comment removed for export] *)
Definition LD_R1 : Z := 0x2b2ed8.   (* [comment removed for export] *)
Definition LD_R2 : Z := 0x2b2f00.   (* [comment removed for export] *)
Definition LD_R3 : Z := 0x2b2f38.   (* [comment removed for export] *)
Definition LD_RD : Z := 0x2b2f50.   (* [comment removed for export] *)
Definition LD_CAP : Z := 0x2b2d80.  (* [comment removed for export] *)
Definition LD_RC : Z := 0x2b2d90.   (* [comment removed for export] *)
Definition LD_FAIL : Z := 0x2b2d94. (* [comment removed for export] *)
Definition LD_RF : Z := 0x2b2dac.   (* [comment removed for export] *)
Definition LD_OK : Z := 0x2b2f94.   (* [comment removed for export] *)
Definition LD_RN : Z := 0x2b2f6c.   (* [comment removed for export] *)
Definition OSSL_ECH_MAX_ECHCONFIG_LEN : Z := 1500.

(* [comment removed for export] *)
Lemma ztb_sub_negK : forall n K, Z_to_bv 64 (n + - bv_unsigned (Z_to_bv 64 (- K))) = Z_to_bv 64 (n + K).
Proof.
  intros n K. rewrite unsigned_lit_wrap. rewrite <- (Z_to_bv_mod64 (n + - _)), <- (Z_to_bv_mod64 (n + K)).
  f_equal. replace (n + - ((- K) mod 2^64)) with (n - ((- K) mod 2^64)) by lia. rewrite Zminus_mod_idemp_r. f_equal. lia.
Qed.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.

  (* [comment removed for export] *)
  Lemma ld_seg1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb : Z),
      s2 = Z_to_bv 64 mb -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RP_R3) fc None m (seg_rom usegs)).
  Proof.
    intros until mb. intros S2 MI. subst s2. unfold RP_R3, LD_R1, P_BIO_eof.
    step. br.
    step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_seg2_eof :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb e : Z),
      s2 = Z_to_bv 64 mb -> 0 < e < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_RD) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_R1) fc None m (seg_rom usegs)).
  Proof.
    intros until e. intros S2 ER MI. subst s2. unfold LD_R1, LD_RD, P_BIO_eof.
    step. if_cases K2; zify_cond K2; [| kill K2]; clear K2.
    step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_seg2_grow :
    forall (rax sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s8 s9 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A rbp K : Z),
      0 <= K -> K + 1024 < 2^63 ->
      rw_cells usegs m rbp [C8 (wz 512)] -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_R2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 (K + 1024)) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 128) a4 a5 a6 a7
                       s2 s3 s4 (Z_to_bv 64 512) (Z_to_bv 64 A_ECHS_FILE_RP) s7 (Z_to_bv 64 (K + 1024)) s9 (Z_to_bv 64 K) (Z_to_bv 64 rbp) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_realloc) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 512) (Z_to_bv 64 A_ECHS_FILE_RP) s7 s8 s9 (Z_to_bv 64 K) (Z_to_bv 64 rbp) t3 t4 t5 t6)
            F (Z_to_bv 64 LD_R1) fc None m (seg_rom usegs)).
  Proof.
    intros until K. intros K0 K1 RB MI. unfold LD_R1, LD_R2, P_CRYPTO_realloc, A_ECHS_FILE_RP. unfold wz in RB.
    step. if_lit.
    step. step. if_lit.
    do 5 step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_seg3 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb A' K : Z),
      s2 = Z_to_bv 64 mb -> 0 < A' < 2^64 -> 0 <= K -> A' + K + 1024 < 2^64 ->
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_R3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) (Z_to_bv 64 (A' + K + 1024)) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (Z_to_bv 64 512) s6 (Z_to_bv 64 A') (Z_to_bv 64 (A' + K + 512)) (Z_to_bv 64 (- (K + 512))) (Z_to_bv 64 (K + 512)) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 512) s6 s7 (Z_to_bv 64 (K + 1024)) (Z_to_bv 64 (- K)) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_R2) fc None m (seg_rom usegs)).
  Proof.
    intros until K. intros S2 AR K0 K1 MI. subst s2. unfold LD_R2, LD_R3, P_BIO_eof.
    step. br.
    step.
    (* [comment removed for export] *)
    step. ubnot. step. br.
    (* [comment removed for export] *)
    step. step. step. br. step. br.
    do 3 step. step. step. step.
    replace (- K + -512) with (- (K + 512)) by lia.
    replace (A' + K + 1024) with (A' + K + 1024) by lia.
    apply evt_done. repeat rewrite <- Z.add_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_seg4 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb c : Z),
      s2 = Z_to_bv 64 mb -> 2 <= c <= 32 -> 2368 <= bv_unsigned s0 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 RP_R3) sp gp tp t0 t1 t2 s0 s7 (Z_to_bv 64 mb) s8 (Z_to_bv 64 512) (Z_to_bv 64 (bv_unsigned s0 + -2296)) a4 a5 a6 a7
                       s2 (Z_to_bv 64 (c - 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_read_ex) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 c) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_R3) fc None m (seg_rom usegs)).
  Proof.
    intros until c. intros S2 CR S0R MI. subst s2. unfold LD_R3, RP_R3, P_BIO_read_ex.
    pose proof (word_range s0) as S0W.
    step. step. if_lit.
    step. rewrite (unsigned_lit c) by lia. rewrite swrap32_small by lia. replace (c + -1) with (c - 1) by lia.
    step. br.
    do 5 step. step. step.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_seg4_cap :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb : Z),
      s2 = Z_to_bv 64 mb -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_RC) sp gp tp t0 t1 t2 s0 s7 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_R3) fc None m (seg_rom usegs)).
  Proof.
    intros until mb. intros S2 MI. subst s2. unfold LD_R3, LD_RC, P_BIO_eof.
    step. step. if_lit.
    step. step. if_lit.
    step. step. step. step.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_segc1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb e : Z),
      s2 = Z_to_bv 64 mb -> 0 < e < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_RC) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s1 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RP_R2) fc None m (seg_rom usegs)).
  Proof.
    intros until e. intros S2 ER MI. subst s2. unfold RP_R2, LD_RC, P_BIO_eof.
    step. br.
    step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_segc2 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_RF) sp gp tp t0 t1 t2 s0 s7 s7 (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 140) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_RC) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold LD_RC, LD_RF, P_CRYPTO_free, A_ECHS_FILE_RP.
    do 7 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_segf :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_RF) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 140) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_FAIL) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold LD_FAIL, LD_RF, P_CRYPTO_free, A_ECHS_FILE_RP.
    do 6 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_segE_ok :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e rbp n K : Z),
      0 < e < 2^64 -> 0 <= n <= 512 -> 0 <= K < 2^62 -> n + K < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      rw_cells usegs m rbp [C8 (wz n)] -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OSSL_ECH_MAX_ECHCONFIG_LEN - 1)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (n + K)) (Z_to_bv 64 n) s9 (Z_to_bv 64 K) (Z_to_bv 64 rbp) t3 t4 t5 t6)
                   F (Z_to_bv 64 LD_OK) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 K) (Z_to_bv 64 rbp) t3 t4 t5 t6)
            F (Z_to_bv 64 LD_RD) fc None m (seg_rom usegs)).
  Proof.
    intros until K. intros ER NR KR GATE RB MI. unfold LD_RD, LD_OK, OSSL_ECH_MAX_ECHCONFIG_LEN in *. unfold wz in RB.
    step. br.
    step. step. step.
    step. if_cases K2; zify_cond K2; [| kill K2]; clear K2.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_segE_big :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e rbp n K : Z),
      0 < e < 2^64 -> 0 <= n <= 512 -> 0 <= K < 2^62 -> OSSL_ECH_MAX_ECHCONFIG_LEN <= n + K ->
      rw_cells usegs m rbp [C8 (wz n)] -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_RN) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OSSL_ECH_MAX_ECHCONFIG_LEN - 1)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (n + K)) (Z_to_bv 64 n) s9 (Z_to_bv 64 K) (Z_to_bv 64 rbp) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 K) (Z_to_bv 64 rbp) t3 t4 t5 t6)
            F (Z_to_bv 64 LD_RD) fc None m (seg_rom usegs)).
  Proof.
    intros until K. intros ER NR KR GATE RB MI. unfold LD_RD, LD_RN, P_ERR_new, OSSL_ECH_MAX_ECHCONFIG_LEN in *. unfold wz in RB.
    step. br.
    step. step. step.
    step. if_cases K2; zify_cond K2; [kill K2|]; clear K2.
    step. step.
    apply evt_done. reflexivity.
  Qed.
End S.
