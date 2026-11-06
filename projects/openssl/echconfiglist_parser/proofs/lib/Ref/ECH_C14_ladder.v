(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_C1_stmt ECH_C7_stmt ECH_C14_stmt ECH_C14_bio2buf.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LD_R1 : Z := 0x26c760.   (* [comment removed for export] *)
Definition LD_R2 : Z := 0x26c788.   (* [comment removed for export] *)
Definition LD_R3 : Z := 0x26c7b0.   (* [comment removed for export] *)
Definition LD_RD : Z := 0x26c7cc.   (* [comment removed for export] *)
Definition LD_RC : Z := 0x26c618.   (* [comment removed for export] *)
Definition LD_RF : Z := 0x26c634.   (* [comment removed for export] *)
Definition LD_OK : Z := 0x26c810.   (* [comment removed for export] *)
Definition LD_RN : Z := 0x26c7e8.   (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma ld_seg1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb : Z),
      s2 = Z_to_bv 64 mb -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom rsegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RP_R3) fc None m (seg_rom rsegs)).
  Proof.
    intros until mb. intros S2 MI. subst s2. unfold RP_R3, LD_R1, P_BIO_eof.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_seg2_eof :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb e : Z),
      s2 = Z_to_bv 64 mb -> 0 < e < 2^64 -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_RD) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom rsegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_R1) fc None m (seg_rom rsegs)).
  Proof.
    intros until e. intros S2 ER MI. subst s2. unfold LD_R1, LD_RD, P_BIO_eof.
    step. try (if_cases K2; zify_cond K2; [| kill K2]; clear K2).
    step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_seg2_grow :
    forall (rax sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A rbp K : Z),
      0 <= K -> K + 1024 < 2^63 ->
      rw_cells rsegs m rbp [C8 (wz 512)] -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_R2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 (K + 1024)) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 128) a4 a5 a6 a7
                       s2 (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 rbp) s5 s6 s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_realloc) fc None m (seg_rom rsegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 rbp) s5 s6 s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_R1) fc None m (seg_rom rsegs)).
  Proof.
    intros until K. intros K0 K1 RB MI. unfold LD_R1, LD_R2, P_CRYPTO_realloc, A_ECHS_FILE_RP. unfold wz in RB.
    step. try if_lit.
    step. step. step. try if_lit.
    do 4 step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_seg3 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb A' K : Z),
      s2 = Z_to_bv 64 mb -> 0 < A' < 2^64 -> 0 <= K -> A' + K + 1024 < 2^64 ->
      mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_R3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (K + 512)) (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 A') (Z_to_bv 64 (A' + K + 512)) (Z_to_bv 64 (- (K + 512))) (Z_to_bv 64 (A' + K)) (Z_to_bv 64 (- (K + 512))) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom rsegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (- K)) (Z_to_bv 64 K) (Z_to_bv 64 (- K)) t3 t4 t5 t6)
            F (Z_to_bv 64 LD_R2) fc None m (seg_rom rsegs)).
  Proof.
    intros until K. intros S2 AR K0 K1 MI. subst s2. unfold LD_R2, LD_R3, P_BIO_eof.
    step. try (if_cases K2; zify_cond K2; [kill K2|]; clear K2).
    do 9 step.
    replace (- K + -512) with (- (K + 512)) by lia.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_seg4 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb c : Z),
      s2 = Z_to_bv 64 mb -> 2 <= c <= 32 -> 2352 <= bv_unsigned s0 -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 RP_R3) sp gp tp t0 t1 t2 s0 s7 (Z_to_bv 64 mb) s8 (Z_to_bv 64 512) (Z_to_bv 64 (bv_unsigned s0 + -2240)) a4 a5 a6 a7
                       s2 s3 s4 s5 (Z_to_bv 64 (c - 1)) s7 s8 s9 s1 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_read_ex) fc None m (seg_rom rsegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 c) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_R3) fc None m (seg_rom rsegs)).
  Proof.
    intros until c. intros S2 CR S0R MI. subst s2. unfold LD_R3, RP_R3, P_BIO_read_ex.
    pose proof (word_range s0) as S0W.
    step. step. step. try if_lit.
    step. rewrite (unsigned_lit c) by lia. rewrite swrap32_small by lia. replace (c + -1) with (c - 1) by lia.
    step. try (if_cases K2; zify_cond K2; [kill K2|]; clear K2).
    do 5 step. step. step.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_seg4_cap :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb : Z),
      s2 = Z_to_bv 64 mb -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_RC) sp gp tp t0 t1 t2 s0 s7 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 (Z_to_bv 64 0) s7 s8 s9 s1 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom rsegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 1) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_R3) fc None m (seg_rom rsegs)).
  Proof.
    intros until mb. intros S2 MI. subst s2. unfold LD_R3, LD_RC, P_BIO_eof.
    step. step. step. try if_lit.
    step. step. try if_lit.
    step. step. step. step.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_segc1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb e : Z),
      s2 = Z_to_bv 64 mb -> 0 < e < 2^64 -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_RC) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s1 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom rsegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RP_R2) fc None m (seg_rom rsegs)).
  Proof.
    intros until e. intros S2 ER MI. subst s2. unfold RP_R2, LD_RC, P_BIO_eof.
    step. try (if_cases K2; zify_cond K2; [kill K2|]; clear K2).
    step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_segc2 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv rsegs m ->
      evt rsegs (fun ms' => exists a0',
          ms' = MS (mkR (Z_to_bv 64 LD_RF) sp gp tp t0 t1 t2 s0 s7 s7 (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 140) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs) /\ a0' = a0)
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LD_RC) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI. unfold LD_RC, LD_RF, P_CRYPTO_free, A_ECHS_FILE_RP.
    do 7 step. apply evt_done. exists a0. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_segE_ok :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e rbp n K : Z),
      0 < e < 2^64 -> 0 <= n <= 512 -> 0 <= K < 2^62 -> n + K < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      rw_cells rsegs m rbp [C8 (wz n)] -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OSSL_ECH_MAX_ECHCONFIG_LEN) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 (Z_to_bv 64 n) s5 s6 (Z_to_bv 64 (n + K)) s8 s9 s10 (Z_to_bv 64 (- K)) t3 t4 t5 t6)
                   F (Z_to_bv 64 LD_OK) fc None m (seg_rom rsegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 rbp) s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (- K)) t3 t4 t5 t6)
            F (Z_to_bv 64 LD_RD) fc None m (seg_rom rsegs)).
  Proof.
    intros until K. intros ER NR KR GATE RB MI. unfold LD_RD, LD_OK, OSSL_ECH_MAX_ECHCONFIG_LEN in *. unfold wz in RB.
    step. try (if_cases K2; zify_cond K2; [kill K2|]; clear K2).
    step. step. step. rewrite ztb_sub_negK.
    step. try (if_cases K2; zify_cond K2; [| kill K2]; clear K2).
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_segE_big :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e rbp n K : Z),
      0 < e < 2^64 -> 0 <= n <= 512 -> 0 <= K < 2^62 -> OSSL_ECH_MAX_ECHCONFIG_LEN <= n + K ->
      rw_cells rsegs m rbp [C8 (wz n)] -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 LD_RN) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OSSL_ECH_MAX_ECHCONFIG_LEN) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 (Z_to_bv 64 n) s5 s6 (Z_to_bv 64 (n + K)) s8 s9 s10 (Z_to_bv 64 (- K)) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 rbp) s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (- K)) t3 t4 t5 t6)
            F (Z_to_bv 64 LD_RD) fc None m (seg_rom rsegs)).
  Proof.
    intros until K. intros ER NR KR GATE RB MI. unfold LD_RD, LD_RN, P_ERR_new, OSSL_ECH_MAX_ECHCONFIG_LEN in *. unfold wz in RB.
    step. try (if_cases K2; zify_cond K2; [kill K2|]; clear K2).
    step. step. step. rewrite ztb_sub_negK.
    step. try (if_cases K2; zify_cond K2; [kill K2|]; clear K2).
    step. step.
    apply evt_done. reflexivity.
  Qed.
End S.
