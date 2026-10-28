(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C7 ECH_AKit ECH_AsKit AsWalk ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AC14_fmt_seg.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AFB_R1 : Z := 0x5536e8.   (* [comment removed for export] *)
Definition AFB_R2 : Z := 0x5536f4.   (* [comment removed for export] *)
Definition AFB_R3 : Z := 0x5536fc.   (* [comment removed for export] *)
Definition AFB_R4 : Z := 0x553714.   (* [comment removed for export] *)
Definition AFB_R5 : Z := 0x553724.   (* [comment removed for export] *)
Definition AFB_R6 : Z := 0x553740.   (* [comment removed for export] *)
Definition AFB_R7 : Z := 0x55375c.   (* [comment removed for export] *)
Definition AFB_631_R1 : Z := 0x5538a4. Definition AFB_631_R2 : Z := 0x554294. Definition AFB_631_R3 : Z := 0x5542ac.   (* [comment removed for export] *)
Definition BIO_FLAGS_BASE64_NO_NL : Z := 0x100.

(* [comment removed for export] *)
Lemma subw_negK : forall n K, 0 <= K <= 512 * 31 -> 1 <= n <= 512 -> bv_swrap 32 (n - Z.land (- K) 18446744073709551615) = n + K.
Proof.
  intros n K KR NR. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ (Z.of_N 32 - 1)) with 2147483648. change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

  (* [comment removed for export] *)
  Lemma afb_seg1 :
    forall (rax sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (n K q : Z)
           (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      0 <= K <= 512 * 31 -> 1 <= n <= 512 -> 0 <= q -> q + 432 <= 2^64 ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFB_R1) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) w184 (Z_to_bv 64 (n + K)) a2 a3 a4 a5 a6 a7 w184 s3 s4 (Z_to_bv 64 (- K)) s6 (Z_to_bv 64 n) s8 (Z_to_bv 64 (n + K)) s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_new_mem_buf) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (- K)) s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AFM_B64) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros KR NR Q1 Q2 SL MI. unfold AFM_B64, AFB_R1, P_BIO_new_mem_buf. unfold arp_sg2 in SL.
    zstep. rewrite subw_negK by lia.
    st1. do 4 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afb_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (M : Z),
      0 < M < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFB_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 M) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 M) t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_f_base64) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFB_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 M) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 AFB_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until M. intros MR MI. unfold AFB_R1 in *. retpc. unfold AFB_R2, P_BIO_f_base64.
    step. br. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afb_seg3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFB_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_new) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFB_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 AFB_R2)) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold AFB_R2 in *. retpc. unfold AFB_R3, P_BIO_new. step. step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma afb_seg4 :
    forall (s0w gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (q ff B : Z) (w144 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      0 < B < 2^64 -> 0 <= q -> q + 432 <= 2^64 ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 (wz ff) w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFB_R4) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 B) (Z_to_bv 64 BIO_FLAGS_BASE64_NO_NL) a2 a3 a4 a5 a6 a7
                                          s2 s3 (Z_to_bv 64 B) s5 s6 s7 (Z_to_bv 64 ff) s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_set_flags) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFB_R3) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFB_R3)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros BR Q1 Q2 SL MI. unfold AFB_R3 in *. retpc. unfold AFB_R4, P_BIO_set_flags, BIO_FLAGS_BASE64_NO_NL. unfold arp_sg2, wz in SL.
    st1. step. br. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afb_seg5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFB_R5) sp gp tp t0 t1 t2 s0 s1 s4 s11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_push) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFB_R4) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 AFB_R4)) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold AFB_R4 in *. retpc. unfold AFB_R5, P_BIO_push. do 4 step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma afb_seg6 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (C : Z),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFB_R6) sp gp tp t0 t1 t2 s0 s1 s6 (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 626) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 C) t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFB_R5) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 AFB_R5)) fc None m (seg_rom asegs)).
  Proof. intros until C. intros MI. unfold AFB_R5 in *. retpc. unfold AFB_R6, P_CRYPTO_malloc, ARP_FILE. do 7 step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma afb_seg7 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb : Z),
      0 < Bb < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFB_R7) sp gp tp t0 t1 t2 s0 s1 s11 (Z_to_bv 64 Bb) s9 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 Bb) s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_read) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFB_R6) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Bb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 AFB_R6)) fc None m (seg_rom asegs)).
  Proof.
    intros until Bb. intros BR MI. unfold AFB_R6 in *. retpc. unfold AFB_R7, P_BIO_read.
    step. br. do 6 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afb_seg8 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (rv q : Z)
           (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      - 2^31 <= rv < 2^31 -> 0 <= q -> q + 432 <= 2^64 ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = if rv <=? 0
                            then MS (mkR (Z_to_bv 64 AFB_631_R1) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs)
                            else MS (mkR (Z_to_bv 64 AFB_R7) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 w176 s5 (Z_to_bv 64 rv) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 AFM_DEC) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFB_R7) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 AFB_R7)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros RR Q1 Q2 SL MI. unfold AFB_R7 in *. retpc. unfold AFB_631_R1, P_ERR_new, AFM_DEC. unfold arp_sg2 in SL.
    destruct (Z.leb_spec rv 0) as [LE0|GT0].
    - step. if_cases K2; zify_cond K2.
      + clear K2. step. step. apply evt_done. reflexivity.
      + exfalso. change 18446744073709551615 with (Z.ones 64) in K0, K1. rewrite Z.land_ones in K0, K1 by (clear; lia). clear - K0 K1 LE0 RR. Z.div_mod_to_equations. lia.
    - step. if_cases K2; zify_cond K2.
      + exfalso. try (change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by (clear; lia); rewrite Z.mod_small in K2 by (clear - GT0 RR; lia)).
        apply Bool.andb_false_iff in K2. destruct K2 as [K2|K2]; [apply Z.ltb_ge in K2| apply Z.ltb_ge in K2]; clear - K2 GT0 RR; lia.
      + clear K0 K1. step. st1. apply evt_done. reflexivity.
  Qed.

  Lemma afb_631a : arp_glue AFB_631_R1 AFB_631_R2 P_ERR_set_debug ARP_FILE 631 ARP_FUNC.
  Proof.
    unfold arp_glue. intros. unfold AFB_631_R1 in *. retpc. unfold AFB_631_R2, P_ERR_set_debug, ARP_FILE, ARP_FUNC.
    do 8 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  Lemma afb_631b : arp_glue AFB_631_R2 AFB_631_R3 P_ERR_set_error AERR_LIB_SSL AR_INTERNAL_ERROR 0.
  Proof.
    unfold arp_glue. intros. unfold AFB_631_R2 in *. retpc. unfold AFB_631_R3, P_ERR_set_error, AERR_LIB_SSL, AR_INTERNAL_ERROR.
    do 6 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afb_seg9 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFM_ERRL_R1) sp gp tp t0 t1 t2 s0 s1 s11 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFB_631_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 AFB_631_R3)) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold AFB_631_R3 in *. retpc. unfold AFM_ERRL_R1, P_BIO_free_all.
    do 5 step. apply evt_done. reflexivity.
  Qed.
End S.
