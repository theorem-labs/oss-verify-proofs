(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AsKitK AsWalk ECH_AC8_blockA ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition AFM_PC0 : Z := 0x5534bc.      (* [comment removed for export] *)
Definition AFM_F603 : Z := 0x553640.     (* [comment removed for export] *)
Definition AFM_R603_1 : Z := 0x553648.   (* [comment removed for export] *)
Definition AFM_R603_2 : Z := 0x553664.   (* [comment removed for export] *)
Definition AFM_ZERO3 : Z := 0x55367c.    (* [comment removed for export] *)
Definition AFM_ERRL : Z := 0x553690.     (* [comment removed for export] *)
Definition AFM_ERRL_R1 : Z := 0x55369c.  (* [comment removed for export] *)
Definition AFM_RDUP : Z := 0x55359c.     (* [comment removed for export] *)
Definition AFM_RMAL : Z := 0x5535cc.     (* [comment removed for export] *)
Definition AFM_RCPY : Z := 0x5535e4.     (* [comment removed for export] *)
Definition AFM_JOIN5 : Z := 0x553608.    (* [comment removed for export] *)
Definition AFM_RSPN : Z := 0x553620.     (* [comment removed for export] *)
Definition AFM_RFRE : Z := 0x55363c.     (* [comment removed for export] *)
Definition AFM_DEC : Z := 0x553768.      (* [comment removed for export] *)
Definition AFM_B64 : Z := 0x5536d0.      (* [comment removed for export] *)
Definition A595_R2 : Z := 0x55327c.      (* [comment removed for export] *)
Definition A595_R3 : Z := 0x5532c4.      (* [comment removed for export] *)
Definition A599_R2 : Z := 0x55347c.      (* [comment removed for export] *)
Definition AA_B64_ALPHABET : Z := 0x1124a0.
Definition AERR_LIB_SSL : Z := 20.
Definition AR_INTERNAL_ERROR : Z := 0xc0103.
Definition AR_PASSED_INVALID_ARGUMENT : Z := 0x80106.
Definition AR_PASSED_NULL_PARAMETER : Z := 0xc0102.

(* [comment removed for export] *)
Definition is_bin_fmt (ds : list byte) (L : Z) : bool :=
  match ds with
  | b0 :: b1 :: b2 :: b3 :: _ => (256 * bv_unsigned b0 + bv_unsigned b1 + 2 =? L) && (bv_unsigned b2 =? 254) && (bv_unsigned b3 =? 13)
  | _ => false
  end.

(* [comment removed for export] *)
Lemma ztb_sub_negK : forall n K, Z_to_bv 64 (n + - bv_unsigned (Z_to_bv 64 (- K))) = Z_to_bv 64 (n + K).
Proof.
  intros n K. rewrite unsigned_lit_wrap. rewrite <- (Z_to_bv_mod64 (n + - _)), <- (Z_to_bv_mod64 (n + K)).
  f_equal. replace (n + - ((- K) mod 2^64)) with (n - ((- K) mod 2^64)) by lia. rewrite Zminus_mod_idemp_r. f_equal. lia.
Qed.

(* [comment removed for export] *)
Ltac ck1f_load ACC x :=
  let ACW := fresh "ACW" in let RD := fresh "RD" in let Hx := fresh "Hx" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (ACW : accessible mc (x - x mod 8) 8) by (eapply accessible_sub; [exact ACC| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| lia]) end;
  assert (Hx : 0 <= x) by lia;
  pose proof (accessible_read8 _ _ ACW) as RD;
  replace (sh (x - x mod 8)) with (sh x) in RD by (unfold sh; Z.div_mod_to_equations; nia);
  rewrite <- (sh_shiftr x), ASHADOW_BASE_val in RD by exact Hx;
  replace (wa (Z.shiftr x 3 + 2147450880)) with (Z_to_bv 64 (Z.shiftr x 3 + 2147450880)) in RD by (symmetry; apply wa_of_Z_to_bv; lia);
  step; clear RD ACW Hx; rewrite ?ck8_zxb0, ?ck8_sxb0.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

  (* [comment removed for export] *)
  Definition arp_glue (raA raB target a0v a1v a2v : Z) : Prop :=
    forall (sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      mem_inv asegs m1 ->
      evt asegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 raB) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 a2v) c3 c4 c5 c6 c7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 target) fc None m1 (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 raA) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 raA)) fc None m1 (seg_rom asegs)).

  Local Tactic Notation "glue_tac" constr(raA) integer(n) :=
    unfold arp_glue; intros;
    let v := eval cbv in raA in
    replace (ret_pc (Z_to_bv 64 raA)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]);
    do n step; apply evt_done; do 12 eexists; reflexivity.

  Lemma arp_g595a : arp_glue ALD_R595 A595_R2 P_ERR_set_debug ARP_FILE 595 ARP_FUNC.
  Proof. unfold A595_R2, P_ERR_set_debug, ARP_FILE, ARP_FUNC. glue_tac ALD_R595 7. Qed.
  Lemma arp_g595b : arp_glue A595_R2 A595_R3 P_ERR_set_error AERR_LIB_SSL AR_INTERNAL_ERROR 0.
  Proof. unfold A595_R3, P_ERR_set_error, AERR_LIB_SSL, AR_INTERNAL_ERROR. glue_tac A595_R2 7. Qed.
  Lemma arp_g599a : arp_glue ALD_RN A599_R2 P_ERR_set_debug ARP_FILE 599 ARP_FUNC.
  Proof. unfold A599_R2, P_ERR_set_debug, ARP_FILE, ARP_FUNC. glue_tac ALD_RN 7. Qed.
  Lemma arp_g599b : arp_glue A599_R2 (A599_R2 + 24) P_ERR_set_error AERR_LIB_SSL AR_INTERNAL_ERROR 0.
  Proof. unfold P_ERR_set_error, AERR_LIB_SSL, AR_INTERNAL_ERROR. glue_tac A599_R2 6. Qed.
  Lemma arp_g603a : arp_glue AFM_R603_1 AFM_R603_2 P_ERR_set_debug ARP_FILE 603 ARP_FUNC.
  Proof. unfold AFM_R603_2, P_ERR_set_debug, ARP_FILE, ARP_FUNC. glue_tac AFM_R603_1 7. Qed.
  Lemma arp_g603b : arp_glue AFM_R603_2 AFM_ZERO3 P_ERR_set_error AERR_LIB_SSL AR_PASSED_INVALID_ARGUMENT 0.
  Proof. unfold AFM_ZERO3, P_ERR_set_error, AERR_LIB_SSL, AR_PASSED_INVALID_ARGUMENT. glue_tac AFM_R603_2 6. Qed.

  (* [comment removed for export] *)
  Lemma arp_zero3 :
    forall (s0w gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff A : Z) (w144 w160 w168 w176 w192 w200 w208 w216 w224 w232 : word),
      0 <= q -> q + 464 <= 2^64 ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 (wz ff) w160 w168 w176 (wz A) w192 w200 w208 w216 w224 w232) ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFM_ERRL_R1) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 A) s3 s4 (Z_to_bv 64 0) s6 (Z_to_bv 64 0) (Z_to_bv 64 ff) s9 s10 (Z_to_bv 64 0) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFM_ZERO3) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFM_ZERO3)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros Q1 Q2 SL MI. unfold AFM_ZERO3 in *. retpc. unfold AFM_ERRL_R1, P_BIO_free_all. unfold arp_sg2, wz in SL.
    go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma arp_errl1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFM_ERRL_R1) sp gp tp t0 t1 t2 s0 s1 s11 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFM_ERRL) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold AFM_ERRL, AFM_ERRL_R1, P_BIO_free_all. do 3 step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma afm_seg1 :
    forall (rax s0w gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q L v160 : Z) (w144 w152 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      0 <= L < 5 -> s6 = Z_to_bv 64 L -> 0 <= q -> q + 464 <= 2^64 ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 (wz v160) w168 w176 w184 w192 w200 w208 w216 w224 w232) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFM_R603_1) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 5) a1 a2 a3 a4 a5 a6 a7
                                          s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 v160) s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFM_PC0) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros LR S6 Q1 Q2 SL MI. subst s6. unfold AFM_PC0, AFM_R603_1, P_ERR_new. unfold arp_sg2, wz in SL.
    go. if_cases K2; zify_cond K2; [| kill K2]. clear K2. go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afm_seg2 :
    forall (rax s0w gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q A L n K ff : Z) (ds : list byte) (w144 w152 w168 w192 w200 w208 w216 w224 w232 : word),
      5 <= L < 2^20 -> n + K = L -> 0 <= K < 2^20 -> 0 <= n -> 0 < A -> A + L < 2^63 -> A mod 8 = 0 ->
      0 <= q -> q + 464 <= 2^64 ->
      bytes_at asegs m A ds -> zlength ds = L -> accessible m A 8 ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 (wz ff) w168 (wz ASHB) (wz A) w192 w200 w208 w216 w224 w232) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0,
          ms' = if is_bin_fmt ds L
                then MS (mkR (Z_to_bv 64 AFM_RDUP) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 A) (Z_to_bv 64 L) (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 607) a4 a5 a6 a7
                             (Z_to_bv 64 A) s3 (Z_to_bv 64 ASHB) s5 (Z_to_bv 64 L) (Z_to_bv 64 n) s8 s9 (Z_to_bv 64 ff) (Z_to_bv 64 K) t3 t4 t5 t6)
                        F (Z_to_bv 64 P_CRYPTO_memdup) fc None m (seg_rom asegs)
                else MS (mkR (Z_to_bv 64 AFM_RMAL) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 (L + 1)) (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 166) (Z_to_bv 64 A) a4 a5 a6 a7
                             s2 s3 u0 s5 (Z_to_bv 64 L) (Z_to_bv 64 n) s8 s9 (Z_to_bv 64 ff) (Z_to_bv 64 K) t3 t4 t5 t6)
                        F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 L) (Z_to_bv 64 n) s8 s9 s10 (Z_to_bv 64 K) t3 t4 t5 t6)
            F (Z_to_bv 64 AFM_PC0) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros LR NK KR NR AP AH A8 Q1 Q2 DS DSL ACC SL MI.
    unfold AFM_PC0, AFM_RDUP, AFM_RMAL, P_CRYPTO_memdup, P_CRYPTO_malloc, ARP_FILE. unfold arp_sg2, ASHB, wz in SL.
    unfold zlength in DSL.
    destruct ds as [|b0 [|b1 [|b2 [|b3 ds4]]]]; try (cbn in DSL; exfalso; lia).
    pose proof (abyte_range b0) as B0. pose proof (abyte_range b1) as B1. pose proof (abyte_range b2) as B2. pose proof (abyte_range b3) as B3.
    pose proof (rd_raw _ _ _ 0 b0 DS eq_refl ltac:(lia)) as RD0. replace (A + 0) with A in RD0 by lia.
    pose proof (rd_raw _ _ _ 1 b1 DS eq_refl ltac:(lia)) as RD1.
    pose proof (rd_raw _ _ _ 2 b2 DS eq_refl ltac:(lia)) as RD2.
    pose proof (rd_raw _ _ _ 3 b3 DS eq_refl ltac:(lia)) as RD3.
    pose proof ACC as (_ & AHI' & _).
    (* [comment removed for export] *)
    go. br.
    (* [comment removed for export] *)
    go. ck1f_load ACC A.
    (* [comment removed for export] *)
    go. ck1f_load ACC (A + 1).
    (* [comment removed for export] *)
    go. unfold zxb. rewrite !(unsigned_lit (bv_unsigned _)) by lia.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
    rewrite (unsigned_lit (bv_unsigned b1 + bv_unsigned b0 * 256)) by lia.
    cbn [is_bin_fmt].
    destruct (Z.eqb_spec (256 * bv_unsigned b0 + bv_unsigned b1 + 2) L) as [E1|NE1].
    - replace (n + K - (bv_unsigned b1 + bv_unsigned b0 * 256)) with 2 by (clear - E1 NK; lia).
      go.
      (* [comment removed for export] *)
      ck1f_load ACC (A + 2). go. unfold zxb.
      destruct (Z.eqb_spec (bv_unsigned b2) 254) as [E2|NE2].
      + rewrite E2. go.
        (* [comment removed for export] *)
        ck1f_load ACC (A + 3). go. unfold zxb.
        destruct (Z.eqb_spec (bv_unsigned b3) 13) as [E3|NE3].
        * rewrite E3. go.
          (* [comment removed for export] *)
          step. cbn [andb]. apply evt_done. exists s4. reflexivity.
        * br. cbn [andb].
          (* [comment removed for export] *)
          go. step. replace (n + K + 1) with (L + 1) by (clear - NK; lia). apply evt_done. eexists. reflexivity.
      + br. cbn [andb].
        go. step. replace (n + K + 1) with (L + 1) by (clear - NK; lia). apply evt_done. eexists. reflexivity.
    - if_cases K2; zify_cond K2.
      2: { exfalso. clear - K2 NE1 NK KR NR LR B0 B1. change 18446744073709551615 with (Z.ones 64) in K2. rewrite Z.land_ones in K2 by lia.
           Z.div_mod_to_equations. lia. }
      clear K2. cbn [andb].
      go. step. replace (n + K + 1) with (L + 1) by (clear - NK; lia). apply evt_done. eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afm_seg3 :
    forall (s0w gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff Bb : Z) (w144 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      0 < Bb < 2^64 -> 0 <= q -> q + 464 <= 2^64 ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 (wz ff) w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFM_RDUP) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 Bb) a1 a2 a3 a4 a5 a6 a7
                                          s2 s3 s4 s5 s6 (Z_to_bv 64 Bb) (Z_to_bv 64 ff) s9 s10 (Z_to_bv 64 0) t3 t4 t5 t6)
                                 F (Z_to_bv 64 AFM_DEC) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFM_RDUP) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 Bb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFM_RDUP)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros BR Q1 Q2 SL MI. unfold AFM_RDUP in *. retpc. unfold AFM_DEC. unfold arp_sg2, wz in SL.
    go. br. go_to AFM_DEC. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afm_seg4 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Cp q A : Z) (w144 w152 w160 w168 w176 w192 w200 w208 w216 w224 w232 : word),
      0 < Cp < 2^64 -> 0 <= q -> q + 464 <= 2^64 ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 w176 (wz A) w192 w200 w208 w216 w224 w232) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFM_RCPY) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 Cp) (Z_to_bv 64 A) s6 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 Cp) s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 AASAN_MEMCPY) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFM_RMAL) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 Cp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFM_RMAL)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros CR Q1 Q2 SL MI. unfold AFM_RMAL in *. retpc. unfold AFM_RCPY, AASAN_MEMCPY. unfold arp_sg2, wz in SL.
    go. br. go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afm_seg5 :
    forall (s0w gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q Cp n K L : Z) (cp : list byte) (jb : byte) (w144 w152 w160 w168 w184 w192 w200 w208 w216 w224 w232 : word),
      0 < Cp -> Cp + L + 1 < 2^63 -> n + K = L -> 0 <= n -> 0 <= K -> 0 <= L -> length cp = Z.to_nat L ->
      0 <= q -> q + 464 <= 2^64 ->
      (Cp + L + 1 <= q \/ q + 464 <= Cp) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 (wz ASHB) w184 w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m Cp [CB (Z.to_nat L) cp; CB 1 [jb]] -> accessible m Cp (L + 1) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 (a2' : word),
          ms' = MS (mkR (Z_to_bv 64 AFM_RSPN) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 Cp) (Z_to_bv 64 AA_B64_ALPHABET) a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 (Z_to_bv 64 L) (Z_to_bv 64 n) s8 (Z_to_bv 64 Cp) s10 (Z_to_bv 64 K) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_strspn) fc None m1 (seg_rom asegs)
          /\ munch [(Cp + L, Cp + L + 1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 Cp [CB (Z.to_nat L) cp; CB 1 [Z_to_bv 8 0]])
        (MS (mkR (Z_to_bv 64 AFM_RCPY) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 (Z_to_bv 64 L) (Z_to_bv 64 n) s8 (Z_to_bv 64 Cp) s10 (Z_to_bv 64 K) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFM_RCPY)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros CP CH NK NR KR LR CPL Q1 Q2 DJ SL CELLS ACC MI. unfold AFM_RCPY in *. retpc.
    unfold AFM_RSPN, AA_B64_ALPHABET, P_strspn. unfold arp_sg2, ASHB, wz in SL.
    pose proof (munch_refl [(Cp + L, Cp + L + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply (proj1 (rw_cells_app asegs m Cp [CB (Z.to_nat L) cp] [CB 1 [jb]])) in CELLS. destruct CELLS as [CPa CPb].
    cbn [cells_size csize Nat.add] in CPb. replace (Cp + Z.of_nat (Z.to_nat L + 0)) with (Cp + L) in CPb by lia.
    apply (arw_cells_recut _ _ _ [C1 jb]) in CPb; [| cbn; split; exact I| reflexivity].
    pose proof ACC as (_ & AHI' & _).
    (* [comment removed for export] *)
    go. rewrite zb_lxor_ones by lia. go. replace (Cp + n + K) with (Cp + L) by lia.
    ck1_load ACC (Cp + L) v V1 V2 Ha.
    (* [comment removed for export] *)
    ck_K 12 AFM_JOIN5 KJ.
    { intros tv. red_tset. unfold AFM_JOIN5.
      set (Q := Cp + L) in *. st1. subst Q.
      go. step.
      apply evt_done. eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      apply (proj2 (rw_cells_app asegs _ Cp [CB (Z.to_nat L) cp] [CB 1 [Z_to_bv 8 0]])). split; [exact CPa|].
      cbn [cells_size csize Nat.add]. replace (Cp + Z.of_nat (Z.to_nat L + 0)) with (Cp + L) by lia.
      eapply (arw_cells_recut _ _ [C1 (Z_to_bv 8 0)]); [exact CPb| cbn; split; [reflexivity| exact I]| reflexivity]. }
    unfold AFM_JOIN5 in KJ. ck1_branch_blt (Cp + L) v V1 V2 Ha KJ.
  Qed.

  (* [comment removed for export] *)
  Lemma afm_seg6 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (span : Z),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFM_RFRE) sp gp tp t0 t1 t2 s0 s1 s9 (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 172) a3 a4 a5 a6 a7
                                          s2 s3 (Z_to_bv 64 span) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFM_RSPN) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 span) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFM_RSPN)) fc None m (seg_rom asegs)).
  Proof.
    intros until span. intros MI. unfold AFM_RSPN in *. retpc. unfold AFM_RFRE, P_CRYPTO_free, ARP_FILE.
    do 7 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afm_seg7 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (span L : Z),
      0 <= span < 2^63 -> 0 <= L < 2^63 -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (if span <? L then Z_to_bv 64 AFM_R603_1 else Z_to_bv 64 AFM_RFRE) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                          s2 s3 (Z_to_bv 64 span) s5 (Z_to_bv 64 L) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 (if span <? L then P_ERR_new else AFM_B64)) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFM_RFRE) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 span) s5 (Z_to_bv 64 L) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFM_RFRE)) fc None m (seg_rom asegs)).
  Proof.
    intros until L. intros SR LR MI. unfold AFM_RFRE in *. retpc. unfold AFM_R603_1, AFM_B64, P_ERR_new.
    destruct (Z.ltb_spec span L) as [LT|GE].
    - step. br. step. step. apply evt_done. reflexivity.
    - step. br. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma abio_free_all_null :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 ASHBASE_CELL) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros GSB SHB0 ST CEIL LO MI RAE. unfold P_BIO_free_all.
    acb. unfold AGOT_SHBASE, ASHBASE_CELL, wz in *. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 48%nat ST. do 4 st1. step. step. st1. st1.
    step. if_lit. do 4 step. step. step.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.
End S.
