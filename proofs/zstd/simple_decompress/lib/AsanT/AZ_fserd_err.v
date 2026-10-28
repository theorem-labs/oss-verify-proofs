(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_cnt1
     AF_fse_rd_count AF_fse_rd_zero AF_fse_rd_loop AF_fse_rd_hdr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Local Ltac acc_hint ::= rdA_acc_hint.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition rd_finvA (C : rdctxA) (m1 : amem) (nc : list Z) (msvw tlw : word) : Prop :=
  u8arr bsegs m1 (a_NC C) (u16s (map (Z_to_bv 64) nc)) /\ length nc = length (a_rt0 C)
  /\ bytes_at bsegs m1 (a_BUF C) (map (Z_to_bv 8) (a_buf C))
  /\ rw_cells bsegs m1 (a_MSVP C) [C4 msvw]
  /\ rw_cells bsegs m1 (a_TLP C) [C4 tlw]
  /\ (exists csA, rw_cells bsegs m1 (a_SPA C) csA /\ cells_size csA = 56%nat)
  /\ stk bsegs m1 (a_lo C) (a_SPA C)
  /\ munch (rd_WA C) (a_m C) m1 /\ wmono bsegs (a_m C) m1 /\ mem_inv bsegs m1.

Lemma rd_finvA_of_inv : forall C m1 nc msvw tlw, rd_invA C m1 nc msvw tlw -> rd_finvA C m1 nc msvw tlw.
Proof.
  intros C m1 nc msvw tlw (ARR & LNC & HBUF & HMSV & HTL & (j16 & FR) & ST & MU & WM & MI). unfold rd_finvA.
  repeat (split; [assumption|]). split; [| split; [exact ST| split; [exact MU| split; [exact WM| exact MI]]]].
  exists (FRA_main C j16). split; [exact FR| reflexivity].
Qed.

(* [comment removed for export] *)
Definition rd_finA_post (C : rdctxA) (r : Z) : machine_state -> Prop :=
  fun ms' => exists m' nc (msvw tlw : word) (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word),
    ms' = MS (mkR x1 (Z_to_bv 64 (a_SPA C)) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 (a_SPA C)) x10 (Z_to_bv 64 r)
                 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (a_FF C)) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (a_FF C))
                 (Z_to_bv 64 (Z.shiftr (a_FF C) 3 + 2147450880)) x27 x28 x29 x30 x31)
             (a_F C) (Z_to_bv 64 0xab14c) (a_fc C) None m' (seg_rom bsegs)
    /\ rd_finvA C m' nc msvw tlw.

Lemma rd_finA_of_main : forall C rt msv tl n ms, rd_mainA_post C rt msv tl n ms -> rd_finA_post C n ms.
Proof.
  intros C rt msv tl n ms (m' & x6 & x10 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & x23 & x30 & -> & INV).
  unfold rd_finA_post, rd_lstA. do 4 eexists. do 22 eexists. split; [reflexivity | apply rd_finvA_of_inv; exact INV].
Qed.

Section Err.
  Variable C : rdctxA.
  Variable RNG : footprint.
  Hypothesis OK : rd_okA C.
  Hypothesis SH : rd_shA C.
  Hypothesis RNGS : rd_rngA C RNG.
  Variable tl : Z.
  Hypothesis Htl : 5 <= tl <= 15.

  Notation buf := (a_buf C).
  Notation msv1 := (a_msv0 C + 1).
  Notation BUF := (a_BUF C).
  Notation NC := (a_NC C).
  Notation MSVP := (a_MSVP C).
  Notation TLP := (a_TLP C).
  Notation SPA := (a_SPA C).
  Notation FF := (a_FF C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
  Ltac zify_lts K :=
    unfold bv_lts in K; rewrite ?land7_mod in K;
    rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
    zify_bool K.

  (* [comment removed for export] *)
  Lemma exit_errA : forall s m1 msvw (x6 x11 x14 x15 x17 x19 x23 x30 : word),
    rd_invA C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> rd_brk_okA C s ->
    (r_remaining s = 1 -> r_charnum s <= msv1) -> (r_remaining s <> 1 \/ 32 < r_bitCount s) ->
    evtF bsegs RNG (rd_finA_post C (2^64 - 20)) (rd_exitA C s m1 x6 x11 x14 x15 x17 x19 x23 x30).
  Proof.
    intros s m1 msvw x6 x11 x14 x15 x17 x19 x23 x30 INV (B1 & B2 & B3 & B4 & B5) HCN HBAD.
    pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & _).
    unfold rd_exitA, rd_lstA.
    destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
    change (2^31) with 2147483648 in *.
    zstep. zstep. zstep. if_cases K; zify_cond K.                             (* [comment removed for export] *)
    - apply evtF_done. unfold rd_finA_post. do 4 eexists. do 22 eexists.
      split; [| apply rd_finvA_of_inv; exact INV]. replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv_eq; reflexivity). reflexivity.
    - zstep. if_cases K2; zify_cond K2; [| exfalso; lia].                       (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3; rewrite ?signed_lit in K3 by lia; [| exfalso; lia].   (* [comment removed for export] *)
      apply evtF_done. unfold rd_finA_post. do 4 eexists. do 22 eexists.
      split; [| apply rd_finvA_of_inv; exact INV]. replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv_eq; reflexivity). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_run_genA : forall (POSTF : machine_state -> Prop) f s sF m1 msvw (x12 x14 x15 x19 x30 : word),
    rloop buf msv1 f s = Ok sF ->
    rd_invA C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    (forall m3 z6 z11 z14 z15 z17 z19 z23 z30, rd_invA C m3 (r_nc sF) msvw (Z_to_bv 64 tl) -> rd_brk_okA C sF ->
       evtF bsegs RNG POSTF (rd_exitA C sF m3 z6 z11 z14 z15 z17 z19 z23 z30)) ->
    evtF bsegs RNG POSTF (rd_headA C s m1 x12 x14 x15 x19 x30).
  Proof.
    intros POSTF. induction f as [|f IH]; intros s sF m1 msvw x12 x14 x15 x19 x30 RL INV HC HP HB32 KX.
    { cbn in RL. discriminate RL. }
    cbn [rloop] in RL.
    assert (CNT : forall s1 m2 (y12 y14 y15 y19 y30 : word),
              rd_invA C m2 (r_nc s1) msvw (Z_to_bv 64 tl) -> CTL msv1 (a_rt0 C) tl s1 -> POS buf s1 -> r_bitCount s1 < 32 ->
              (let! fl := rcount_block buf msv1 s1 in match fl with Brk s' => Ok s' | Cont s' => rloop buf msv1 f s' end) = Ok sF ->
              evtF bsegs RNG POSTF (rd_cntA C s1 m2 y12 y14 y15 y19 y30)).
    { intros s1 m2 y12 y14 y15 y19 y30 INV1 HC1 HP1 HB1 RL1.
      destruct (rcount_total buf (buf_all_bytesA C OK) (buf_h8A C OK) msv1 (a_rt0 C) (msv1_okA C OK) tl Htl s1 HC1 HP1 HB1) as (fl & EF & HF).
      rewrite EF in RL1. cbn [bind] in RL1.
      eapply (count_runA C RNG OK SH RNGS tl Htl POSTF s1 m2 msvw (Z_to_bv 64 tl) fl); try eassumption.
      - intros s' m3 z6 z11 z14 z15 z17 z19 z23 z30 -> INV3 BK. injection RL1 as ->.
        eapply KX; assumption.
      - intros s' m3 z12 z14 z15 z19 z30 -> INV3. destruct HF as (HC3 & HP3 & HB3 & _).
        eapply IH; eassumption. }
    unfold rbody in RL.
    destruct (r_previous0 s) eqn:EP.
    - destruct (rzero_total buf (buf_all_bytesA C OK) (buf_h8A C OK) msv1 (a_rt0 C) (msv1_okA C OK) tl Htl s HC HP HB32) as (flz & EZ & HZ).
      rewrite EZ in RL. cbn [bind] in RL.
      unfold rd_headA. rewrite EP.
      eapply (zero_runA C RNG OK SH RNGS POSTF tl s m1 msvw (Z_to_bv 64 tl) flz); try eassumption.
      + intros s' z6 z11 z14 z15 z17 z19 z23 z30 -> EN BK. cbn [bind] in RL. injection RL as ->.
        eapply KX; [rewrite EN; exact INV | exact BK].
      + intros s' z12 z14 z15 z19 z30 -> EN. destruct HZ as (HC1 & HP1 & HB1 & _).
        apply CNT; try assumption. rewrite EN. exact INV.
    - cbn [bind] in RL.
      pose proof (CNT s m1) as CNT'. unfold rd_cntA in CNT'.
      unfold rd_headA. rewrite EP.
      apply CNT'; assumption.
  Qed.

  Corollary loop_run_genA' : forall (POSTF : machine_state -> Prop) f s sF m1 msvw pc (x6 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
    rloop buf msv1 f s = Ok sF ->
    rd_invA C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    (forall m3 z6 z11 z14 z15 z17 z19 z23 z30, rd_invA C m3 (r_nc sF) msvw (Z_to_bv 64 tl) -> rd_brk_okA C sF ->
       evtF bsegs RNG POSTF (rd_exitA C sF m3 z6 z11 z14 z15 z17 z19 z23 z30)) ->
    pc = (if r_previous0 s then 0xaad54 else 0xaaed0) ->
    x6 = Z_to_bv 64 (r_bitCount s) -> x10 = Z_to_bv 64 (BUF + r_ip s) -> x11 = Z_to_bv 64 (bv_swrap 32 (r_bitStream s)) ->
    x13 = Z_to_bv 64 (r_charnum s) -> x16 = Z_to_bv 64 (r_remaining s) -> x17 = Z_to_bv 64 (r_threshold s) ->
    x23 = Z_to_bv 64 (r_nbBits s) ->
    evtF bsegs RNG POSTF (rd_lstA C pc m1 x6 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30).
  Proof.
    intros POSTF f s sF m1 msvw pc x6 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 RL INV HC HP HB KX -> -> -> -> -> -> -> ->.
    exact (loop_run_genA POSTF f s sF m1 msvw x12 x14 x15 x19 x30 RL INV HC HP HB KX).
  Qed.
End Err.

Section HdrGen.
  Variable C : rdctxA.
  Variable RNG : footprint.
  Hypothesis OK : rd_okA C.
  Hypothesis SH : rd_shA C.
  Hypothesis RNGS : rd_rngA C RNG.

  Notation buf := (a_buf C).
  Notation msv1 := (a_msv0 C + 1).
  Notation BUF := (a_BUF C).
  Notation NC := (a_NC C).
  Notation MSVP := (a_MSVP C).
  Notation TLP := (a_TLP C).
  Notation SPA := (a_SPA C).
  Notation FF := (a_FF C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
  Ltac zify_lts K :=
    unfold bv_lts in K; rewrite ?land7_mod in K;
    rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
    zify_bool K.

  (* [comment removed for export] *)
  Lemma hd_tail_genA : forall (POSTF : machine_state -> Prop) m1 tl0 sF j0 j24 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
    u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
    rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
    bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells bsegs m1 SPA (FRA_mid C j0 j24) ->
    stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
    Z.land (le32 buf 0) 15 <= 10 ->
    rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) = Ok sF ->
    (forall m3 z6 z11 z14 z15 z17 z19 z23 z30,
       rd_invA C m3 (r_nc sF) (Z_to_bv 64 (a_msv0 C)) (Z_to_bv 64 (Z.land (le32 buf 0) 15 + 5)) -> rd_brk_okA C sF ->
       evtF bsegs RNG POSTF (rd_exitA C sF m3 z6 z11 z14 z15 z17 z19 z23 z30)) ->
    evtF bsegs RNG POSTF
      (MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
               (Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
          (a_F C) (Z_to_bv 64 0xaacdc) (a_fc C) None m1 (seg_rom bsegs)).
  Proof.
    intros POSTF m1 tl0 sF j0 j24 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI HX RL KX.
    pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SNT & _ & SMT & _ & STB & _).
    pose proof (okA_lin C OK) as (HH' & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
                                 & TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
    pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
    pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
    unfold FRA_mid, ASHB in FRM. unfold rd_WA, RDA_CALLEE in MU.
    destruct (rd_s0_inv buf msv1 (a_rt0 C) (buf_all_bytesA C OK) (proj1 HH) ltac:(lia) HX) as (HC0 & HP0 & HB0').
    pose proof (le32_range buf 0 (buf_all_bytesA C OK)) as RW.
    set (W := le32 buf 0) in *.
    remember (Z.land W 15) as x eqn:Ex.
    assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
    assert (P5 : 32 <= 2 ^ (x + 5) <= 32768).
    { split; [change 32 with (2^5)| change 32768 with (2^15)]; apply Z.pow_le_mono_r; lia. }
    assert (LWS : length (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C))) = length (a_rt0 C))
      by (rewrite length_map; apply zero_prefix_length).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.                          (* [comment removed for export] *)
    do 7 zstep.                                                               (* [comment removed for export] *)
    zstep.                                                                    (* [comment removed for export] *)
    zstep. rewrite ?(Z.mod_small x 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.   (* [comment removed for export] *)
    replace (32 * 2 ^ x) with (2 ^ (x + 5)) by (rewrite Z.pow_add_r by lia; change (2^5) with 32; lia).
    rewrite (FseWalkKit.swrap32_small (2 ^ (x + 5))) by lia.
    zstep. zstep. zstep.                                                      (* [comment removed for export] *)
    zstep. zstep.                                                             (* [comment removed for export] *)
    do 4 zstep.                                                               (* [comment removed for export] *)
    zstep. rewrite (FseWalkKit.swrap32_small (2 ^ (x + 5) + 1)) by lia.                  (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_true.                                      (* [comment removed for export] *)
    replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 18446744071562067968) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (INV0 : rd_invA C mm (r_nc (rd_s0 buf msv1 (a_rt0 C))) (Z_to_bv 64 (a_msv0 C)) (Z_to_bv 64 (x + 5))) end.
    { unfold rd_s0. cbv zeta. cbnR. unfold rd_invA.
      split; [eassumption|]. split; [apply zero_prefix_length|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eexists; unfold FRA_main, ASHB; eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption. }
    pose proof (loop_run_genA' C RNG OK SH RNGS (x + 5) ltac:(lia) POSTF (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) sF m
                  (Z_to_bv 64 (a_msv0 C)) 0xaaed0) as LR.
    unfold rd_lstA in LR.
    eapply LR; try eassumption; try reflexivity.
    all: unfold rd_s0; cbv zeta; cbnR; fold W; rewrite <- ?Ex.
    all: try (f_equal; lia).
    all: try reflexivity.
    rewrite ?Z.shiftr_div_pow2 by lia. f_equal. symmetry. apply FseWalkKit.swrap32_small.
    assert (0 <= W / 2^4 < 2^28) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia.
  Qed.

  (* [comment removed for export] *)
  Definition hd_stA (m1 : amem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
            (Z_to_bv 64 NC) x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
            (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
       (a_F C) (Z_to_bv 64 0xaac6c) (a_fc C) None m1 (seg_rom bsegs).

  (* [comment removed for export] *)
  Lemma hd_chk_splitA : forall (POSTF : machine_state -> Prop) m1 tl0 j0 j24 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
    u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
    rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
    bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells bsegs m1 SPA (FRA_mid C j0 j24) ->
    stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
    (forall (y10 y13 : word), 10 < Z.land (le32 buf 0) 15 -> evtF bsegs RNG POSTF
        (MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
                 y10 (Z_to_bv 64 (2^64 - 44)) (Z_to_bv 64 10) y13 x14 x15 x16 x17
                 (Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
            (a_F C) (Z_to_bv 64 0xab14c) (a_fc C) None m1 (seg_rom bsegs))) ->
    (forall (y12 y13 : word), Z.land (le32 buf 0) 15 <= 10 -> evtF bsegs RNG POSTF
        (MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
                 (Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) y12 y13 x14 x15 x16 x17
                 (Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
            (a_F C) (Z_to_bv 64 0xaacdc) (a_fc C) None m1 (seg_rom bsegs))) ->
    evtF bsegs RNG POSTF (hd_stA m1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof.
    intros POSTF m1 tl0 j0 j24 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI KERR KOK.
    pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
                                 & TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
    pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
    pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
    destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & UT & UB).
    destruct (chkB m1 BUF (BUF + zlen buf) BUF UB ltac:(lia) ltac:(lia)) as (b0 & RDB0 & CK0 & SR0).
    destruct (chkB m1 BUF (BUF + zlen buf) (BUF + 3) UB ltac:(lia) ltac:(lia)) as (b3 & RDB3 & CK3 & SR3).
    destruct (chk1A m1 TLP (TLP + 4) TLP 4 UT ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (bt & RDBT & CKT & SRT).
    destruct (buf_rdA C OK m1 0 HBUF ltac:(lia)) as [RD0 R0].
    destruct (buf_rdA C OK m1 1 HBUF ltac:(lia)) as [RD1 R1].
    destruct (buf_rdA C OK m1 2 HBUF ltac:(lia)) as [RD2 R2].
    destruct (buf_rdA C OK m1 3 HBUF ltac:(lia)) as [RD3 R3].
    rewrite Z.add_0_r in RD0.
    unfold hd_stA.
    (* [comment removed for export] *)
    assert (J2 : forall (y10 y11 y12 y13 : word), y10 = Z_to_bv 64 (Z.land (le32 buf 0) 15) -> y11 = Z_to_bv 64 (le32 buf 0) ->
      Z.land (le32 buf 0) 15 <= 10 ->
      evtF bsegs RNG POSTF
        (MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
                 y10 y11 y12 y13 x14 x15 x16 x17
                 (Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
            (a_F C) (Z_to_bv 64 0xaaccc) (a_fc C) None m1 (seg_rom bsegs))).
    { intros y10 y11 y12 y13 -> -> HX. clear RDB0 CK0 SR0 RDB3 CK3 SR3.
      zstep. zstep. zstep. rewrite sxb_sval.                                  (* [comment removed for export] *)
      zstep. if_cases G; zify_cond G.                                         (* [comment removed for export] *)
      - zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply KOK. exact HX.
      - apply KOK. exact HX. }
    (* [comment removed for export] *)
    assert (J1 : forall (y10 y11 y12 : word),
      evtF bsegs RNG POSTF
        (MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
                 y10 y11 y12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
            (a_F C) (Z_to_bv 64 0xaac90) (a_fc C) None m1 (seg_rom bsegs))).
    { intros y10 y11 y12. clear RDB0 CK0 SR0 RDB3 CK3 SR3.
      zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.   (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
      rewrite le32_lbu_raw by assumption.
      change (Znth 0 buf + 2 ^ 8 * Znth 1 buf + 2 ^ 16 * Znth 2 buf + 2 ^ 24 * Znth 3 buf) with (le32 buf 0).
      pose proof (le32_range buf 0 (buf_all_bytesA C OK)) as RW.
      zstep. zstep. zstep.                                                  (* [comment removed for export] *)
      if_cases K; zify_cond K; rewrite ?(Z.mod_small (le32 buf 0) 18446744073709551616) in * by lia.
      - eapply J2; [reflexivity | reflexivity | lia].
      - zstep. zstep.                                                         (* [comment removed for export] *)
        replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 (2^64 - 44)) by (apply bv_eq; reflexivity).
        eapply KERR. lia. }
    clear J2.
    (* [comment removed for export] *)
    assert (J0 : forall (y10 y11 : word),
      evtF bsegs RNG POSTF
        (MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
                 y10 y11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
            (a_F C) (Z_to_bv 64 0xaac7c) (a_fc C) None m1 (seg_rom bsegs))).
    { intros y10 y11. clear RDB0 CK0 SR0.
      zstep. zstep. zstep. zstep. rewrite sxb_sval.                          (* [comment removed for export] *)
      zstep. if_cases G; zify_cond G.                                         (* [comment removed for export] *)
      - zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply J1.
      - apply J1. }
    clear J1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite sxb_sval.                                    (* [comment removed for export] *)
    zstep. if_cases G; zify_cond G.                                           (* [comment removed for export] *)
    - zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply J0.
    - apply J0.
  Qed.
End HdrGen.

(* [comment removed for export] *)
Lemma read_body8_err_invA : forall buf msv1 nc0 e, 8 <= zlen buf -> all_bytes buf -> 1 <= msv1 <= zlen nc0 ->
  read_ncount_body8 buf msv1 nc0 = Err e ->
  (10 < Z.land (le32 buf 0) 15 /\ e = 44) \/
  (Z.land (le32 buf 0) 15 <= 10 /\ e = 20 /\
   exists sF, rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 nc0) = Ok sF
      /\ (r_remaining sF = 1 -> r_charnum sF <= msv1) /\ (r_remaining sF <> 1 \/ 32 < r_bitCount sF)).
Proof.
  intros buf msv1 nc0 e H8 HB Hm E. unfold read_ncount_body8, assert in E.
  destruct (Z.leb_spec msv1 (FseNCount.Zlength nc0)) as [L|L]; cbv iota in E; cbn [bind] in E. 2:{ unfold FseNCount.Zlength in L. lia. }
  rewrite (readLE32_le32 buf 0) in E by lia. cbn [bind] in E.
  unfold FSE_MIN_TABLELOG, FSE_TABLELOG_ABSOLUTE_MAX in E.
  set (x := Z.land (le32 buf 0) 15) in *.
  destruct (Z.ltb_spec 15 (x + 5)) as [B|B]; cbv iota in E.
  { left. injection E as <-. split; [lia| reflexivity]. }
  right. split; [lia|].
  rewrite shr32_ok in E by lia. cbn [bind] in E.
  assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
  replace ((0 <=? x + 5) && (x + 5 <? 31)) with true in E by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  cbn [bind] in E.
  assert (ES0 : rd_s0 buf msv1 nc0 = FseNCount.mkR (zero_prefix (Z.to_nat msv1) nc0) 0 (le32 buf 0 / 2 ^ 4) 4 0 (2 ^ (x + 5) + 1) (2 ^ (x + 5)) (x + 5 + 1) false)
    by reflexivity.
  rewrite <- ES0 in E.
  destruct (rd_s0_inv buf msv1 nc0 HB H8 Hm ltac:(fold x; lia)) as (HC0 & HP0 & HB0). fold x in HC0.
  destruct (rloop_total buf HB ltac:(unfold FseNCount.Zlength; lia) msv1 nc0 ltac:(unfold FseNCount.Zlength; lia) (x + 5) ltac:(lia)
              (S (Z.to_nat msv1)) (rd_s0 buf msv1 nc0) HC0 HP0 HB0 ltac:(unfold rd_s0; cbn; lia)) as (sF & RL & _ & FIN).
  rewrite RL in E. cbn [bind] in E.
  destruct (Z.eqb_spec (r_remaining sF) 1) as [E1|N1]; cbn [negb] in E; cbv iota in E.
  - destruct (FIN E1) as (CN & _).
    destruct (Z.ltb_spec msv1 (r_charnum sF)) as [B2|B2]; cbv iota in E; [lia|].
    destruct (Z.ltb_spec 32 (r_bitCount sF)) as [B3|B3]; cbv iota in E; [|discriminate E].
    injection E as <-. split; [reflexivity|]. exists sF. split; [exact RL|]. split; [intros _; exact CN| right; exact B3].
  - injection E as <-. split; [reflexivity|]. exists sF. split; [exact RL|]. split; [intros; contradiction| left; exact N1].
Qed.

Section MainGen.
  Variable C : rdctxA.
  Variable RNG : footprint.
  Hypothesis OK : rd_okA C.
  Hypothesis SH : rd_shA C.
  Hypothesis RNGS : rd_rngA C RNG.

  Notation buf := (a_buf C).
  Notation msv1 := (a_msv0 C + 1).
  Notation BUF := (a_BUF C).
  Notation NC := (a_NC C).
  Notation MSVP := (a_MSVP C).
  Notation TLP := (a_TLP C).
  Notation SPA := (a_SPA C).
  Notation FF := (a_FF C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.

  (* [comment removed for export] *)
  Lemma rd_main_genA : forall (POSTF : machine_state -> Prop) (tl0 : word) (j48 : list byte) (RLO RHI : Z)
      (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
    u8arr bsegs (a_m C) NC (u16s (map (Z_to_bv 64) (a_rt0 C))) ->
    rw_cells bsegs (a_m C) MSVP [C4 (Z_to_bv 64 (a_msv0 C))] ->
    rw_cells bsegs (a_m C) TLP [C4 tl0] ->
    bytes_at bsegs (a_m C) BUF (map (Z_to_bv 8) buf) ->
    rw_cells bsegs (a_m C) SPA [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
    stk bsegs (a_m C) (a_lo C) SPA -> mem_inv bsegs (a_m C) ->
    rt_got (a_m C) -> rt_got_ric (a_m C) -> rt_shbase (a_m C) -> rt_inited (a_m C) -> rt_layout (a_m C) -> rt_real_mem (a_m C) ->
    (RLO <= NC /\ NC + 2 * zlen (a_rt0 C) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND) ->
    wr_at bsegs (a_m C) (shad RLO) (shad RHI - shad RLO) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
    (forall m1 j0 j24 (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 : word),
       u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
       rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
       bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells bsegs m1 SPA (FRA_mid C j0 j24) ->
       stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
       evtF bsegs RNG POSTF (hd_stA C m1 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31)) ->
    evtF bsegs RNG POSTF
      (MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
               x10 x11 (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
          (a_F C) (Z_to_bv 64 0xaac48) (a_fc C) None (a_m C) (seg_rom bsegs)).
  Proof.
    intros POSTF tl0 j48 RLO RHI x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31
           ARR HMSV HTL HBUF FRA0 ST MI GOT RIC SHB INI LAY REAL HULL WRH RSH KH.
    pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
                                 & TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
    pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB' & RBS).
    pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
    pose proof (munch_refl (rd_WA C) (a_m C)) as MU. pose proof (wmono_refl bsegs (a_m C)) as WM. unfold rd_WA, RDA_CALLEE in MU.
    pose proof SH as (UN & UM & UT & UB).
    assert (LWS : length (map (Z_to_bv 64) (a_rt0 C)) = length (a_rt0 C)) by apply length_map.
    remember (a_m C) as m eqn:Em.
    zstep. zstep.                                                             (* [comment removed for export] *)
    zstep. rewrite (sx32_small (a_msv0 C)) by lia.                            (* [comment removed for export] *)
    zstep. rewrite ?(FseWalkKit.swrap32_small msv1) by lia.                   (* [comment removed for export] *)
    zstep. zstep. rewrite (shl32_shr31 msv1) by lia.                          (* [comment removed for export] *)
    zstep. zstep. zstep.                                                      (* [comment removed for export] *)
    set (bsA := u16s (map (Z_to_bv 64) (a_rt0 C))) in *.
    assert (LA : length bsA = (2 * length (a_rt0 C))%nat) by (subst bsA; rewrite u16s_length, LWS; reflexivity).
    set (n1 := Z.to_nat (2 * msv1)).
    pose proof (rw_cells_of_u8arr _ _ _ _ ARR) as RA. clear ARR.
    pose proof (rw_cells_split_CB bsegs _ NC [] _ bsA [] [n1; (length bsA - n1)%nat] RA ltac:(cbn [sum_nat]; lia)) as RS.
    cbn [app mk_CB_cells] in RS. clear RA.
    change [CB n1 (firstn n1 bsA); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]
      with ([CB n1 (firstn n1 bsA)] ++ [CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) in RS.
    apply rd_rw_cells_appA in RS. destruct RS as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) buf)) = zlen buf) by (rewrite length_map; reflexivity).
    assert (UN1 : unpoisoned m1 NC (NC + 2 * msv1)).
    { assert (UNx : unpoisoned m1 NC (NC + 2 * zlen (a_rt0 C))) by (apply (inv_shadowA C m1 OK SH); unfold rd_WA, RDA_CALLEE; rewrite <- Em; exact MU).
      eapply unpoisoned_sub; [exact UNx| lia| lia]. }
    pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BN & _ & _ & _ & _ & _ & _ & _ & _ & SNM & SNT & SNB & _).
    destruct HULL as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
    call (amemset_specZ NC (2 * msv1) 0 SPA).
    all: first [ lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => eassumption
         | |- rw_cells _ _ NC _ => exact R1
         | |- rw_cells _ _ _ _ => assumption
         | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact BN| lia| lia]| lia]
         | |- unpoisoned _ _ _ => exact UN1
         | |- wr_at _ _ _ _ => eassumption
         | |- rng _ _ _ => eapply rng_sub'; [exact RSTK| lia]
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- _ => unfold KHIGH, KEND in *; lia
         end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
    (* [comment removed for export] *)
    lazymatch goal with
    | P : rw_cells bsegs ?mm NC [CB (Z.to_nat (2 * msv1)) (repeat (Z_to_bv 8 0) (Z.to_nat (2 * msv1)))] |- _ =>
      rename mm into m2; rename P into P0
    end.
    assert (ARR : u8arr bsegs m2 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C))))).
    { pose proof (proj2 (rd_rw_cells_appA bsegs m2 NC [CB n1 (repeat (Z_to_bv 8 0) n1)]
                          [CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) (conj P0 R2)) as RJ.
      pose proof (rw_cells_merge bsegs m2 NC [] [CB n1 (repeat (Z_to_bv 8 0) n1); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))] [] RJ) as RMg.
      cbn [app] in RMg.
      apply u8arr_of_rw_cells in RMg. cbn [cells_bytes cbytes app] in RMg. rewrite app_nil_r in RMg.
      rewrite firstn_all2 in RMg by (rewrite length_skipn; lia).
      replace n1 with (2 * Z.to_nat msv1)%nat in RMg by (subst n1; lia).
      subst bsA. rewrite u16s_zero_prefix in RMg by lia. exact RMg. }
    clear R2 P0.
    lazymatch goal with
    | FRMx : rw_cells bsegs m2 SPA [CB 8 ?a; C8 _; C8 _; CB 24 ?b; C8 _] |- _ =>
        eapply (KH m2 a b); try eassumption
    | _ => eapply (KH m2); try eassumption
    end.
    all: try (unfold rd_WA, RDA_CALLEE; rewrite <- Em; eassumption).
    all: try (rewrite <- Em; eassumption).
  Qed.

  (* [comment removed for export] *)
  Theorem rd_mainA_err : forall e (tl0 : word) (j48 : list byte) (RLO RHI : Z)
      (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
    u8arr bsegs (a_m C) NC (u16s (map (Z_to_bv 64) (a_rt0 C))) ->
    rw_cells bsegs (a_m C) MSVP [C4 (Z_to_bv 64 (a_msv0 C))] ->
    rw_cells bsegs (a_m C) TLP [C4 tl0] ->
    bytes_at bsegs (a_m C) BUF (map (Z_to_bv 8) buf) ->
    rw_cells bsegs (a_m C) SPA [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
    stk bsegs (a_m C) (a_lo C) SPA -> mem_inv bsegs (a_m C) ->
    rt_got (a_m C) -> rt_got_ric (a_m C) -> rt_shbase (a_m C) -> rt_inited (a_m C) -> rt_layout (a_m C) -> rt_real_mem (a_m C) ->
    (RLO <= NC /\ NC + 2 * zlen (a_rt0 C) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND) ->
    wr_at bsegs (a_m C) (shad RLO) (shad RHI - shad RLO) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
    read_ncount_body8 buf msv1 (a_rt0 C) = Err e ->
    evtF bsegs RNG (rd_finA_post C (2^64 - e))
      (MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
               x10 x11 (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
          (a_F C) (Z_to_bv 64 0xaac48) (a_fc C) None (a_m C) (seg_rom bsegs)).
  Proof.
    intros e tl0 j48 RLO RHI x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31
           ARR HMSV HTL HBUF FRA0 ST MI GOT RIC SHB INI LAY REAL HULL WRH RSH RB.
    pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & _).
    destruct (read_body8_err_invA buf msv1 (a_rt0 C) e (proj1 HH) (buf_all_bytesA C OK) ltac:(lia) RB)
      as [(HX & ->) | (HX & -> & sF & RL & HCN & HBAD)].
    - eapply (rd_main_genA _ tl0 j48 RLO RHI); try eassumption.
      intros m1 j0 j24 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 ARR1 HMSV1 HTL1 HBUF1 FRM1 ST1 MU1 WM1 MI1.
      eapply (hd_chk_splitA C RNG OK SH RNGS _ m1 tl0 j0 j24); try eassumption.
      + intros w10 w13 _. apply evtF_done. unfold rd_finA_post. do 4 eexists. do 22 eexists. split; [reflexivity|].
        unfold rd_finvA. split; [exact ARR1|]. split; [apply zero_prefix_length|]. split; [exact HBUF1|]. split; [exact HMSV1|].
        split; [exact HTL1|]. split; [| split; [exact ST1| split; [exact MU1| split; [exact WM1| exact MI1]]]].
        exists (FRA_mid C j0 j24). split; [exact FRM1| reflexivity].
      + intros y12' y13' HX'. exfalso. lia.
    - eapply (rd_main_genA _ tl0 j48 RLO RHI); try eassumption.
      intros m1 j0 j24 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 ARR1 HMSV1 HTL1 HBUF1 FRM1 ST1 MU1 WM1 MI1.
      eapply (hd_chk_splitA C RNG OK SH RNGS _ m1 tl0 j0 j24); try eassumption.
      + intros w10 w13 HX'. exfalso. lia.
      + intros y12' y13' _.
        eapply (hd_tail_genA C RNG OK SH RNGS _ m1 tl0 sF j0 j24); try eassumption.
        intros m3 z6 z11 z14 z15 z17 z19 z23 z30 INV3 BK.
        pose proof (le32_range buf 0 (buf_all_bytesA C OK)) as RW.
        assert (X0 : 0 <= Z.land (le32 buf 0) 15) by (rewrite land_15; apply Z.mod_pos_bound; lia).
        eapply (@exit_errA C RNG OK (Z.land (le32 buf 0) 15 + 5)); try eassumption; try lia.
  Qed.
End MainGen.
End CANSEC1.
