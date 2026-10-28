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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_base RF_fse_rd_mem RF_fse_rd_count RF_fse_rd_zero RF_fse_rd_loop RF_fse_rd_hdr RF_fse_rd_body RF_fse_rd.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition rd_err_post (C : rdctx) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' rt' msvw tlw,
    ms' = MS (mkR (c_ra C) (Z_to_bv 64 (c_SP C)) (c_gp C) (c_tp C) t0 t1 t2 (c_s0 C) (c_s1 C) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 (c_s2 C) (c_s3 C) (c_s4 C) (c_s5 C) (c_s6 C) (c_s7 C) (c_s8 C) (c_s9 C) (c_s10 C) (c_s11 C) t3 t4 t5 t6)
             (c_F C) (ret_pc (c_ra C)) (c_fc C) None m' (seg_rom usegs)
    /\ munch (rd_W C) (c_m C) m'
    /\ wmono usegs (c_m C) m' /\ mem_inv usegs m'
    /\ stk usegs m' (c_lo C) (c_SP C)
    /\ u8arr usegs m' (c_NC C) (u16s (map (Z_to_bv 64) rt')) /\ length rt' = length (c_rt0 C)
    /\ rw_cells usegs m' (c_MSVP C) [C4 msvw]
    /\ rw_cells usegs m' (c_TLP C) [C4 tlw].

Section Err.
  Variable C : rdctx.
  Hypothesis OK : rd_ok C.

  Notation buf := (c_buf C).
  Notation msv1 := (c_msv0 C + 1).
  Notation BUF := (c_BUF C).
  Notation NC := (c_NC C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.

  (* [comment removed for export] *)
  Lemma epi_err : forall m1 nc msvw tlw r (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rd_inv0 C m1 nc msvw tlw -> x10 = Z_to_bv 64 r ->
    evt usegs (rd_err_post C r)
      (MS (mkR x1 (Z_to_bv 64 (c_SP C + -128)) (c_gp C) (c_tp C) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (c_F C) (Z_to_bv 64 0x2a26c) (c_fc C) None m1 (seg_rom usegs)).
  Proof.
    intros until x31. intros INV ->.
    pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB & _).
    unfold RD_STACK in *.
    destruct INV as (ARR & LNC & HBUF & HMSV & HTL & (junk24 & FR) & ST & MU & WM & MI). unfold rd_W, RD_STACK in MU.
    do 13 zstep. zstep. zstep.
    release_frame FR ST (c_SP C).
    apply evt_done. unfold rd_err_post, rd_W, RD_STACK.
    do 14 eexists. exists m1, nc, msvw, tlw. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact ARR|]. split; [exact LNC|]. split; [exact HMSV| exact HTL].
  Qed.

  (* [comment removed for export] *)
  Lemma exit_err : forall s m1 msvw tlw (x1 x6 x13 x14 x16 x25 x28 x29 : word),
    rd_inv C m1 (r_nc s) msvw tlw -> rd_brk_ok C s ->
    (r_remaining s = 1 -> r_charnum s <= msv1) -> (r_remaining s <> 1 \/ 32 < r_bitCount s) ->
    evt usegs (rd_err_post C (2^64 - 20)) (rd_exit C s m1 x1 x6 x13 x14 x16 x25 x28 x29).
  Proof.
    intros s m1 msvw tlw x1 x6 x13 x14 x16 x25 x28 x29 INV (B1 & B2 & B3 & B4 & B5) HCN HBAD.
    apply rd_inv_inv0 in INV.
    pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & _).
    unfold rd_exit, rd_lst.
    destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - eapply epi_err; [exact INV | apply bv_eq; reflexivity].
    - zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
      zstep. zstep. if_cases K3; zify_cond K3; rewrite ?signed_lit in K3 by lia; [|exfalso; lia].
      eapply epi_err; [exact INV | apply bv_eq; reflexivity].
  Qed.
End Err.

Section LoopGen.
  Variable C : rdctx.
  Hypothesis OK : rd_ok C.
  Variable tl : Z.
  Hypothesis Htl : 5 <= tl <= 15.

  Notation buf := (c_buf C).
  Notation msv1 := (c_msv0 C + 1).
  Notation BUF := (c_BUF C).
  Notation NC := (c_NC C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.

  (* [comment removed for export] *)
  Lemma loop_run_gen : forall (POSTF : machine_state -> Prop) f s sF m1 msvw (x1 x6 x14 x16 x28 : word),
    rloop buf msv1 f s = Ok sF ->
    rd_inv C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    (forall m3 z1 z6 z13 z14 z16 z25 z28 z29, rd_inv C m3 (r_nc sF) msvw (Z_to_bv 64 tl) -> rd_brk_ok C sF ->
       evt usegs POSTF (rd_exit C sF m3 z1 z6 z13 z14 z16 z25 z28 z29)) ->
    evt usegs POSTF (rd_head C s m1 x1 x6 x14 x16 x28).
  Proof.
    intros POSTF. induction f as [|f IH]; intros s sF m1 msvw x1 x6 x14 x16 x28 RL INV HC HP HB32 KX.
    { cbn in RL. discriminate RL. }
    cbn [rloop] in RL.
    assert (CNT : forall s1 m2 (y6 y27 : word),
              rd_inv C m2 (r_nc s1) msvw (Z_to_bv 64 tl) -> CTL msv1 (c_rt0 C) tl s1 -> POS buf s1 -> r_bitCount s1 < 32 ->
              (let! fl := rcount_block buf msv1 s1 in match fl with Brk s' => Ok s' | Cont s' => rloop buf msv1 f s' end) = Ok sF ->
              evt usegs POSTF (rd_cnt C s1 m2 y6 y27)).
    { intros s1 m2 y6 y27 INV1 HC1 HP1 HB1 RL1.
      destruct (rcount_total buf (buf_all_bytes C OK) (buf_h8 C OK) msv1 (c_rt0 C) (msv1_ok C OK) tl Htl s1 HC1 HP1 HB1) as (fl & EF & HF).
      rewrite EF in RL1. cbn [bind] in RL1.
      eapply (count_run C OK tl Htl POSTF s1 m2 msvw (Z_to_bv 64 tl) fl); try eassumption.
      - intros s' m3 z1 z6 z13 z14 z16 z25 z28 z29 -> INV3 BK. injection RL1 as ->.
        eapply KX; assumption.
      - intros s' m3 z1 z6 z14 z16 z28 -> INV3. destruct HF as (HC3 & HP3 & HB3 & _).
        eapply IH; eassumption. }
    unfold rbody in RL.
    destruct (r_previous0 s) eqn:EP.
    - destruct (rzero_total buf (buf_all_bytes C OK) (buf_h8 C OK) msv1 (c_rt0 C) (msv1_ok C OK) tl Htl s HC HP HB32) as (flz & EZ & HZ).
      rewrite EZ in RL. cbn [bind] in RL.
      unfold rd_head. rewrite EP.
      eapply (zero_run C OK POSTF tl s m1 msvw (Z_to_bv 64 tl) flz); try eassumption.
      + intros s' z1 z6 z13 z14 z16 z25 z28 z29 -> EN BK. cbn [bind] in RL. injection RL as ->.
        eapply KX; [rewrite EN; exact INV | exact BK].
      + intros s' z6 z27 -> EN. destruct HZ as (HC1 & HP1 & HB1 & _).
        apply CNT; try assumption. rewrite EN. exact INV.
    - cbn [bind] in RL.
      unfold rd_head. rewrite EP.
      eapply (cnt_entry C tl Htl POSTF s m1); [exact HC | exact HP |].
      intros y6 y27. apply CNT; assumption.
  Qed.
End LoopGen.

Section HdrGen.
  Variable C : rdctx.
  Hypothesis OK : rd_ok C.

  Notation buf := (c_buf C).
  Notation msv1 := (c_msv0 C + 1).
  Notation BUF := (c_BUF C).
  Notation NC := (c_NC C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.

  Corollary loop_run_gen' : forall (POSTF : machine_state -> Prop) tl, 5 <= tl <= 15 ->
    forall f s sF m1 msvw pc (x1 x6 x11 x13 x14 x16 x24 x25 x26 x27 x28 x29 : word),
    rloop buf msv1 f s = Ok sF ->
    rd_inv C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    (forall m3 z1 z6 z13 z14 z16 z25 z28 z29, rd_inv C m3 (r_nc sF) msvw (Z_to_bv 64 tl) -> rd_brk_ok C sF ->
       evt usegs POSTF (rd_exit C sF m3 z1 z6 z13 z14 z16 z25 z28 z29)) ->
    pc = (if r_previous0 s then 0x29e80 else 0x29e64) ->
    x11 = Z_to_bv 64 (r_charnum s) -> x13 = Z_to_bv 64 (bv_swrap 32 (r_bitStream s)) -> x24 = Z_to_bv 64 (r_remaining s) ->
    x25 = Z_to_bv 64 (r_threshold s) -> x26 = Z_to_bv 64 (r_bitCount s) -> x27 = Z_to_bv 64 (BUF + r_ip s) ->
    x29 = Z_to_bv 64 (r_nbBits s) ->
    evt usegs POSTF (rd_lst C pc m1 x1 x6 x11 x13 x14 x16 x24 x25 x26 x27 x28 x29).
  Proof.
    intros POSTF tl Htl f s sF m1 msvw pc x1 x6 x11 x13 x14 x16 x24 x25 x26 x27 x28 x29 RL INV HC HP HB KX -> -> -> -> -> -> -> ->.
    exact (loop_run_gen C OK tl Htl POSTF f s sF m1 msvw x1 x6 x14 x16 x28 RL INV HC HP HB KX).
  Qed.

  (* [comment removed for export] *)
  Lemma rd_header_err : forall m1 tl0 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rd_inv0 C m1 (zero_prefix (Z.to_nat msv1) (c_rt0 C)) (Z_to_bv 64 (c_msv0 C)) tl0 ->
    10 < Z.land (le32 buf 0) 15 ->
    evt usegs (rd_err_post C (2^64 - 44))
      (MS (mkR x1 (Z_to_bv 64 (c_SP C + -128)) (c_gp C) (c_tp C) x5 x6 x7 (Z_to_bv 64 BUF) (Z_to_bv 64 (c_MSVP C))
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 NC) (Z_to_bv 64 (c_TLP C)) (Z_to_bv 64 msv1) (Z_to_bv 64 (BUF + zlen buf))
               x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (c_F C) (Z_to_bv 64 0x29da0) (c_fc C) None m1 (seg_rom usegs)).
  Proof.
    intros m1 tl0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV HX.
    pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB & _).
    destruct (rd_aln C OK) as (HNC0 & HNC2 & HMS0 & HMS4 & HTL0 & HTL4 & HBP).
    unfold RD_STACK in *.
    pose proof INV as INV'.
    destruct INV' as (ARR & LNC & HBUF & HMSV & HTL & (junk24 & FR) & ST & MU & WM & MI). unfold rd_W, RD_STACK in MU.
    destruct (buf_rd C OK m1 0 HBUF ltac:(lia)) as [RD0 R0].
    destruct (buf_rd C OK m1 1 HBUF ltac:(lia)) as [RD1 R1].
    destruct (buf_rd C OK m1 2 HBUF ltac:(lia)) as [RD2 R2].
    destruct (buf_rd C OK m1 3 HBUF ltac:(lia)) as [RD3 R3].
    rewrite Z.add_0_r in RD0.
    zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
    zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite le32_lbu_raw by assumption.
    change (Znth 0 buf + 2 ^ 8 * Znth 1 buf + 2 ^ 16 * Znth 2 buf + 2 ^ 24 * Znth 3 buf) with (le32 buf 0).
    pose proof (le32_range buf 0 (buf_all_bytes C OK)) as RW.
    set (W := le32 buf 0) in *.
    zstep.
    remember (Z.land W 15) as x eqn:Ex.
    assert (X0 : 0 <= x < 16) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
    zstep. zstep.
    if_cases K; zify_cond K; [exfalso; lia|].
    zstep. zstep.
    eapply (epi_err C OK); [exact INV | apply bv_eq; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma rd_header_gen : forall (POSTF : machine_state -> Prop) m1 tl0 sF (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rd_inv0 C m1 (zero_prefix (Z.to_nat msv1) (c_rt0 C)) (Z_to_bv 64 (c_msv0 C)) tl0 ->
    Z.land (le32 buf 0) 15 <= 10 ->
    rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (c_rt0 C)) = Ok sF ->
    (forall m3 z1 z6 z13 z14 z16 z25 z28 z29,
       rd_inv C m3 (r_nc sF) (Z_to_bv 64 (c_msv0 C)) (Z_to_bv 64 (Z.land (le32 buf 0) 15 + 5)) -> rd_brk_ok C sF ->
       evt usegs POSTF (rd_exit C sF m3 z1 z6 z13 z14 z16 z25 z28 z29)) ->
    evt usegs POSTF
      (MS (mkR x1 (Z_to_bv 64 (c_SP C + -128)) (c_gp C) (c_tp C) x5 x6 x7 (Z_to_bv 64 BUF) (Z_to_bv 64 (c_MSVP C))
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 NC) (Z_to_bv 64 (c_TLP C)) (Z_to_bv 64 msv1) (Z_to_bv 64 (BUF + zlen buf))
               x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (c_F C) (Z_to_bv 64 0x29da0) (c_fc C) None m1 (seg_rom usegs)).
  Proof.
    intros POSTF m1 tl0 sF x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV HX RL KX.
    pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB & _).
    destruct (rd_aln C OK) as (HNC0 & HNC2 & HMS0 & HMS4 & HTL0 & HTL4 & HBP).
    unfold RD_STACK in *.
    destruct (rd_s0_inv buf msv1 (c_rt0 C) (buf_all_bytes C OK) (proj1 HH) ltac:(lia) HX) as (HC0 & HP0 & HB0').
    destruct INV as (ARR & LNC & HBUF & HMSV & HTL & (junk24 & FR) & ST & MU & WM & MI). unfold rd_W, RD_STACK in MU.
    destruct (buf_rd C OK m1 0 HBUF ltac:(lia)) as [RD0 R0].
    destruct (buf_rd C OK m1 1 HBUF ltac:(lia)) as [RD1 R1].
    destruct (buf_rd C OK m1 2 HBUF ltac:(lia)) as [RD2 R2].
    destruct (buf_rd C OK m1 3 HBUF ltac:(lia)) as [RD3 R3].
    rewrite Z.add_0_r in RD0.
    zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
    zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite le32_lbu_raw by assumption.
    change (Znth 0 buf + 2 ^ 8 * Znth 1 buf + 2 ^ 16 * Znth 2 buf + 2 ^ 24 * Znth 3 buf) with (le32 buf 0).
    pose proof (le32_range buf 0 (buf_all_bytes C OK)) as RW.
    set (W := le32 buf 0) in *.
    zstep.
    remember (Z.land W 15) as x eqn:Ex.
    assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
    assert (P5 : 32 <= 2 ^ (x + 5) <= 32768).
    { split; [change 32 with (2^5)| change 32768 with (2^15)]; apply Z.pow_le_mono_r; lia. }
    zstep. zstep.
    if_cases K; zify_cond K; [| exfalso; lia].
    zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
    zstep. replace (Z.land (c_TLP C) 3) with 0
      by (change 3 with (2^2 - 1); rewrite land_ones_mod by lia; change (2^2) with 4; symmetry; Z.div_mod_to_equations; lia).
    zstep. if_false.
    do 19 zstep.
    zstep. rewrite ?(Z.mod_small x 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace (32 * 2 ^ x) with (2 ^ (x + 5)) by (rewrite Z.pow_add_r by lia; change (2^5) with 32; lia).
    rewrite (swrap32_small (2 ^ (x + 5))) by lia.
    do 5 zstep. zstep. rewrite (swrap32_small (2 ^ (x + 5) + 1)) by lia.
    zstep. zstep. zstep. zstep. if_false.
    replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 18446744071562067968) by (apply bv_eq; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (INV0 : rd_inv C mm (r_nc (rd_s0 buf msv1 (c_rt0 C))) (Z_to_bv 64 (c_msv0 C)) (Z_to_bv 64 (x + 5)));
      [ unfold rd_s0; cbv zeta; cbnR; unfold rd_inv, rd_W, RD_STACK;
        split; [exact ARR|]; split; [exact LNC|]; split; [exact HBUF|]; split; [exact HMSV|]; split; [exact HTL|];
        split; [do 2 eexists; exact FR|]; split; [exact ST|]; split; [exact MU|]; split; [exact WM| exact MI]
      | pose proof (loop_run_gen' POSTF (x + 5) ltac:(lia) (S (Z.to_nat msv1)) (rd_s0 buf msv1 (c_rt0 C)) sF mm (Z_to_bv 64 (c_msv0 C)) 0x29e64) as LR ]
    end.
    unfold rd_lst in LR.
    eapply LR; try eassumption; try reflexivity.
    all: unfold rd_s0; cbv zeta; cbnR; fold W; rewrite <- ?Ex.
    all: try (f_equal; lia).
    rewrite Z.shiftr_div_pow2 by lia. f_equal. symmetry. apply swrap32_small.
    assert (0 <= W / 2^4 < 2^28) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia.
  Qed.
End HdrGen.

(* [comment removed for export] *)
Lemma read_body8_err_inv : forall buf msv1 nc0 e, 8 <= zlen buf -> all_bytes buf -> 1 <= msv1 <= zlen nc0 ->
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

Section BodyGen.
  Variable C : rdctx.
  Hypothesis OK : rd_ok C.

  Notation buf := (c_buf C).
  Notation msv1 := (c_msv0 C + 1).
  Notation BUF := (c_BUF C).
  Notation NC := (c_NC C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.

  (* [comment removed for export] *)
  Lemma rd_body8_gen : forall (POSTF : machine_state -> Prop) (tl0 : word) (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    u8arr usegs (c_m C) NC (u16s (map (Z_to_bv 64) (c_rt0 C))) ->
    rw_cells usegs (c_m C) (c_MSVP C) [C4 (Z_to_bv 64 (c_msv0 C))] ->
    rw_cells usegs (c_m C) (c_TLP C) [C4 tl0] ->
    bytes_at usegs (c_m C) BUF (map (Z_to_bv 8) buf) ->
    stk usegs (c_m C) (c_lo C) (c_SP C) -> mem_inv usegs (c_m C) ->
    (forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
       rd_inv0 C m1 (zero_prefix (Z.to_nat msv1) (c_rt0 C)) (Z_to_bv 64 (c_msv0 C)) tl0 ->
       evt usegs POSTF
         (MS (mkR x1 (Z_to_bv 64 (c_SP C + -128)) (c_gp C) (c_tp C) x5 x6 x7 (Z_to_bv 64 BUF) (Z_to_bv 64 (c_MSVP C))
                  x10 x11 x12 x13 x14 x15 x16 x17
                  (Z_to_bv 64 NC) (Z_to_bv 64 (c_TLP C)) (Z_to_bv 64 msv1) (Z_to_bv 64 (BUF + zlen buf))
                  x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (c_F C) (Z_to_bv 64 0x29da0) (c_fc C) None m1 (seg_rom usegs))) ->
    evt usegs POSTF
      (MS (mkR (c_ra C) (Z_to_bv 64 (c_SP C)) (c_gp C) (c_tp C) t0 t1 t2 (c_s0 C) (c_s1 C)
               (Z_to_bv 64 NC) (Z_to_bv 64 (c_MSVP C)) (Z_to_bv 64 (c_TLP C)) (Z_to_bv 64 BUF) (Z_to_bv 64 (zlen buf)) a5 a6 a7
               (c_s2 C) (c_s3 C) (c_s4 C) (c_s5 C) (c_s6 C) (c_s7 C) (c_s8 C) (c_s9 C) (c_s10 C) (c_s11 C) t3 t4 t5 t6)
          (c_F C) (Z_to_bv 64 0x29cc4) (c_fc C) None (c_m C) (seg_rom usegs)).
  Proof.
    intros POSTF tl0 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ARR HMSV HTL HBUF ST MI KH.
    pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB & _).
    destruct (rd_aln C OK) as (HNC0 & HNC2 & HMS0 & HMS4 & HTL0 & HTL4 & HBP).
    unfold RD_STACK in *.
    pose proof (munch_refl (rd_W C) (c_m C)) as MU. pose proof (wmono_refl usegs (c_m C)) as WM. unfold rd_W, RD_STACK in MU.
    assert (LWS : length (map (Z_to_bv 64) (c_rt0 C)) = length (c_rt0 C)) by apply length_map.
    assert (LBS : zlen (map (Z_to_bv 8) buf) = zlen buf) by (rewrite length_map; reflexivity).
    remember (c_m C) as m eqn:Em.
    carve_frame 128%nat ST.
    do 14 zstep.
    zstep. zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
    zstep. zstep. zstep.
    zstep. replace (0 <? BUF) with true by (symmetry; apply Z.ltb_lt; lia).
    zstep. replace (BUF + zlen buf <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    zstep. zstep. if_false.
    zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
    zstep. replace (Z.land (c_MSVP C) 3) with 0
      by (change 3 with (2^2 - 1); rewrite land_ones_mod by lia; change (2^2) with 4; symmetry; Z.div_mod_to_equations; lia).
    zstep. if_false.
    zstep. zstep.
    zstep. if_cases K; zify_cond K; [| exfalso; lia].
    zstep. rewrite (sx32_small (c_msv0 C)) by lia.
    zstep. rewrite (swrap32_small msv1) by lia.
    zstep. zstep. rewrite (shl32_shr31 msv1) by lia.
    zstep. zstep. zstep.
    set (bsA := u16s (map (Z_to_bv 64) (c_rt0 C))) in *.
    assert (LA : length bsA = (2 * length (c_rt0 C))%nat) by (subst bsA; rewrite u16s_length, LWS; reflexivity).
    set (n1 := Z.to_nat (2 * msv1)).
    pose proof (rw_cells_of_u8arr _ _ _ _ ARR) as RA. clear ARR.
    pose proof (rw_cells_split_CB usegs _ NC [] _ bsA [] [n1; (length bsA - n1)%nat] RA ltac:(cbn [sum_nat]; lia)) as RS.
    cbn [app mk_CB_cells] in RS. clear RA.
    change [CB n1 (firstn n1 bsA); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]
      with ([CB n1 (firstn n1 bsA)] ++ [CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) in RS.
    apply rd_rw_cells_app in RS. destruct RS as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
    call (rd_memset_specZ NC (2 * msv1) 0); [exact R1 | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
    assert (ARR : u8arr usegs x13 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (c_rt0 C))))).
    { pose proof (proj2 (rd_rw_cells_app usegs x13 NC [CB n1 (repeat (Z_to_bv 8 0) n1)]
                          [CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) (conj POST R2)) as RJ.
      pose proof (rw_cells_merge usegs x13 NC [] [CB n1 (repeat (Z_to_bv 8 0) n1); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))] [] RJ) as RM. cbn [app] in RM.
      apply u8arr_of_rw_cells in RM. cbn [cells_bytes cbytes app] in RM. rewrite app_nil_r in RM.
      rewrite firstn_all2 in RM by (rewrite length_skipn; lia).
      replace n1 with (2 * Z.to_nat msv1)%nat in RM by (subst n1; lia).
      subst bsA. rewrite u16s_zero_prefix in RM by lia. exact RM. }
    clear POST R2.
    eapply (KH x13).
    unfold rd_inv0, rd_W, RD_STACK. rewrite <- Em.
    split; [exact ARR|]. split; [apply zero_prefix_length|]. split; [exact HBUF|]. split; [exact HMSV|]. split; [exact HTL|].
    split; [eexists; exact FR|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM| exact MI0].
  Qed.

  (* [comment removed for export] *)
  Theorem rd_body8_err : forall e (tl0 : word) (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    u8arr usegs (c_m C) NC (u16s (map (Z_to_bv 64) (c_rt0 C))) ->
    rw_cells usegs (c_m C) (c_MSVP C) [C4 (Z_to_bv 64 (c_msv0 C))] ->
    rw_cells usegs (c_m C) (c_TLP C) [C4 tl0] ->
    bytes_at usegs (c_m C) BUF (map (Z_to_bv 8) buf) ->
    stk usegs (c_m C) (c_lo C) (c_SP C) -> mem_inv usegs (c_m C) ->
    read_ncount_body8 buf msv1 (c_rt0 C) = Err e ->
    evt usegs (rd_err_post C (2^64 - e))
      (MS (mkR (c_ra C) (Z_to_bv 64 (c_SP C)) (c_gp C) (c_tp C) t0 t1 t2 (c_s0 C) (c_s1 C)
               (Z_to_bv 64 NC) (Z_to_bv 64 (c_MSVP C)) (Z_to_bv 64 (c_TLP C)) (Z_to_bv 64 BUF) (Z_to_bv 64 (zlen buf)) a5 a6 a7
               (c_s2 C) (c_s3 C) (c_s4 C) (c_s5 C) (c_s6 C) (c_s7 C) (c_s8 C) (c_s9 C) (c_s10 C) (c_s11 C) t3 t4 t5 t6)
          (c_F C) (Z_to_bv 64 0x29cc4) (c_fc C) None (c_m C) (seg_rom usegs)).
  Proof.
    intros e tl0 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ARR HMSV HTL HBUF ST MI RB.
    pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & _).
    destruct (read_body8_err_inv buf msv1 (c_rt0 C) e (proj1 HH) (buf_all_bytes C OK) ltac:(lia) RB) as [(HX & ->) | (HX & -> & sF & RL & HCN & HBAD)].
    - eapply (rd_body8_gen _ tl0); try eassumption.
      intros. eapply (rd_header_err C OK); eassumption.
    - eapply (rd_body8_gen _ tl0); try eassumption.
      intros m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV.
      eapply (rd_header_gen C OK _ m1 tl0 sF); [exact INV | exact HX | exact RL |].
      intros m3 z1 z6 z13 z14 z16 z25 z28 z29 INV3 BK.
      eapply (exit_err C OK); eassumption.
  Qed.
End BodyGen.

(* [comment removed for export] *)
Definition fse_read_err_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV NC MSVP TLP : Z) (rt0 : list Z) (lo : Z) (m : fmem) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' rt' msvw tlw,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - FSE_READ_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ u8arr usegs m' NC (u16s (map (Z_to_bv 64) rt')) /\ length rt' = length rt0
    /\ rw_cells usegs m' MSVP [C4 msvw]
    /\ rw_cells usegs m' TLP [C4 tlw].

Section TopAny.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem).
  Variables (SPV NC MSVP TLP BUF : Z) (rt0 buf : list Z) (msv0 lo : Z) (tl0 : word).
  Hypothesis ARR : u8arr usegs m NC (u16s (map (Z_to_bv 64) rt0)).
  Hypothesis HMSV : rw_cells usegs m MSVP [C4 (Z_to_bv 64 msv0)].
  Hypothesis HTL : rw_cells usegs m TLP [C4 tl0].
  Hypothesis HBUF : bytes_at usegs m BUF (map (Z_to_bv 8) buf).
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) buf.
  Hypothesis HM0 : 0 <= msv0 <= 255.
  Hypothesis HM1 : msv0 + 1 <= zlen rt0.
  Hypothesis HLEN : zlen buf <= 1048576.
  Hypothesis HNC0 : 0 < NC.
  Hypothesis HNC2 : NC mod 2 = 0.
  Hypothesis HMP0 : 0 < MSVP.
  Hypothesis HMP4 : MSVP mod 4 = 0.
  Hypothesis HTP0 : 0 < TLP.
  Hypothesis HTP4 : TLP mod 4 = 0.
  Hypothesis HBP : 0 < BUF.
  Hypothesis HSLACK : BUF + zlen buf + 8 <= 2^64.
  Hypothesis ST : stk usegs m lo SPV.
  Hypothesis LO : lo <= SPV - FSE_READ_STACK.
  Hypothesis RSP : 0 <= SPV < 2^64.
  Hypothesis SNS : NC + 2 * zlen rt0 <= lo \/ SPV <= NC.
  Hypothesis SMS : MSVP + 4 <= lo \/ SPV <= MSVP.
  Hypothesis STS : TLP + 4 <= lo \/ SPV <= TLP.
  Hypothesis SBS : BUF + zlen buf <= lo \/ SPV <= BUF.
  Hypothesis SNM : NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC.
  Hypothesis SNT : NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC.
  Hypothesis SNB : NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC.
  Hypothesis SMT : MSVP + 4 <= TLP \/ TLP + 4 <= MSVP.
  Hypothesis SMB : MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP.
  Hypothesis STB : TLP + 4 <= BUF \/ BUF + zlen buf <= TLP.
  Hypothesis MI : mem_inv usegs m.

  Notation EPOST r := (fse_read_err_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 lo m r).

  Lemma bounds_any : 0 <= lo /\ (0 <= NC /\ NC + 2 * zlen rt0 <= 2^64) /\ (0 <= MSVP /\ MSVP + 4 <= 2^64) /\ (0 <= TLP /\ TLP + 4 <= 2^64).
  Proof.
    destruct ST as (L0 & _). pose proof (u8arr_bound _ _ _ _ ARR) as B1. rewrite u16s_length, length_map in B1.
    pose proof (rw_cells_bound _ _ _ _ HMSV) as B2. pose proof (rw_cells_bound _ _ _ _ HTL) as B3.
    cbn [cells_size csize Nat.add] in B2, B3. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_top8_ok : forall rt msv tl n (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word), 8 <= zlen buf ->
    read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n) ->
    evt usegs (fse_read_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 rt msv tl n lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
               (Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x29cc4) fc None m (seg_rom usegs)).
  Proof.
    intros rt msv tl n t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 H8 RN.
    destruct bounds_any as (L0 & BN & BM & BT).
    pose proof RN as RN'. unfold read_ncount in RN'. unfold FseNCount.Zlength in RN'.
    replace (zlen buf <? 8) with false in RN' by (symmetry; apply Z.ltb_ge; lia).
    set (C := mkRD ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF lo rt0 buf msv0).
    assert (OK : rd_ok C).
    { unfold rd_ok, RD_STACK, FSE_READ_STACK in *. cbn. repeat split; try assumption; try lia. }
    eapply evt_mono.
    - exact (rd_body8 C OK rt msv tl n tl0 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ARR HMSV HTL HBUF ST MI RN').
    - intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & ST' & A' & M' & T').
      unfold fse_read_post. do 14 eexists. exists m'. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, rd_W, RD_STACK, FSE_READ_STACK. subst C. cbn [outside c_NC c_rt0 c_MSVP c_TLP c_SP]. intros x; lia. }
      split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact A'|]. split; [exact M'| exact T'].
  Qed.

  (* [comment removed for export] *)
  Lemma rd_top8_err : forall e (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word), 8 <= zlen buf ->
    read_ncount rt0 msv0 buf = Err e ->
    evt usegs (EPOST (2^64 - e))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
               (Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x29cc4) fc None m (seg_rom usegs)).
  Proof.
    intros e t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 H8 RN.
    destruct bounds_any as (L0 & BN & BM & BT).
    pose proof RN as RN'. unfold read_ncount in RN'. unfold FseNCount.Zlength in RN'.
    replace (zlen buf <? 8) with false in RN' by (symmetry; apply Z.ltb_ge; lia).
    set (C := mkRD ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF lo rt0 buf msv0).
    assert (OK : rd_ok C).
    { unfold rd_ok, RD_STACK, FSE_READ_STACK in *. cbn. repeat split; try assumption; try lia. }
    eapply evt_mono.
    - exact (rd_body8_err C OK e tl0 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ARR HMSV HTL HBUF ST MI RN').
    - intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & rt' & msvw & tlw & -> & MU & WM & MI' & ST' & A' & LA' & M' & T').
      unfold fse_read_err_post. do 14 eexists. exists m', rt', msvw, tlw. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, rd_W, RD_STACK, FSE_READ_STACK. subst C. cbn [outside c_NC c_rt0 c_MSVP c_TLP c_SP]. intros x; lia. }
      split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact A'|]. split; [exact LA'|]. split; [exact M'| exact T'].
  Qed.

  Lemma pad_tail_any : forall (z : byte) k, (k <= 8)%nat -> firstn (8 - k) (skipn k (repeat z 8)) = repeat z (8 - k).
  Proof. intros z k Hk. do 9 (destruct k as [|k]; [reflexivity|]). lia. Qed.

  (* [comment removed for export] *)
  Lemma rd_top_small_err : forall e (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word), zlen buf < 8 ->
    read_ncount rt0 msv0 buf = Err e ->
    evt usegs (EPOST (2^64 - e))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
               (Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x29cc4) fc None m (seg_rom usegs)).
  Proof.
    intros e t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 H8 RN.
    destruct bounds_any as (L0 & BN & BM & BT). unfold FSE_READ_STACK in *.
    set (hb := zlen buf) in *. set (hbn := Z.to_nat hb).
    set (buf' := buf ++ repeat 0 (Z.to_nat (8 - hb))).
    assert (LB' : zlen buf' = 8) by (subst buf' hb; rewrite length_app, repeat_length; lia).
    assert (HL : msv0 + 1 <= zlen rt0) by exact HM1.
    pose proof (munch_refl [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - 256, SPV)] m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    assert (LWS : length (map (Z_to_bv 64) rt0) = length rt0) by apply length_map.
    assert (LBS : zlen (map (Z_to_bv 8) buf) = hb) by (rewrite length_map; reflexivity).
    carve_frame 128%nat ST.
    do 14 zstep.
    zstep. zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
    zstep. zstep. zstep.
    zstep. replace (0 <? BUF) with true by (symmetry; apply Z.ltb_lt; lia).
    zstep. replace (BUF + hb <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    zstep. zstep. if_false.
    zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
    zstep. replace (Z.land MSVP 3) with 0
      by (change 3 with (2^2 - 1); rewrite land_ones_mod by lia; change (2^2) with 4; symmetry; Z.div_mod_to_equations; lia).
    zstep. if_false.
    zstep. zstep.
    zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch type of FR with rw_cells _ _ _ (CB 16 ?j :: ?rest) =>
      change (CB 16 j :: rest) with ([CB 16 j] ++ rest) in FR end.
    apply rd_rw_cells_app in FR. destruct FR as [J16 FR]. cbn [cells_size csize Nat.add] in FR.
    replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) in FR by lia.
    (* [comment removed for export] *)
    pose proof (rw_cells_merge usegs _ (SPV + -112) [] [C8 (Z_to_bv 64 0)]
                  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as FM.
    cbn [app cells_size cells_bytes csize cbytes Nat.add] in FM. clear FR.
    change (le8 (Z_to_bv 64 0) ++ []) with (repeat (Z_to_bv 8 0) 8) in FM.
    pose proof (rw_cells_split_CB usegs _ (SPV + -112) [] 8 (repeat (Z_to_bv 8 0) 8)
                  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                  [hbn; (8 - hbn)%nat] FM ltac:(cbn [sum_nat]; lia)) as FS.
    cbn [app mk_CB_cells] in FS. clear FM. rewrite (pad_tail_any (Z_to_bv 8 0) hbn) in FS by lia.
    change (CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8)) :: CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn)) ::
            [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      with ([CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8))] ++ ([CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] ++
            [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FS.
    apply rd_rw_cells_app in FS. destruct FS as [R1 FS]. apply rd_rw_cells_app in FS. destruct FS as [R2 R3].
    cbn [cells_size csize Nat.add] in R2, R3.
    replace (SPV + -112 + Z.of_nat (hbn + 0)) with (SPV + -112 + hb) in R2, R3 by lia.
    replace (SPV + -112 + hb + Z.of_nat (8 - hbn + 0)) with (SPV + -104) in R3 by lia.
    call (rd_memcpy_specZ (SPV + -112) BUF hb); [exact HBUF | rewrite length_map; unfold hb; lia | exact R1 | lia | eassumption
          | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
    (* [comment removed for export] *)
    assert (FB' : Forall (fun c => 0 <= c < 256) buf').
    { subst buf'. apply Forall_app. split; [exact FBY|]. apply Forall_forall. intros c Hc. apply repeat_spec in Hc. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RB8 : rw_cells usegs mm (SPV + -112) [CB 8 (map (Z_to_bv 8) buf')]) end.
    { replace (SPV + -112 + hb) with (SPV + -112 + Z.of_nat (cells_size [CB hbn (map (Z_to_bv 8) buf)])) in R2
        by (cbn [cells_size csize Nat.add]; lia).
      lazymatch goal with P : rw_cells usegs ?mm (SPV + -112) [CB (Z.to_nat hb) (map (Z_to_bv 8) buf)] |- _ =>
        pose proof (proj2 (rd_rw_cells_app usegs mm (SPV + -112) [CB hbn (map (Z_to_bv 8) buf)]
                            [CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))]) (conj P R2)) as RJ;
        pose proof (rw_cells_merge usegs mm (SPV + -112) [] [CB hbn (map (Z_to_bv 8) buf); CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] [] RJ) as RM
      end.
      cbn [app cells_size cells_bytes csize cbytes Nat.add] in RM. rewrite app_nil_r in RM.
      replace (hbn + (8 - hbn + 0))%nat with 8%nat in RM by lia.
      subst buf'. rewrite map_app, map_repeat. replace (Z.to_nat (8 - hb)) with (8 - hbn)%nat by lia. exact RM. }
    clear R2.
    do 7 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      set (C' := mkRD (Z_to_bv 64 171372) gp tp (Z_to_bv 64 hb) (Z_to_bv 64 MSVP) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) s4
                      (Z_to_bv 64 (BUF + hb)) s6 s7 s8 s9 s10 s11 F fc mm (SPV + -128) NC MSVP TLP (SPV + -112) lo rt0 buf' msv0) end.
    assert (OK' : rd_ok C').
    { unfold rd_ok, RD_STACK. subst C'. cbn [c_buf c_msv0 c_rt0 c_SP c_lo c_NC c_BUF c_MSVP c_TLP]. rewrite LB'.
      repeat split; try assumption; try lia. }
    assert (HBUF' : bytes_at usegs (c_m C') (c_BUF C') (map (Z_to_bv 8) (c_buf C'))).
    { subst C'. cbn [c_m c_BUF c_buf]. destruct RB8 as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. exact BA. }
    replace (Z_to_bv 64 8) with (Z_to_bv 64 (zlen (c_buf C'))) by (subst C'; cbn [c_buf]; rewrite LB'; reflexivity).
    assert (CASES : (read_ncount_body8 buf' (msv0 + 1) rt0 = Err e /\ (e = 44 \/ e = 20))
                    \/ (e = 20 /\ exists rt msv tl n, read_ncount_body8 buf' (msv0 + 1) rt0 = Ok (rt, msv, tl, n) /\ hb < n /\ 1 <= n <= 8)).
    { pose proof RN as RN'. unfold read_ncount in RN'. unfold FseNCount.Zlength in RN'. fold hb in RN'.
      replace (hb <? 8) with true in RN' by (symmetry; apply Z.ltb_lt; lia). fold buf' in RN'.
      destruct (read_ncount_body8_total buf' (msv0 + 1) rt0 (Forall_all_bytes _ FB') ltac:(unfold FseNCount.Zlength; lia)
                  ltac:(unfold FseNCount.Zlength; lia)) as [(nc2 & msv2 & tl2 & n2 & E2 & _ & _ & _ & _ & N2 & _) | (e2 & E2)].
      - right. rewrite E2 in RN'. cbn [bind] in RN'. destruct (Z.ltb_spec hb n2); [|discriminate RN']. injection RN' as <-.
        split; [reflexivity|]. exists nc2, msv2, tl2, n2. split; [exact E2|]. unfold FseNCount.Zlength in N2. split; [lia|lia].
      - left. rewrite E2 in RN'. cbn [bind] in RN'. injection RN' as <-. split; [exact E2|].
        destruct (read_body8_err_inv buf' (msv0 + 1) rt0 e2 ltac:(lia) (Forall_all_bytes _ FB') ltac:(lia) E2) as [(_ & ->) | (_ & -> & _)]; auto. }
    destruct CASES as [(EB & EV) | (-> & rt & msv & tl & n & EB & HN & NR)].
    - (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (rd_body8_err C' OK' e tl0); subst C'; cbn [c_m c_NC c_rt0 c_MSVP c_msv0 c_TLP c_BUF c_buf c_lo c_SP];
          try eassumption. }
      intros ms' PO. hnf in PO. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST' & ARR' & LARR' & HMSV' & HTL').
    unfold rd_W, RD_STACK in MU'. subst C'.
    cbn [c_ra c_gp c_tp c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m c_SP c_NC c_MSVP c_TLP c_BUF c_lo c_rt0 c_buf c_msv0] in *.
    clear ARR HMSV HTL HBUF'.
    lazymatch type of MU' with munch _ ?ma ?mb => transport_after_call usegs ma mb MU' WM'; clear MU' WM'; try clear ma end.
    replace (ret_pc (Z_to_bv 64 171372)) with (Z_to_bv 64 171372) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct EV as [-> | ->].
      + zstep. zstep. zstep. zstep. if_true.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of J16 with rw_cells _ _ _ [CB 16 ?j] =>
      assert (FR : rw_cells usegs mm (SPV + -128)
                     [CB 16 j; CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      end
    end.
    { match goal with |- rw_cells _ _ _ (?c :: ?rest) => change (c :: rest) with ([c] ++ rest) end.
      apply rd_rw_cells_app. split; [exact J16|]. cbn [cells_size csize Nat.add].
      replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) by lia.
      change [CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        with ([CB 8 (map (Z_to_bv 8) buf')] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      apply rd_rw_cells_app. split; [exact RB8|]. cbn [cells_size csize Nat.add].
      replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia. exact R3. }
    clear RB8 R3 J16.
    do 13 zstep. zstep. zstep.
    release_frame FR ST' SPV.
    apply evt_done. unfold fse_read_err_post, FSE_READ_STACK.
    do 14 eexists. eexists. eexists. eexists. eexists. split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption.
      + zstep. zstep. zstep. zstep. if_true.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of J16 with rw_cells _ _ _ [CB 16 ?j] =>
      assert (FR : rw_cells usegs mm (SPV + -128)
                     [CB 16 j; CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      end
    end.
    { match goal with |- rw_cells _ _ _ (?c :: ?rest) => change (c :: rest) with ([c] ++ rest) end.
      apply rd_rw_cells_app. split; [exact J16|]. cbn [cells_size csize Nat.add].
      replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) by lia.
      change [CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        with ([CB 8 (map (Z_to_bv 8) buf')] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      apply rd_rw_cells_app. split; [exact RB8|]. cbn [cells_size csize Nat.add].
      replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia. exact R3. }
    clear RB8 R3 J16.
    do 13 zstep. zstep. zstep.
    release_frame FR ST' SPV.
    apply evt_done. unfold fse_read_err_post, FSE_READ_STACK.
    do 14 eexists. eexists. eexists. eexists. eexists. split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption.
    - (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (rd_body8 C' OK' rt msv tl n tl0); subst C'; cbn [c_m c_NC c_rt0 c_MSVP c_msv0 c_TLP c_BUF c_buf c_lo c_SP];
          try eassumption. }
      intros ms' PO. hnf in PO. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST' & ARR' & HMSV' & HTL').
    unfold rd_W, RD_STACK in MU'. subst C'.
    cbn [c_ra c_gp c_tp c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m c_SP c_NC c_MSVP c_TLP c_BUF c_lo c_rt0 c_buf c_msv0] in *.
    clear ARR HMSV HTL HBUF'.
    lazymatch type of MU' with munch _ ?ma ?mb => transport_after_call usegs ma mb MU' WM'; clear MU' WM'; try clear ma end.
    replace (ret_pc (Z_to_bv 64 171372)) with (Z_to_bv 64 171372) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep. zstep. replace (hb <? n) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      zstep.
      zstep. replace (n <? 18446744073709551497) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. if_false.
      zstep. zstep.
      replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv_eq; reflexivity).
      assert (LARR' : length rt = length rt0).
      { destruct (read_ncount_body8_total buf' (msv0 + 1) rt0 (Forall_all_bytes _ FB') ltac:(unfold FseNCount.Zlength; lia)
                    ltac:(unfold FseNCount.Zlength; lia)) as [(nc2 & msv2 & tl2 & n2 & E2 & L2 & _) | (e2 & E2)];
          rewrite EB in E2; [injection E2 as <- <- <- <-; exact L2 | discriminate E2]. }
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of J16 with rw_cells _ _ _ [CB 16 ?j] =>
      assert (FR : rw_cells usegs mm (SPV + -128)
                     [CB 16 j; CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      end
    end.
    { match goal with |- rw_cells _ _ _ (?c :: ?rest) => change (c :: rest) with ([c] ++ rest) end.
      apply rd_rw_cells_app. split; [exact J16|]. cbn [cells_size csize Nat.add].
      replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) by lia.
      change [CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        with ([CB 8 (map (Z_to_bv 8) buf')] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      apply rd_rw_cells_app. split; [exact RB8|]. cbn [cells_size csize Nat.add].
      replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia. exact R3. }
    clear RB8 R3 J16.
    do 13 zstep. zstep. zstep.
    release_frame FR ST' SPV.
    apply evt_done. unfold fse_read_err_post, FSE_READ_STACK.
    do 14 eexists. eexists. eexists. eexists. eexists. split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption.
  Qed.
End TopAny.

(* [comment removed for export] *)
Definition fse_read_any_stmt_at (ENTRY : Z) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV NC MSVP TLP BUF : Z)
         (rt0 buf : list Z) (msv0 lo : Z) (tl0 : word),
  u8arr usegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
  rw_cells usegs m MSVP [C4 (Z_to_bv 64 msv0)] ->
  rw_cells usegs m TLP [C4 tl0] ->
  bytes_at usegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
  0 <= msv0 <= 255 -> msv0 + 1 <= zlen rt0 -> zlen buf <= 1048576 ->
  0 < NC -> NC mod 2 = 0 -> 0 < MSVP -> MSVP mod 4 = 0 -> 0 < TLP -> TLP mod 4 = 0 ->
  0 < BUF -> BUF + zlen buf + 8 <= 2^64 ->
  stk usegs m lo SPV -> lo <= SPV - FSE_READ_STACK -> 0 <= SPV < 2^64 ->
  (NC + 2 * zlen rt0 <= lo \/ SPV <= NC) -> (MSVP + 4 <= lo \/ SPV <= MSVP) ->
  (TLP + 4 <= lo \/ SPV <= TLP) -> (BUF + zlen buf <= lo \/ SPV <= BUF) ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
  (NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) ->
  (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  (MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 NC -> a1 = Z_to_bv 64 MSVP -> a2 = Z_to_bv 64 TLP -> a3 = Z_to_bv 64 BUF -> a4 = Z_to_bv 64 (zlen buf) ->
  evt usegs
    (fun ms' =>
       (exists rt msv tl n, read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n) /\
          fse_read_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 rt msv tl n lo m ms')
       \/ (exists e, read_ncount rt0 msv0 buf = Err e /\
             fse_read_err_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 lo m (2^64 - e) ms'))
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition fse_read_body_any_stmt : Prop := fse_read_any_stmt_at PFSE_READ_BODY.
Definition fse_read_any_stmt : Prop := fse_read_any_stmt_at PFSE_READ.

Theorem fse_read_body_any_proof : fse_read_body_any_stmt.
Proof.
  unfold fse_read_body_any_stmt, fse_read_any_stmt_at.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV NC MSVP TLP BUF
         rt0 buf msv0 lo tl0
         ARR HMSV HTL HBUF FBY HM0 HM1 HLEN HNC0 HNC2 HMP0 HMP4 HTP0 HTP4 HBP HSLACK ST LO RSP SNS SMS STS SBS SNM SNT SNB SMT SMB STB MI -> -> -> -> ->.
  unfold PFSE_READ_BODY.
  destruct (read_ncount_total rt0 msv0 buf (Forall_all_bytes _ FBY) ltac:(lia) ltac:(unfold FseNCount.Zlength; lia))
    as [(rt & msv & tl & n & RN & _) | (e & RN)].
  - eapply evt_mono; [| intros ms' P; left; exists rt, msv, tl, n; split; [exact RN | exact P]].
    destruct (Z_lt_le_dec (zlen buf) 8) as [LT|GE].
    + assert (HLEN' : zlen buf <= 65536) by lia.
      eapply (rd_top_small ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF rt0 rt buf msv0 msv tl n lo tl0); eassumption.
    + eapply (rd_top8_ok ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF rt0 buf msv0 lo tl0); eassumption.
  - eapply evt_mono; [| intros ms' P; right; exists e; split; [exact RN | exact P]].
    destruct (Z_lt_le_dec (zlen buf) 8) as [LT|GE].
    + eapply (rd_top_small_err ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF rt0 buf msv0 lo tl0); eassumption.
    + eapply (rd_top8_err ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF rt0 buf msv0 lo tl0); eassumption.
Qed.

Theorem fse_read_any_proof : fse_read_any_stmt.
Proof.
  unfold fse_read_any_stmt, fse_read_any_stmt_at.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV NC MSVP TLP BUF
         rt0 buf msv0 lo tl0
         ARR HMSV HTL HBUF FBY HM0 HM1 HLEN HNC0 HNC2 HMP0 HMP4 HTP0 HTP4 HBP HSLACK ST LO RSP SNS SMS STS SBS SNM SNT SNB SMT SMB STB MI -> -> -> -> ->.
  unfold PFSE_READ.
  zstep. zstep.
  eapply (fse_read_body_any_proof ra gp tp t0 t1 t2 s0 s1 _ _ _ _ _ (Z_to_bv 64 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m SPV NC MSVP TLP BUF rt0 buf msv0 lo tl0); try eassumption; reflexivity.
Qed.
