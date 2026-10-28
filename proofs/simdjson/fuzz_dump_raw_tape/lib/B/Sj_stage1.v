(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps
  Sj_stage1_iface Sj_stage1_defs Sj_stage1_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition env_at (E : s1env) (F : bvmap 5 word) (fc : bv 32) (m : mem) : s1env :=
  mkS1Env (e_ra E) (e_sp E) (e_gp E) (e_tp E) (e_s0 E) (e_s1 E) (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E)
          (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) F fc (e_lo E) (e_THIS E) (e_BUF E) (e_IDX E) (e_bs E) (e_cap E)
          (e_vptr E) (e_p12 E) (e_mid E) (e_docj E) m.

Lemma env_at_ok : forall E F fc m, env_ok_b E -> env_ok_b (env_at E F fc m).
Proof. intros E F fc m [[H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11] B1 B2 B3]. constructor; [constructor|..]; assumption. Qed.

Section Stage1CPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MCP : memcpy_icontract_f RT e_asan_memcpy.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, A1_GTOP, A1_STACK, B1_GTOP, B1_STACK, S1_LEN_MAX in *; lia.

Lemma a1_art_step : forall Σ (E : s1env) (m m' : mem), a1_live RT Σ E -> ART RT Σ m ->
  rt_sp0 RT Σ - STACK_WIN <= bv_unsigned (e_sp E) - 448 -> bv_unsigned (e_sp E) <= USTACK_TOP ->
  munch (b1_W E) m m' -> wmono bsegs m m' -> ART RT Σ m'.
Proof using AF.
  intros Σ E m m' (INT & INI & INB & _) HA SPLO SPHI MU WM.
  apply (art_client_write RT AF Σ m m' (bv_unsigned (e_sp E) - 448) HA SPLO); [| exact WM].
  intros a Ha. apply MU. unfold s1_W_g. cbn [outside].
  split; [intros Hin; apply Ha; left; lia|].
  split; [intros Hin; apply Ha; right; right; left; exists (e_THIS E), 96; split; [exact INT| lia]|].
  split; [intros Hin; apply Ha; right; right; left; exists (e_IDX E), (4 * Z.of_nat (e_cap E)); split; [exact INI| lia]| exact I].
Qed.

Lemma b1_shz_art : forall Σ (E : s1env), a1_live RT Σ E -> ART RT Σ (e_m0 E) ->
  rt_sp0 RT Σ - STACK_WIN <= bv_unsigned (e_sp E) - 448 -> bv_unsigned (e_sp E) <= USTACK_TOP -> 0 <= e_len E -> b1_shz E.
Proof using AF.
  intros Σ E LV HA SPLO SPHI LEN0 m' MU WM.
  pose proof (a1_art_step Σ E _ m' LV HA SPLO SPHI MU WM) as HA'.
  destruct LV as (INT & INI & (pb & nb & INB & B8 & BLO & BHI) & T8 & I8 & CAP4).
  split; [| split].
  - eapply shz_sub; [exact (shz_live RT AF Σ m' _ _ HA' INT T8)| lia|]. change (96 / 8) with 12. lia.
  - eapply shz_sub; [exact (shz_live RT AF Σ m' _ _ HA' INI I8)| lia|].
    pose proof (Z.div_mod (4 * Z.of_nat (e_cap E)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (4 * Z.of_nat (e_cap E)) 8 ltac:(lia)). lia.
  - eapply shz_sub; [exact (shz_live RT AF Σ m' _ _ HA' INB B8)| lia|].
    pose proof (Z.div_mod nb 8 ltac:(lia)). pose proof (Z.mod_pos_bound nb 8 ltac:(lia)). lia.
Qed.

Lemma env_ok_b_of : forall Σ (E : s1env) m, env_ok E -> a1_live RT Σ E -> ART RT Σ m -> env_ok_b E.
Proof using AF.
  intros Σ E m OK (INT & INI & (pb & nb & INB & B8 & BLO & BHI) & T8 & I8 & CAP4) HA.
  pose proof (af_live_range RT AF Σ m _ _ HA INI) as (I0 & _).
  pose proof (af_live_range RT AF Σ m _ _ HA INB) as (P0 & _).
  constructor; [exact OK| lia| exact I0|].
  pose proof (Z.div_mod (e_IDX E) 8 ltac:(lia)) as D. rewrite I8 in D.
  replace (e_IDX E) with ((2 * (e_IDX E / 8)) * 4) by lia. apply Z.mod_mul. lia.
Qed.

Theorem stage1_ok : stage1_cps RT.
Proof using AF MCP.
  intros Σ PMc E t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufo leno ws0 FDO MST OK LV LOW LOR SPT SPA ART0 MI0 ST0 PARSER0 IDXA0 IDXL BUFRO0 FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ _ ART0) as SP0R. pose proof (af_sp0_win RT AF Σ _ ART0) as SP0W.
  pose proof OK as OK'. destruct OK' as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
  pose proof (blen_nonneg (e_bs E)) as LEN0.
  set (usp := bv_unsigned (e_sp E)) in *.
  pose proof (af_client_consts RT AF Σ _ ART0) as (G1 & G2 & _).
  pose proof (b1_shz_art Σ E LV ART0 ltac:(ul) ltac:(ul) LEN0) as SHZ0.
  pose proof (env_ok_b_of Σ E _ OK LV ART0) as OKB.

  pose proof (b1_walk1 E OKB SHZ0 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufo leno MI0 (conj G1 G2) ST0 PARSER0) as W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & MID & Hc1'). clear Hc1.
  destruct MID as (m1 & u5 & u6 & u7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31
                   & j0 & j16 & j24 & j32 & j40 & jt & j304 & j312 & j320 & j328 & j332 & j336 & j340
                   & -> & MU1 & WM1 & MI1 & ST1 & FRlo1 & FRtb1 & FRhi1 & PARSER1).
  fold usp in MU1, ST1, FRlo1, FRtb1, FRhi1, Hc1'.
  pose proof (a1_art_step Σ E _ m1 LV ART0 ltac:(ul) ltac:(ul) (munch_weaken _ _ _ _ (b1_W1_sub E) MU1) WM1) as ART1.
  pose proof LV as (INT & INI & (pb & nb & INB & B8 & BLO & BHI) & T8 & I8 & CAP4).
  pose proof (af_live_range RT AF Σ _ pb nb ART0 INB) as (PB0 & PBHI & _).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -448)) = usp + -448) by (apply unsigned_lit; ul).

  apply (MCP Σ PMc (Z_to_bv 64 B1_MEMCPY_RA) (Z_to_bv 64 (usp + -448)) (e_gp E) (e_tp E) u5 u6 u7 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 0)
           (Z_to_bv 64 (usp + -400)) (Z_to_bv 64 B1_TABLE) (Z_to_bv 64 256) x13 x14 x15 x16 x17
           (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 2147450880) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E)
           (e_s10 E) (e_s11 E) x28 x29 x30 x31 (e_F E) (e_fc E) m1 (usp + -400) B1_TABLE TABLE_BYTES (e_lo E) FDO MST);
    try reflexivity; try assumption; [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - ul.
  - unfold B1_TABLE. lia.
  - apply table_at_b. exact MI1.
  - change (Z.of_nat (length TABLE_BYTES)) with 256. split.
    + intros _. split.
      * apply (acc_lit RT AF Σ m1 _ _ ART1). unfold B1_TABLE, ACC_LITS. repeat (first [left; reflexivity | right]).
      * right; right; right. unfold B1_TABLE, SEGTOP_A. lia.
    + left. unfold B1_TABLE. ul.
  - change (Z.of_nat (length TABLE_BYTES)) with 256. unfold checked_dst. rewrite EU2. split; [| split].
    + intros _. split; [apply (af_acc_stack RT AF Σ m1 _ _ ART1); ul|]. right; right; left. ul.
    + intros i Hi. left. ul.
    + exact (rw_cells_wr_at bsegs m1 _ _ 256 FRtb1 ltac:(cbn; lia)).
  - right. change (Z.of_nat (length TABLE_BYTES)) with 256. unfold B1_TABLE. ul.
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -448) with (usp + (-28) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - intros c2 (Hc2 & FC2). unfold icpt_post in Hc2.
    destruct (ASTA_unpack_f RT Σ _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BS2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (w5 & w6 & w7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. change (Z.of_nat (length TABLE_BYTES)) with 256 in PRES2.
    unfold B1_MEMCPY_RA in Hc2'. rewrite (ret_pc_even 0xb37b0) in Hc2' by lia.

    assert (STK2 : forall x, usp + -448 <= x < usp -> ~ (usp + -400 <= x < usp + -400 + 256) ->
                     aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -448) x /\ ~ (usp + -400 <= x < usp + -400 + 256))
      by (intros x Hx Hn; split; [left; ul| exact Hn]).
    assert (LIV2 : forall p n x, In (p, n) (rt_live RT Σ) -> p + n <= e_lo E -> p <= x < p + n ->
                     aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -448) x /\ ~ (usp + -400 <= x < usp + -400 + 256))
      by (intros p n x Hin Hlo Hx; split; [right; right; left; exists p, n; split; [exact Hin| exact Hx]| ul]).
    assert (FRlo2 : rw_cells bsegs m2 (usp + -448) [CB 16 j0; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40]).
    { apply (rw_cells_agree bsegs m1 m2 _ _ FRlo1); [| exact WM2]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply STK2; lia. }
    assert (FRhi2 : rw_cells bsegs m2 (usp + -144) (frame_mid_b E j304 j312 j320 j328 j332 j336 j340)).
    { apply (rw_cells_agree bsegs m1 m2 _ _ FRhi1); [| exact WM2]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
      intros x Hx. unfold frame_mid_b in Hx. cbn [cells_size csize Nat.add] in Hx. apply STK2; lia. }
    assert (FRtb2 : rw_cells bsegs m2 (usp + -400) [CB 256 TABLE_BYTES]).
    { apply (rw_cells_CB_intro m2 _ TABLE_BYTES BS2).
      apply (wr_at_transport bsegs m1 m2 _ _ (rw_cells_wr_at bsegs m1 _ _ 256 FRtb1 ltac:(cbn; lia)) WM2). }
    assert (PARSER2 : rw_cells bsegs m2 (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz (e_len E)))).
    { apply (rw_cells_agree bsegs m1 m2 _ _ PARSER1); [| exact WM2]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
      intros x Hx. unfold parser_cells in Hx. cbn [cells_size csize Nat.add] in Hx. apply (LIV2 _ _ x INT); lia. }
    assert (AG01 : agree_on (fun x => ~ (usp + -448 <= x < usp) /\ ~ (e_THIS E <= x < e_THIS E + 96)) (e_m0 E) m1).
    { apply (agree_of_munch _ _ _ _ MU1). intros x [H1 H2]. unfold b1_W1. cbn [outside]. fold usp.
      split; [lia|]. split; [exact H2| exact I]. }
    assert (IDXA2 : u32arr bsegs m2 (e_IDX E) ws0).
    { apply (u32arr_agree m1 m2); [| | exact WM2].
      + apply (u32arr_agree (e_m0 E) m1 _ _ IDXA0); [| exact WM1]. eapply agree_sub; [exact AG01|].
        intros x Hx. cbv beta in *. rewrite IDXL in Hx. split; [ul| destruct S_TI; lia].
      + apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2). intros x Hx. cbv beta in Hx. rewrite IDXL in Hx. apply (LIV2 _ _ x INI); lia. }
    assert (BUFRO2 : bytes_at bsegs m2 (e_BUF E) (padded_bytes (e_bs E))).
    { apply (bytes_at_agree bsegs m1 m2).
      + apply (bytes_at_agree bsegs (e_m0 E) m1 _ _ BUFRO0). eapply agree_sub; [exact AG01|].
        intros x Hx. cbv beta in *. rewrite padded_bytes_blen in Hx. split; [ul| destruct S_TB; lia].
      + apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2). intros x Hx. cbv beta in Hx. rewrite padded_bytes_blen in Hx.
        apply (LIV2 _ _ x INB); lia. }

    set (E2 := env_at E F2 fc2 m2).
    pose proof (env_at_ok E F2 fc2 m2 OKB) as OK2. fold E2 in OK2.
    assert (LV2 : a1_live RT Σ E2) by exact LV.
    assert (SHZ2 : b1_shz E2) by (apply (b1_shz_art Σ E2 LV2 ART2); [change (bv_unsigned (e_sp E2)) with usp; ul| change (bv_unsigned (e_sp E2)) with usp; ul| exact LEN0]).
    pose proof (b1_walk2 E2 OK2 SHZ2 w5 w6 w7 (Z_to_bv 64 (usp + -400)) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 nsi nxt ws0
                  j0 j16 j24 j32 j40 j304 j312 j320 j328 j332 j336 j340 MI2 ST2 FRlo2 FRtb2 FRhi2 PARSER2 IDXA2 IDXL BUFRO2) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c3 Hc3); intros ms POST; unfold s1_post_g in POST;
                         destruct POST as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & _); exact FRM2].
    eapply ASTA_conseq; [exact Hc3|]. intros ms POST.
    unfold s1_post_g in POST.
    destruct POST as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m' & ws' & nxt'
                      & -> & MU3 & WM3 & MI3 & ST3 & PARSER3 & NXT3 & IDXA3 & IDXL3 & IDXF3 & BUFRO3).
    change (e_m0 E2) with m2 in MU3, WM3. change (bv_unsigned (e_sp E2)) with usp in ST3.
    exists m'. split; [| split; [exact FRM2| split; [| split]]].
    + unfold ret_st. do 16 eexists. reflexivity.
    + split; [| split; [exact MI3| split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))| exact ST3]]].
      apply (a1_art_step Σ E2 m2 m' LV2 ART2); [change (bv_unsigned (e_sp E2)) with usp; ul| change (bv_unsigned (e_sp E2)) with usp; ul| exact MU3| exact WM3].
    + intros a Ha Hout. unfold a1_FP in Hout. cbn [outside] in Hout. destruct Hout as (HO1 & HO2 & _).
      pose proof (aclient_split_c RT AF Σ _ usp (bv_unsigned a) ART0 Ha) as SPL.
      assert (NFR : ~ (usp + -448 <= bv_unsigned a < usp)) by ul.
      rewrite (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | |].
      * unfold b1_W1. cbn [outside]. fold usp. split; [lia|]. split; [exact HO1| exact I].
      * apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
      * lia.
      * unfold s1_W_g. cbn [outside]. change (bv_unsigned (e_sp E2)) with usp. change (e_THIS E2) with (e_THIS E).
        change (e_IDX E2) with (e_IDX E). change (e_cap E2) with (e_cap E).
        split; [lia|]. split; [exact HO1|]. split; [exact HO2| exact I].
    + exists ws', nxt'. split; [exact PARSER3|]. split; [exact NXT3|]. split; [exact IDXA3|]. split; [exact IDXL3|].
      split; [exact IDXF3| exact BUFRO3].
Qed.

End Stage1CPS.
