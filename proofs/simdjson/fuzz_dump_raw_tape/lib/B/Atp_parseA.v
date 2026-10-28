(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_stage1_kit Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_stage1_iface Sj_stage2_iface Sj_h_layout Atp_hkit3A Sj_h_parsew.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition PARSE_STACK : Z := S2A_STACK + 64.

Definition parse_X (THIS IDX TAPE SBUF OC IA ncap tcap scap : Z) : list (Z * Z) :=
  [(THIS, THIS + 96); (IDX, IDX + 4 * ncap); (TAPE, TAPE + 8 * tcap); (SBUF, SBUF + scap); (OC, OC + 8192); (IA, IA + 1024)].

Section ParseCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis S1 : stage1_cps RT.
Hypothesis S2 : stage2at_cps RT.

Local Ltac ul := unfold PARSE_STACK, S2A_STACK, Sj_num_iface.NUMA_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition parse_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
         (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (bs : list Z) (ws0 : list word) (tcap scap : Z)
         (vptr capv nsi nxt bufv lenv docv dcap : word) (p12 p28 p50 : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 BUF -> a2 = Z_to_bv 64 (blen bs) -> a3 = Z_to_bv 64 DOC -> tp = Z_to_bv 64 0x6abde8 -> frm0 fc ->
  bytes_ok bs -> blen bs <= 1048512 ->
  blen bs + 3 <= tcap -> tcap <= 2^40 -> 5 * blen bs + 5 <= 3 * scap -> scap <= 2^40 -> scap mod 8 = 0 ->
  blen bs + 4 <= Z.of_nat (length ws0) -> Z.of_nat (length ws0) < 2^40 ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PARSE_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  (length (rt_frames RT Σ) + S2A_FRAMES <= FRAMES_MAX)%nat -> S2A_COST (blen bs) <= rt_credit RT Σ ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX ->
  In (THIS, 96) (rt_live RT Σ) -> In (IDX, 4 * Z.of_nat (length ws0)) (rt_live RT Σ) -> live_reg RT Σ BUF (blen bs + 64) ->
  live_reg RT Σ TAPE (8 * tcap) -> live_reg RT Σ SBUF scap -> live_reg RT Σ OC 8192 -> live_reg RT Σ IA 1024 ->
  THIS mod 8 = 0 -> IDX mod 8 = 0 -> TAPE mod 8 = 0 -> SBUF mod 8 = 0 -> OC mod 8 = 0 -> IA mod 8 = 0 ->
  pairwise_disj [(THIS, 96); (IDX, 4 * Z.of_nat (length ws0)); (BUF, blen bs + 64); (TAPE, 8 * tcap); (SBUF, scap); (OC, 8192); (IA, 1024)] ->
  fobj RT Σ m DOC 24 ->
  rw_cells bsegs m THIS (impl16 vptr nsi p12 (Z_to_bv 64 IDX) nxt p28 capv (Z_to_bv 64 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50
                                (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
  rw_cells bsegs m DOC [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 dcap] ->
  u32arr bsegs m IDX ws0 ->
  bytes_at bsegs m BUF (padded_bytes bs) ->
  (exists ocs, u32arr bsegs m OC ocs /\ length ocs = 2048%nat) ->
  (exists ias, u8arr bsegs m IA ias /\ length ias = 1024%nat) ->
  cps_f
    (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                 t3 t4 t5 t6 F fc e_parse m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m' (v : word),
           ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ bv_unsigned v < 64
         /\ s2a_okres TAPE SBUF tcap scap v m'
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (parse_X THIS IDX TAPE SBUF OC IA (Z.of_nat (length ws0)) tcap scap) m m'
         /\ (exists nsi' nxt' bufv' lenv' docv',
               rw_cells bsegs m' THIS (impl16 vptr nsi' p12 (Z_to_bv 64 IDX) nxt' p28 capv (Z_to_bv 64 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50
                                              (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv' lenv' docv'))) c
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - S2A_COST (blen bs) <= rt_credit RT Σ').

Theorem parse_ok : parse_cps.
Proof using AF S1 S2.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    THIS DOC IDX BUF TAPE SBUF OC IA bs ws0 tcap scap vptr capv nsi nxt bufv lenv docv dcap p12 p28 p50
    FDO MST -> -> -> -> -> FRM BOK LEN TC1 TC2 SC1 SC2 SC8 ICAP ICAPH ART0 MI0 ST0 LOW LOR SPT SPA FRB CRB LVB
    INT INI RBUF RTAPE RSBUF ROC RIA T8 I8 TP8 SB8 OC8 IA8 PD FOBJ0 THISC DOCC ARR BUFB OCA IAA.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (BL0 : 0 <= blen bs) by (unfold blen; lia).

  pose proof (af_live_range RT AF Σ m THIS 96 ART0 INT) as (TH0 & TH1 & _).
  pose proof (af_live_range RT AF Σ m IDX _ ART0 INI) as (IX0 & IX1 & _).
  pose proof (live_reg_range RT AF Σ m BUF _ ART0 RBUF ltac:(lia)) as (BF0 & BF1 & _).
  pose proof (live_reg_range RT AF Σ m OC _ ART0 ROC ltac:(lia)) as (OC0 & OC1 & _).
  pose proof (live_reg_range RT AF Σ m IA _ ART0 RIA ltac:(lia)) as (IA0 & IA1 & _).
  pose proof FOBJ0 as (D8 & _ & (f & k & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f k ART0 INF) as (F0 & F1 & FSZ & _).
  assert (FP1 : fp_client RT Σ lo [(usp - 32, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).

  pose proof (pa_walk1 usp lo ra gp (Z_to_bv 64 0x6abde8) t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 BUF) (Z_to_bv 64 (blen bs)) (Z_to_bv 64 DOC)
                a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FP1 MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ DOC 24 ART0 LOW FP1 MU1 FOBJ0) as FOBJ1.
  assert (AG1 : agree_on (fun x => x < usp - 32) m m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. split; [lia| exact I]. }

  assert (THISC1 := THISC). apply (rw_cells_agree bsegs m m1 _ _) in THISC1; [| eapply agree_sub; [exact AG1|]; intros x Hx; unfold impl16 in Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; ul| exact WM1].
  assert (DOCC1 := DOCC). apply (rw_cells_agree bsegs m m1 _ _) in DOCC1; [| eapply agree_sub; [exact AG1|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; ul| exact WM1].
  assert (ARR1 : u32arr bsegs m1 IDX ws0) by (apply (u32arr_agree m m1 _ _ ARR); [eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul| exact WM1]).
  assert (BUFB1 : bytes_at bsegs m1 BUF (padded_bytes bs)).
  { apply (bytes_at_agree bsegs m m1 _ _ BUFB). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. rewrite padded_bytes_blen in Hx. ul. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -32) mod 16 = 0) by (replace (usp + -32) with (usp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).

  apply impl16_s1 in THISC1.
  set (MID := mid16 p28 capv (Z_to_bv 64 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA)) in *.
  set (E := mkS1Env (Z_to_bv 64 0xe6f7c) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6abde8) (Z_to_bv 64 DOC) (Z_to_bv 64 THIS)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo THIS BUF IDX bs (length ws0) vptr p12 MID (le8 docv) m1).
  assert (OK : env_ok E).
  { pose proof (pairwise_disj_nth _ 0 1 _ _ PD eq_refl eq_refl ltac:(lia)) as D_TH_IX.
    pose proof (pairwise_disj_nth _ 0 2 _ _ PD eq_refl eq_refl ltac:(lia)) as D_TH_BF.
    pose proof (pairwise_disj_nth _ 1 2 _ _ PD eq_refl eq_refl ltac:(lia)) as D_IX_BF.
    unfold ivl_disj in D_TH_IX, D_TH_BF, D_IX_BF. cbn [fst snd] in D_TH_IX, D_TH_BF, D_IX_BF.
    unfold E. constructor; cbn [e_bs e_lo e_sp e_THIS e_IDX e_BUF e_cap]; unfold S1_LEN_MAX, A1_GTOP, A1_STACK; rewrite ?EU2; try assumption.
    all: clear - LEN LOW LOR TH0 TH1 IX0 IX1 BF0 BF1 ICAP D_TH_IX D_TH_BF D_IX_BF SP0R SP0W; ul. }
  assert (LV : a1_live RT Σ E).
  { unfold a1_live, E. cbn [e_THIS e_IDX e_BUF e_cap e_bs]. split; [exact INT|]. split; [exact INI|]. split.
    - destruct RBUF as (pb & nb & INB & B8 & BLO & BHI). exists pb, nb. split; [exact INB|]. split; [exact B8|]. split; [exact BLO| lia].
    - split; [exact T8|]. split; [exact I8| exact ICAP]. }
  destruct (stage1 bs) as [code idxs] eqn:ES.
  pose proof (stage1_code_range bs) as CR. rewrite ES in CR. cbn [fst] in CR.
  apply (S1 Σ PMc E t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufv lenv ws0 FDO MST OK LV);
    [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - exact LOW.
  - cbn [E e_lo e_sp]. rewrite EU2. ul.
  - cbn [E e_sp]. rewrite EU2. ul.
  - cbn [E e_sp]. rewrite EU2. exact SPA2.
  - exact ART1.
  - exact MI1.
  - cbn [E e_m0 e_lo e_sp]. rewrite EU2. exact ST1.
  - exact THISC1.
  - exact ARR1.
  - reflexivity.
  - exact BUFB1.
  - exact FRM.
  - intros c2 (Hc2 & FC2).
    destruct (ASTA_unpack_f RT Σ _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & FRM2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & RES2) & _ & Hc2'). clear Hc2.
    cbn [E e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_m0 e_bs] in RS2, ST2, PRES2, RES2.
    rewrite ES in RS2, RES2. cbn [fst snd] in RS2, RES2.
    rewrite EU2 in ST2, PRES2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite (ret_pc_even 0xe6f7c) in Hc2' by lia.
    destruct RES2 as (ws' & nxt' & THISC2 & NXT2 & ARR2 & LWS2 & FIRSTN & BUFB2).
    unfold parser_cells in THISC2. cbn [E e_THIS e_IDX e_BUF e_bs e_cap e_vptr e_p12 e_mid e_docj] in THISC2, ARR2, LWS2, BUFB2.
    unfold a1_FP in PRES2. cbn [E e_THIS e_IDX e_cap] in PRES2.
    destruct (impl16_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ THISC) as (L12 & L28 & L50).
    apply (s1_impl16 m2 THIS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L28 L50) in THISC2.

    assert (FR2 : rw_cells bsegs m2 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul|]. cbn [outside]. split; [ul|]. split; [ul| exact I]. }
    destruct (Z.eqb_spec code 0) as [C0|CN].
    +
      subst code.
      pose proof (pa_walk2 usp lo j gp (Z_to_bv 64 0x6abde8) u0 u1 u2 (Z_to_bv 64 DOC) (Z_to_bv 64 THIS) b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 s1 F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) FR2 MI2) as W2.
      lazymatch type of W2 with evt bsegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & ST3) & Hc3'). clear Hc3.
      pose proof (art_fp_client RT AF Σ m2 m3 lo _ ART2 LOW FP1 MU3 WM3) as ART3.
      rewrite <- ESP in Hc3'.

      assert (AG3 : agree_on (fun x => x < usp - 32) m2 m3).
      { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. split; [lia| exact I]. }
      assert (AG13 : forall (P : Z -> Prop),
                (forall x, P x -> x < usp - 32 /\ aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -32) x
                                  /\ ~ (THIS <= x < THIS + 96) /\ ~ (IDX <= x < IDX + 4 * Z.of_nat (length ws0))) -> agree_on P m1 m3).
      { intros P HP. eapply agree_trans; [| eapply agree_sub; [exact AG3| intros x Hx; exact (proj1 (HP x Hx))]].
        apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2). intros x Hx. destruct (HP x Hx) as (_ & H2 & H3 & H4).
        split; [exact H2|]. cbn [outside]. split; [exact H3|]. split; [exact H4| exact I]. }
      assert (DOCC3 : rw_cells bsegs m3 DOC [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 dcap]).
      { apply (rw_cells_agree_nw bsegs m1 m3 _ _ DOCC1). apply AG13. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
        pose proof (af_frames_range RT AF Σ m f k ART0 INF) as (_ & _ & _ & FLV).
        pose proof (FLV THIS 96 INT) as F_TH. pose proof (FLV IDX _ INI) as F_IX.
        split; [ul|]. split; [right; right; right; left; exists f, k; split; [exact INF| lia]|]. clear - Hx F_TH F_IX FLO FHI. split; lia. }
      assert (FOBJ3 : fobj RT Σ m3 DOC 24).
      { apply (fobj_agree RT AF Σ Σ m1 m3 DOC 24 ART1 FOBJ1 eq_refl).
        destruct (fobj_shadow_range RT AF Σ m1 DOC 24 ART1 FOBJ1) as (f' & k' & INF' & S1' & S2' & _).
        pose proof (af_fshadow_apart RT AF Σ m1 f' k' ART1 INF') as (SL & _).
        pose proof (SL THIS 96 INT) as X1. pose proof (SL IDX _ INI) as X2.
        pose proof (af_frames_range RT AF Σ m1 f' k' ART1 INF') as (F0' & F1' & _).
        assert (FSZ' : 0 <= fs_size k') by (unfold fs_size; apply Z.shiftl_nonneg; lia).
        assert (SH1 : shad (f' + fs_size k') <= 17592186044416 + SHB).
        { unfold shad. assert ((f' + fs_size k') / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; ul). lia. }
        apply AG13. intros x Hx. cbv beta in Hx. change ((24 + 7) / 8) with 3 in *.
        split; [clear X1 X2; unfold SHB in *; ul|]. split; [right; right; right; right; exists f', k'; split; [exact INF'| lia]|].
        clear - Hx X1 X2 S1' S2'. split; lia. }
      destruct OCA as (ocs & OCA & LOCS). destruct IAA as (ias & IAA & LIAS).
      assert (OCA3 : u32arr bsegs m3 OC ocs).
      { apply (u32arr_agree_nw m1 m3); [apply (u32arr_agree m m1 _ _ OCA); [eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; rewrite LOCS in Hx; ul| exact WM1]|].
        apply AG13. intros x Hx. cbv beta in Hx. rewrite LOCS in Hx.
        pose proof (pairwise_disj_nth _ 0 5 _ _ PD eq_refl eq_refl ltac:(lia)) as D_TH_OC.
        pose proof (pairwise_disj_nth _ 1 5 _ _ PD eq_refl eq_refl ltac:(lia)) as D_IX_OC.
        unfold ivl_disj in D_TH_OC, D_IX_OC. cbn [fst snd] in D_TH_OC, D_IX_OC.
        split; [clear D_TH_OC D_IX_OC; ul|]. split; [apply (live_reg_client RT Σ OC 8192); [exact ROC| lia]|]. clear - Hx D_TH_OC D_IX_OC. split; lia. }
      assert (IAA3 : u8arr bsegs m3 IA ias).
      { apply (u8arr_agree_nw m1 m3).
        - destruct IAA as [Hb Hw]. split; [apply (bytes_at_agree bsegs m m1 _ _ Hb); eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; rewrite LIAS in Hx; ul|].
          exact (wr_at_transport bsegs m m1 _ _ Hw WM1).
        - apply AG13. intros x Hx. cbv beta in Hx. rewrite LIAS in Hx.
          pose proof (pairwise_disj_nth _ 0 6 _ _ PD eq_refl eq_refl ltac:(lia)) as D_TH_IA.
          pose proof (pairwise_disj_nth _ 1 6 _ _ PD eq_refl eq_refl ltac:(lia)) as D_IX_IA.
          unfold ivl_disj in D_TH_IA, D_IX_IA. cbn [fst snd] in D_TH_IA, D_IX_IA.
          split; [clear D_TH_IA D_IX_IA; ul|]. split; [apply (live_reg_client RT Σ IA 1024); [exact RIA| lia]|]. clear - Hx D_TH_IA D_IX_IA. split; lia. }
      assert (THISC3 : rw_cells bsegs m3 THIS (impl16 vptr (Z_to_bv 64 (Z.of_nat (length idxs))) p12 (Z_to_bv 64 IDX) nxt' p28 capv (Z_to_bv 64 1024)
                                                      (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) (Z_to_bv 64 BUF) (Z_to_bv 64 (blen bs)) docv)).
      { apply (rw_cells_agree_nw bsegs m2 m3 _ _ THISC2). eapply agree_sub; [exact AG3|]. intros x Hx. unfold impl16 in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (ARR3 : u32arr bsegs m3 IDX ws').
      { apply (u32arr_agree_nw m2 m3 _ _ ARR2). eapply agree_sub; [exact AG3|]. intros x Hx. cbv beta in *. rewrite LWS2 in Hx. ul. }
      assert (BUFB3 : bytes_at bsegs m3 BUF (padded_bytes bs)).
      { apply (bytes_at_agree bsegs m2 m3 _ _ BUFB2). eapply agree_sub; [exact AG3|]. intros x Hx. cbv beta in *. rewrite padded_bytes_blen in Hx. ul. }
      pose proof (stage1_S1OUT bs idxs ES) as SO1.
      apply (S2 Σ PMc ra sp gp (Z_to_bv 64 0x6abde8) u0 u1 u2 s0 s1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 lo
               THIS DOC IDX BUF TAPE SBUF OC IA bs idxs ws' tcap scap vptr capv nxt' docv dcap p12 p28 p50 FDO MST eq_refl FRM2 SO1 BOK LEN FIRSTN
               TC1 TC2 SC1 SC2 SC8); rewrite ?LWS2; try assumption.
      * fold usp. ul.
      * apply live_reg_of_in; assumption.
      * apply live_reg_of_in; assumption.
      * exists ocs. split; assumption.
      * exists ias. split; assumption.
      * split; [exact Hc3'| apply (cfrm0_of_asta RT Σ PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2].
      * intros c4 ((Σ4 & Hc4 & FRS4 & LV4 & SP4 & CR4) & FC4).
        apply Hk. split; [| exact FC4]. exists Σ4.
        split; [| split; [exact FRS4| split; [exact LV4| split; [exact SP4| exact CR4]]]].
        eapply ASTA_conseq; [exact Hc4|]. intros ms (m4 & v & nxt4 & RS4 & V64 & OKRES4 & _ & AFT4 & PRES4 & THISC4). fold usp in AFT4, PRES4.
        exists m4, v. split; [exact RS4|]. split; [exact V64|]. split; [exact OKRES4|]. split; [exact AFT4|]. split.
        -- intros a Ha Hout. unfold parse_X in Hout. cbn [outside] in Hout. destruct Hout as (HO1 & HO2 & HO3 & HO4 & HO5 & HO6 & _).
           pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
           rewrite (PRES4 a), (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | | | |].
           ++ cbn [outside]. split; [clear - SPL LOW LOR; ul| exact I].
           ++ apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
           ++ cbn [outside]. split; [exact HO1|]. split; [exact HO2| exact I].
           ++ cbn [outside]. split; [clear - SPL LOW LOR; ul| exact I].
           ++ exact Ha.
           ++ unfold s2a_X. cbn [outside]. repeat (split; [assumption|]). exact I.
        -- exists (Z_to_bv 64 (Z.of_nat (length idxs))), nxt4, (Z_to_bv 64 BUF), (Z_to_bv 64 (blen bs)), (Z_to_bv 64 DOC). exact THISC4.
    +
      pose proof (pa_walk3 usp lo code j gp (Z_to_bv 64 0x6abde8) u0 u1 u2 (Z_to_bv 64 DOC) (Z_to_bv 64 THIS) b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 s1 F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) FR2 MI2) as W3.
      lazymatch type of W3 with evt bsegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W3') Hc2'). clear W3'. intros c3 Hc3.
      apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c3 Hc3); intros ms (m3 & _ & E3 & _); rewrite E3; exact FRM2].
      exists Σ. split; [| split; [reflexivity| split; [reflexivity| split; [reflexivity|]]]].
      2:{ unfold S2A_COST. assert (0 <= mcost (blen bs + 64)) by (unfold mcost, DCOST; destruct (blen bs + 64 <=? 64512); lia). unfold Sj_num_iface.NUMA_CREDIT. lia. }
      eapply ASTA_conseq; [exact Hc3|]. intros ms (m3 & RS3 & _ & MU3 & WM3 & MI3 & ST3). exists m3, (Z_to_bv 64 code).
      split; [rewrite ESP; exact RS3|].
      split; [rewrite unsigned_lit by (clear - CR; lia); clear - CR; lia|].
      split; [left; rewrite unsigned_lit by (clear - CR; lia); clear - CR CN; lia|].
      split; [split; [exact (art_fp_client RT AF Σ m2 m3 lo _ ART2 LOW FP1 MU3 WM3)| split; [exact MI3| exact ST3]]|].
      split.
      * intros a Ha Hout. unfold parse_X in Hout. cbn [outside] in Hout. destruct Hout as (HO1 & HO2 & _).
        pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
        rewrite (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | |].
        -- cbn [outside]. split; [clear - SPL LOW LOR; ul| exact I].
        -- apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
        -- cbn [outside]. split; [exact HO1|]. split; [exact HO2| exact I].
        -- cbn [outside]. split; [clear - SPL LOW LOR; ul| exact I].
      * exists (Z_to_bv 64 (Z.of_nat (length idxs))), nxt', (Z_to_bv 64 BUF), (Z_to_bv 64 (blen bs)), docv.
        apply (rw_cells_agree bsegs m2 m3 _ _ THISC2); [| exact WM3]. apply (agree_of_munch _ _ _ _ MU3).
        intros x Hx. unfold impl16 in Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I].
Qed.

End ParseCPS.
