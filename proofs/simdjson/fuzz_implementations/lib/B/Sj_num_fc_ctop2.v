(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lits Sj_num_bkit Sj_num_bdefs Sj_num_lm_kit
  Sj_num_fc_stmt Sj_num_fc_defs Sj_num_fc_rel Sj_num_fc_pro Sj_num_fc_pro2 Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_dc Sj_num_fc_top14 Sj_num_fc_tkit Sj_num_fc_ctop1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac fcb_at_simpl :=
  repeat match goal with
  | H : context [fcb_W (fcb_at ?E0 ?m0)] |- _ => change (fcb_W (fcb_at E0 m0)) with (fcb_W E0) in H
  | |- context [fcb_W (fcb_at ?E0 ?m0)] => change (fcb_W (fcb_at E0 m0)) with (fcb_W E0)
  | H : context [fcb_saved (fcb_at ?E0 ?m0)] |- _ => change (fcb_saved (fcb_at E0 m0)) with (fcb_saved E0) in H
  | |- context [fcb_saved (fcb_at ?E0 ?m0)] => change (fcb_saved (fcb_at E0 m0)) with (fcb_saved E0)
  end;
  cbn [fcb_at q_ra q_sp q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_A q_FIRST q_LAST q_OUT q_lo q_spq q_f q_txt q_m0] in *.

Ltac fc_close_at :=
  unfold FCINV; fcb_at_simpl;
  split; [unfold fcb_spill; fcb_at_simpl; eassumption|]; split; [do 4 eexists; unfold fcb_pns; eassumption|]; split; [lia|]; split; [lia|];
  split; [fcp_forget_obj|]; split; [fcp_forget_obj|];
  split; [first [ intros BGF; discriminate BGF | intros _; fcp_forget_obj ]|];
  split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Section FCTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HPDC : pdcb_stmt RT PMc.
  Hypothesis HNDC : ndcb_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).

  Variable E : fcbenv.
  Variables (p n : Z) (me : mem).
  Notation SP := (q_SP E).
  Notation S := (q_S E).
  Notation f := (q_f E).
  Notation lo := (q_lo E).
  Notation spq := (q_spq E).
  Notation OUT := (q_OUT E).
  Notation A := (q_A E).
  Notation FIRST := (q_FIRST E).
  Notation LAST := (q_LAST E).
  Notation TL := (q_TL E).
  Hypothesis OK : fcb_ok E.
  Hypothesis ETP : q_tp E = Z_to_bv 64 B_TP.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + FFB_FRAMES <= FRAMES_MAX)%nat.
  Hypothesis CRD : (FFB_CREDIT <= rt_credit RT Σ0)%Z.

  Hypothesis PIN : In (p, n) (rt_live RT Σ0).
  Hypothesis PCH : (p mod 8 = 0 /\ p <= A /\ LAST + 8 <= p + n /\ A + TL <= p + n)%Z.

  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (v : word), frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_ex (rt_live RT Σ0) (rt_frames RT Σ0) SP OUT 8 me m' ->
     rw_cells bsegs m' OUT [C8 v] ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - FFB_CREDIT <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR (q_ra E) (q_sp E) (q_gp E) (q_tp E) t0' t1' t2' (q_s0 E) (q_s1 E) a0' a1' a2' a3' a4' a5' a6' a7'
                               (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) t3' t4' t5' t6')
                          F' (ret_pc (q_ra E)) fc' None m' (seg_rom bsegs)).
  Collection TOPH := AF RTF FDO MST HPDC HNDC OK ETP SP16 LOR FRL CRD PIN PCH HK.

  Notation MREL := (fc_mrel RT Σ0 E me).
  Notation PARK := (fc_park E).
  Notation W := (fcb_W E).
  Notation QΣ Σ := (fun ms' => aevt RT PMc Σ K ms').
  Notation EB mb := (fcb_at E mb).

  Notation T1 L := (L RT AF RTF PMc FDO MST HPDC HNDC Σ0 K E p n me OK ETP SP16 LOR FRL CRD PIN PCH HK) (only parsing).
  Notation fc_srel := (Sj_num_fc_ctop1.fc_srel RT Σ0 E).
  Notation fc_ctx := (Sj_num_fc_ctop1.fc_ctx RT Σ0 E me).
  Notation TK L Σ SR := (L RT AF Σ0 Σ E OK LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR)))) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ E me OK LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR)))) (only parsing).

  Ltac top_env Σ SR :=
    pose proof OK as OK'; destruct OK' as [ROOM TOP [SPQ1 SPQ2] (F64 & FLO1 & FLO2) FSH FS0 (TX1 & TX2 & TX3) (FL1 & FL2 & FL3) (TS1 & TS2) (O1 & O2 & O3)];
    unfold SPB_STACK, NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, FCB_GTOP, NUM_TXT_MAX, USTACK_TOP in *;
    pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof (T1 top_inF Σ _ SR) as HinF; pose proof (T1 top_inP Σ _ SR) as HinP; pose proof PCH as (PC1 & PC2 & PC3 & PC4);
    pose proof (f64_8 f F64) as F8; pose proof (eq_refl : fs_size 4 = 1024%Z) as FS4.

  Lemma fc_kf5 : forall Σ used fc mb, fc_ctx Σ used fc mb -> fcb_kf5 (EB mb) (QΣ Σ).
  Proof using TOPH.
    intros Σ used fc mb CTX. unfold fcb_kf5. intros until FL. intros INV FRM1.
    destruct INV as (SPILL & (vb & j5 & er & j4 & PNS) & NBR & TMR & (jd & DGC) & (h0 & HDR) & BIGP & BSH & (v & OUTC) & TXT & MI & MU & WM & ST).
    clear BIGP. fcb_at_simpl. unfold fcb_spill in SPILL. unfold fcb_pns in PNS.
    destruct (T1 top_ctx_step Σ used fc mb mm CTX MU WM) as (SR & HU & FRM & ARTm & MRm & PKm). clear CTX MU WM.
    destruct PKm as ((jh & HIGHc) & SAVED & (h & HDR24) & SHW).
    top_env Σ SR. pose proof SR as (EF & EL & ES & EC).
    apply evt_done.
    eapply (aevt_set_shadow RT RTF PMc FDO MST Σ K 0xf5%Z) with (d := S) (n := 128%Z) (lo := lo);
      [unfold set_shadow_vals; cbn [In]; do 11 right; left; reflexivity | reflexivity | reflexivity | lia
      | intros i Hi; exists f, 4%nat; split; [exact HinF|]; unfold shad, SHB; rewrite FS4; replace (f + 1024)%Z with (f + 128 * 8)%Z by lia; rewrite Z.div_add by lia; lia
      | exact SHW | exact ARTm | exact MI | exact (T1 top_cok Σ used mm SR ST) | exact FRM1 |].
    intros v0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m3 FRM' RA PR _.
    rewrite ?unsigned_lit in RA, PR by lia. destruct RA as (ART3 & MI3 & WM3 & ST3).
    pose proof (TKm fc_mrel_ex Σ SR mm m3 S 128%Z ARTm MRm WM3 PR ltac:(right; left; lia)) as MR3.
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m3 (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x /\ ~ (S <= x < S + 128)%Z) PR (fun x H => H)) as AG.
    unfold fcb_saved in SAVED. clear ST MI SHW BSH TXT HDR HDR24.
    rt_transport_with mm m3 AG WM3 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac| lia]).

    destruct (af_frame_release RT AF Σ m3 f 4%nat (rt_frames RT Σ0) ART3 EF) as (Σ2 & fl & FLAG & NAC & FL0 & FL1' & LAST' & REL).
    rewrite FS4 in LAST'. replace (f + 1024 - 8)%Z with (f + 1016)%Z in LAST' by lia.
    pose proof (af_sp0_range RT AF Σ m3 ART3) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R. pose proof (T1 top_lor1 Σ used SR) as LOR1. unfold STACK_WIN in LOR1, FL1'.
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply (fcb_rel2 f fl m3 ltac:(lia) ltac:(lia) _); [exact LAST' | exact FLAG | exact MI3 | apply munch_refl | apply wmono_refl |].
    clear LAST' FLAG MI3. intros mm4 FLAG0 MI4 MU4 WM4.
    destruct (REL mm4 MU4 WM4 FLAG0) as (ART4 & EF4 & EL4 & ES4 & EC4 & EA4 & EM4).
    apply evt_done. apply (aevt_frame_release RT PMc Σ Σ2 K _ EA4 EM4).
    assert (FLO' : (fl < OUT \/ OUT + 8 <= fl)%Z).
    { destruct (Z_lt_le_dec fl OUT) as [H|H]; [left; exact H|]. destruct (Z_lt_le_dec fl (OUT + 8)) as [H2|H2]; [| right; exact H2].
      exfalso. apply NAC. left. unfold USTACK_TOP in *. lia. }
    transport_after_call bsegs m3 mm4 MU4 WM4.
    assert (MR4 : MREL mm4).
    { destruct MR3 as [WMa PRa]. split; [exact (wmono_trans bsegs _ _ _ WMa WM4)|]. eapply pres_fp_trans; [exact PRa|].
      apply (pres_fp_of_munch _ _ _ _ [(fl, (fl + 1)%Z)] _ _ MU4). intros a Ha _. cbn [outside]. split; [| exact I]. intros Hfl. apply NAC.
      assert (a = fl) by lia. subst a.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [left; unfold USTACK_TOP in *; lia | right; left; exact Ha | right; right; left; rewrite EL; exact Ha
        | right; right; right; left; destruct Ha as (f1 & k1 & Hin & Hr); exists f1, k1; split; [rewrite EF; right; exact Hin| exact Hr]
        | right; right; right; right; destruct Ha as (f1 & k1 & Hin & Hr); exists f1, k1; split; [rewrite EF; right; exact Hin| exact Hr]]. }

    assert (WORK : rw_cells bsegs mm4 spq ([C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 (Z_to_bv 64 f)] ++
                     [C8 (Z_to_bv 64 q); C8 w; C8 lm; C1 (Z_to_bv 8 nb); C1 vb; C1 (Z_to_bv 8 tm); CB 5 j5; C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL); C4 er; CB 4 j4] ++ [CB 8 jd])).
    { apply (proj2 (num_rw_cells_app bsegs mm4 spq _ _)). split; [exact SPILL|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 72) with 72%Z.
      apply (proj2 (num_rw_cells_app bsegs mm4 (spq + 72) _ _)). split; [exact PNS|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 72) with 72%Z.
      replace (spq + 72 + 72)%Z with (spq + 144)%Z by lia. exact DGC. }
    destruct (rw_cells_forget bsegs _ _ _ WORK) as [jsp SPILLf]. cbn [app cells_size csize Nat.add] in SPILLf.
    apply (aevt_evt RT AF PMc MST).
    eapply (fcb_leave E OK F' fc' (fun ms' => aevt RT PMc Σ2 K ms')); [exact SPILLf | exact HIGHc | exact SAVED | exact ST3 |].
    intros zt0 zt1 zt2 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 STF.
    apply evt_done.
    eapply HK; [exact FRM' | | | exact OUTC | exact EF4 | rewrite EL4; exact EL | rewrite ES4; exact ES | rewrite EC4; unfold FFB_CREDIT; lia].
    - split; [exact ART4|]. split; [exact MI4|]. split; [exact (proj1 MR4)| exact STF].
    - intros a Ha Hn. apply (proj2 MR4 a Ha). cbn [outside]. split; [lia| exact I].
  Qed.

  Lemma fc_ctx_call2 : forall Σ Σ' used used' fc fc' (mm m' : mem) D N, fc_ctx Σ used fc mm -> fc_srel Σ' used' -> (0 <= used' <= 9)%Z -> frm0 fc' ->
    rt_after RT Σ' spq lo mm m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq D N mm m' ->
    ((f + 32 <= D /\ D + N <= f + 536) \/ (spq <= D /\ D + N <= spq + 152))%Z -> fc_ctx Σ' used' fc' m'.
  Proof using TOPH.
    intros Σ Σ' used used' fc fc' mm m' D N (SR & HU & FRM & HA & MR & PK) SR' HU' FRM' (ART' & MI' & WM' & ST') PR HD.
    split; [exact SR'|]. split; [exact HU'|]. split; [exact FRM'|]. split; [exact ART'|].
    top_env Σ SR.
    split; [eapply (TKm fc_mrel_ex Σ SR mm m' D N HA MR WM' PR); clear FSH TS1 TS2; lia|].
    destruct PK as ((jh & P2) & P3 & (h & P4) & P6).
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x /\ ~ (D <= x < D + N)%Z) PR (fun x H => H)) as AG.
    unfold fcb_saved in P3.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac| lia]).
    split; [exists jh; exact P2|]. split; [exact P3|]. split; [exists h; exact P4| exact P6].
  Qed.
  Lemma fc_ctx_call : forall Σ used fc fc' (mm m' : mem) D N, fc_ctx Σ used fc mm -> frm0 fc' -> rt_after RT Σ spq lo mm m' ->
    rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq D N mm m' -> ((f + 32 <= D /\ D + N <= f + 536) \/ (spq <= D /\ D + N <= spq + 152))%Z -> fc_ctx Σ used fc' m'.
  Proof using TOPH.
    intros Σ used fc fc' mm m' D N CTX FRM' RA PR HD. pose proof CTX as (SR & HU & _).
    exact (fc_ctx_call2 Σ Σ used used fc fc' mm m' D N CTX SR HU FRM' RA PR HD).
  Qed.
End FCTOP.
