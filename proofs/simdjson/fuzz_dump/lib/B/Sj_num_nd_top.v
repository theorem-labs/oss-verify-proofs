(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_shl_top
  Sj_num_lm_pro Sj_num_lm_kit Sj_num_nd_pro Sj_num_nd_defs Sj_num_nd_a Sj_num_nd_b3 Sj_num_nd_b Sj_num_nd_rel Sj_num_nd_tkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section NDTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HP5 : p5b_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo d spq f g : Z) (kg : nat) (me : mem) (p2 e cr : Z).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis ETP : tp = Z_to_bv 64 B_TP.
  Hypothesis ROOM : (lo + NDCB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + 2 <= FRAMES_MAX)%nat.
  Hypothesis HE : (0 <= e < 135 * (cr + 1))%Z.
  Hypothesis HCR : (0 <= cr)%Z.
  Hypothesis HER : (e <= NDCB_RANGE)%Z.
  Hypothesis CRD : (cr + 1 <= rt_credit RT Σ0)%Z.
  Hypothesis PR : (- NDCB_RANGE <= p2 <= NDCB_RANGE)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 160 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x6cd000 <= f /\ f + 1016 <= lo /\ (f + 1016 <= S \/ S + 127 <= f) /\ 0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XG : In (g, kg) (rt_frames RT Σ0) /\ (g <= X)%Z /\ (X + 504 <= g + fs_size kg - 8)%Z.
  Hypothesis XNUM : (0x6cd000 <= X /\ X + 504 <= lo /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 1024 <= X) /\ (X + 504 <= S \/ S + 128 <= X)
                    /\ (X / 8 + 2147450880 + 63 <= f \/ f + 1024 <= X / 8 + 2147450880)
                    /\ (X / 8 + 2147450880 + 63 <= S \/ S + 128 <= X / 8 + 2147450880))%Z.

  Hypothesis HK : dc_k RT PMc Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 me X lo (cr + 1).
  Collection TOPH := AF RTF FDO MST HP5 ETP ROOM TOP SP16 LOR FRL HE HCR HER CRD PR SPQ NF X8 XG XNUM SEP HK.

  Notation MREL := (nd_mrel RT Σ0 sp X me).
  Notation PARK := (nd_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo d spq f).
  Notation QΣ Σ := (fun ms' => aevt RT PMc Σ K ms').

  Definition nd_srel (Σ : rts RT) (used : Z) : Prop :=
    rt_frames RT Σ = (f, 4%nat) :: rt_frames RT Σ0 /\ rt_live RT Σ = rt_live RT Σ0 /\ rt_sp0 RT Σ = rt_sp0 RT Σ0
    /\ (rt_credit RT Σ0 - 1 - used <= rt_credit RT Σ)%Z.

  Definition nd_ctx (Σ : rts RT) (used : Z) (fc : bv 32) (mb : mem) : Prop :=
    nd_srel Σ used /\ (0 <= used <= cr)%Z /\ frm0 fc /\ ART RT Σ mb /\ MREL mb /\ PARK mb.

  Notation TK L Σ SR := (L RT AF Σ0 Σ sp X lo d spq f g kg ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF X8 XG XNUM SEP) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ sp X lo d spq f g kg me ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF X8 XG XNUM SEP) (only parsing).

  Lemma top_spq : (0 <= d <= 16 /\ spq = SP - 160 - d)%Z.
  Proof using TOPH. destruct SPQ as [[->| ->] ->]; lia. Qed.
  Lemma top_er : (0 <= e <= NDCB_RANGE)%Z.
  Proof using TOPH. destruct HE. split; [assumption| exact HER]. Qed.
  Lemma top_lor1 : forall Σ used, nd_srel Σ used -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z.
  Proof using TOPH. intros Σ used (_ & _ & ES & _). rewrite ES. exact LOR. Qed.
  Lemma top_inF : forall Σ used, nd_srel Σ used -> In (f, 4%nat) (rt_frames RT Σ).
  Proof using TOPH. intros Σ used (EF & _). rewrite EF. left. reflexivity. Qed.
  Lemma top_inG : forall Σ used, nd_srel Σ used -> In (g, kg) (rt_frames RT Σ).
  Proof using TOPH. intros Σ used (EF & _). rewrite EF. right. exact (proj1 XG). Qed.
  Lemma top_art : forall Σ used W (mb mm : mem), nd_srel Σ used -> tk_wf sp X lo f W -> ART RT Σ mb -> munch W mb mm -> wmono bsegs mb mm -> ART RT Σ mm.
  Proof using TOPH. intros Σ used W mb mm SR HW HA MU WM. exact (art_of_munch RT AF Σ mb mm lo W HA (top_lor1 Σ used SR) (TK tk_fpok Σ SR W HW) MU WM). Qed.
  Lemma top_mrel : forall Σ used W (mb mm : mem), nd_srel Σ used -> tk_wf sp X lo f W -> ART RT Σ mb -> MREL mb -> munch W mb mm -> wmono bsegs mb mm -> MREL mm.
  Proof using TOPH. intros Σ used W mb mm SR. exact (TKm nd_mrel_munch Σ SR W mb mm). Qed.
  Lemma top_wfWN : forall Σ used, nd_srel Σ used -> tk_wf sp X lo f (nd_W X spq f).
  Proof using TOPH. intros Σ used SR. exact (TK tk_wf_WN Σ SR). Qed.
  Lemma top_ctx_stepW : forall W Σ used fc (mb mm : mem), tk_wf sp X lo f W -> tk_wfp X spq f W -> nd_ctx Σ used fc mb -> munch W mb mm -> wmono bsegs mb mm -> nd_ctx Σ used fc mm.
  Proof using TOPH.
    intros W Σ used fc mb mm HW HWP (SR & HU & FRM & HA & MR & PK) MU WM. split; [exact SR|]. split; [exact HU|]. split; [exact FRM|].
    split; [exact (top_art Σ used _ mb mm SR HW HA MU WM)|].
    split; [exact (top_mrel Σ used _ mb mm SR HW HA MR MU WM)|].
    apply (nd_park_munch RT AF Σ0 Σ ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g kg ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF X8 XG XNUM SEP
             W mb mm HWP PK MU WM).
  Qed.
  Lemma top_ctx_step : forall Σ used fc (mb mm : mem), nd_ctx Σ used fc mb -> munch (nd_W X spq f) mb mm -> wmono bsegs mb mm -> nd_ctx Σ used fc mm.
  Proof using TOPH. intros Σ used fc mb mm CTX. pose proof CTX as (SR & _). exact (top_ctx_stepW _ Σ used fc mb mm (top_wfWN Σ used SR) (TK tk_wfp_WN Σ SR) CTX). Qed.
  Lemma top_ctx_stepA : forall Σ used fc (mb mm : mem), nd_ctx Σ used fc mb ->
    munch [(spq, spq + 56); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z mb mm -> wmono bsegs mb mm -> nd_ctx Σ used fc mm.
  Proof using TOPH. intros Σ used fc mb mm CTX. pose proof CTX as (SR & _). exact (top_ctx_stepW _ Σ used fc mb mm (TK tk_wf_WA Σ SR) (TK tk_wfp_WA Σ SR) CTX). Qed.
  Lemma top_cok : forall Σ used (mm : mem), nd_srel Σ used -> stk bsegs mm lo spq -> call_ok RT Σ mm (Z_to_bv 64 spq) lo.
  Proof using TOPH.
    intros Σ used mm SR ST. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (stk_lo_nonneg bsegs _ _ _ ST) as LO0. destruct SPQ as [Hd Hs]. unfold NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in *.
    unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST|]. split; [exact (top_lor1 Σ used SR)|]. unfold RT_STACK, USTACK_TOP.
    split; [lia|]. split; [lia| Z.div_mod_to_equations; lia].
  Qed.

  Ltac top_env Σ SR :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof XNUM as (Q1 & Q2 & Q3 & Q4 & Q5); pose proof SEP as (E1 & E2 & E3 & E4);
    pose proof top_spq as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (top_inF Σ _ SR) as HinF; pose proof (f64_8 f (proj1 NF)) as F8; pose proof (eq_refl : fs_size 4 = 1024%Z) as FS4;
    pose proof (proj1 (proj2 XG)) as G1; pose proof (proj2 (proj2 XG)) as G2; pose proof (top_inG Σ _ SR) as HinG;
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    assert (F32 : ((f + 32) / 8 = f / 8 + 4)%Z) by (replace (f + 32)%Z with (f + 8 * 4)%Z by lia; apply f64_div; exact (proj1 NF)).

  Lemma nd_ctx_call2 : forall Σ Σ' used used' fc fc' (mm m' : mem) D N, nd_ctx Σ used fc mm -> nd_srel Σ' used' -> (0 <= used' <= cr)%Z -> frm0 fc' ->
    rt_after RT Σ' spq lo mm m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq D N mm m' ->
    ((f + 32 <= D /\ D + N <= f + 536) \/ (X <= D /\ D + N <= X + 504))%Z -> nd_ctx Σ' used' fc' m'.
  Proof using TOPH.
    intros Σ Σ' used used' fc fc' mm m' D N (SR & HU & FRM & HA & MR & PK) SR' HU' FRM' (ART' & MI' & WM' & ST') PRX HD.
    split; [exact SR'|]. split; [exact HU'|]. split; [exact FRM'|]. split; [exact ART'|].
    split; [eapply (TKm nd_mrel_ex Σ SR mm m' D N HA MR WM' PRX); destruct HD; [left| right; left]; lia|].
    destruct PK as ((jh & P2) & P3 & (h & P4) & P6 & _).
    top_env Σ SR.
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x /\ ~ (D <= x < D + N)%Z) PRX (fun x H => H)) as AG.
    unfold LM_SAVED in P3.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac| lia]).
    split; [exists jh; exact P2|]. split; [exact P3|]. split; [exists h; exact P4|]. split; [exact P6| exact ST'].
  Qed.
  Lemma nd_ctx_call : forall Σ used fc fc' (mm m' : mem) D N, nd_ctx Σ used fc mm -> frm0 fc' -> rt_after RT Σ spq lo mm m' ->
    rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq D N mm m' ->
    ((f + 32 <= D /\ D + N <= f + 536) \/ (X <= D /\ D + N <= X + 496))%Z -> nd_ctx Σ used fc' m'.
  Proof using TOPH.
    intros Σ used fc fc' mm m' D N CTX FRM' RA PRX HD. pose proof CTX as (SR & HU & _).
    eapply (nd_ctx_call2 Σ Σ used used fc fc' mm m' D N CTX SR HU FRM' RA PRX). lia.
  Qed.

  Lemma nd_k55c : forall Σ used F fc mb, nd_ctx Σ used fc mb -> nd_55c_k sp gp tp F fc X p2 e spq f mb (QΣ Σ).
  Proof using TOPH.
    intros Σ used F fc mb CTX. unfold nd_55c_k. intros until mm. intros XINV.
    destruct XINV as ((jsp & SPILL) & (xbs & XA & XL) & (xlen & XN & LEN) & ZR & _ & MI & MU & WM). unfold nd_W in MU.
    destruct (top_ctx_step Σ used fc mb mm CTX MU WM) as (SR & HU & FRM & ARTm & MRm & PKm). clear CTX MU WM.
    destruct PKm as ((jh & HIGHc) & SAVED & (h & HDR) & SHW & ST).
    top_env Σ SR. pose proof SR as (EF & EL & ES & EC).
    assert (HL : length h = 32%nat) by exact (proj1 (proj1 (proj1 HDR))).
    apply (rw_cells_split_CB bsegs mm f [] 32 h [] [8; 24]%nat) in HDR; [| reflexivity]. cbn [mk_CB_cells app] in HDR.
    eapply (nd_rel1 f mm ltac:(lia) _); [exact HDR | exact MI | apply munch_refl | apply wmono_refl |].
    clear HDR MI. intros mm2 HDR2 MI2 MU2 WM2.
    apply evt_done.
    transport_after_call bsegs mm mm2 MU2 WM2.
    pose proof (top_art Σ used _ mm mm2 SR (TK tk_wf_W1 Σ SR) ARTm MU2 WM2) as ART2.
    pose proof (top_mrel Σ used _ mm mm2 SR (TK tk_wf_W1 Σ SR) ARTm MRm MU2 WM2) as MR2.
    clear HDR2 MU2 WM2.
    eapply (aevt_set_shadow RT RTF PMc FDO MST Σ K 0xf5%Z) with (d := S) (n := 128%Z) (lo := lo);
      [unfold set_shadow_vals; cbn [In]; do 11 right; left; reflexivity | reflexivity | reflexivity | lia
      | intros i Hi; exists f, 4%nat; split; [exact HinF|]; unfold shad, SHB; rewrite FS4; replace (f + 1024)%Z with (f + 128 * 8)%Z by lia; rewrite Z.div_add by lia; lia
      | exact SHW | exact ART2 | exact MI2 | exact (top_cok Σ used mm2 SR ST) | exact FRM |].
    intros v0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m3 FRM' RA PRX _.
    rewrite ?unsigned_lit in RA, PRX by lia. destruct RA as (ART3 & MI3 & WM3 & ST3).
    pose proof (TKm nd_mrel_ex Σ SR mm2 m3 S 128%Z ART2 MR2 WM3 PRX ltac:(right; right; lia)) as MR3.
    pose proof (agree_of_pres_ex _ _ _ _ _ mm2 m3 (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x /\ ~ (S <= x < S + 128)%Z) PRX (fun x H => H)) as AG.
    unfold LM_SAVED in SAVED. clear ST MI2 SHW.
    rt_transport_with mm2 m3 AG WM3 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length, ?XL in Hx; cbv beta; split; [aclient_tac| lia]).

    destruct (af_frame_release RT AF Σ m3 f 4%nat (rt_frames RT Σ0) ART3 EF) as (Σ2 & fl & FLAG & NAC & FL0 & FL1 & LAST & REL).
    rewrite FS4 in LAST. replace (f + 1024 - 8)%Z with (f + 1016)%Z in LAST by lia.
    pose proof (af_sp0_range RT AF Σ m3 ART3) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R. pose proof (top_lor1 Σ used SR) as LOR1. unfold STACK_WIN in LOR1, FL1.
    assert (FLX : (fl < X \/ X + 504 <= fl)%Z).
    { destruct (Z_lt_le_dec fl X) as [H|H]; [left; exact H|]. destruct (Z_lt_le_dec fl (X + 504)) as [H2|H2]; [| right; exact H2].
      exfalso. apply NAC. right; right; right; left. exists g, kg. split; [exact HinG| lia]. }
    assert (FLS : (fl < X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= fl)%Z).
    { destruct (Z_lt_le_dec fl (X / 8 + 2147450880)) as [H|H]; [left; exact H|]. destruct (Z_lt_le_dec fl (X / 8 + 2147450880 + 63)) as [H2|H2]; [| right; exact H2].
      exfalso. apply NAC. right; right; right; right. exists g, kg. split; [exact HinG|]. unfold shad, SHB. Z.div_mod_to_equations. lia. }
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply (nd_rel2 f fl m3 ltac:(lia) ltac:(lia) _); [exact LAST | exact FLAG | exact MI3 | apply munch_refl | apply wmono_refl |].
    clear LAST FLAG MI3. intros mm4 FLAG0 MI4 MU4 WM4.
    destruct (REL mm4 MU4 WM4 FLAG0) as (ART4 & EF4 & EL4 & ES4 & EC4 & EA4 & EM4).
    apply evt_done. apply (aevt_frame_release RT PMc Σ Σ2 K _ EA4 EM4).
    transport_after_call bsegs m3 mm4 MU4 WM4.
    assert (MR4 : MREL mm4).
    { destruct MR3 as [WMa PRa]. split; [exact (wmono_trans bsegs _ _ _ WMa WM4)|]. eapply pres_fp_trans; [exact PRa|].
      apply (pres_fp_of_munch _ _ _ _ [(fl, (fl + 1)%Z)] _ _ MU4). intros a Ha _. cbn [outside]. split; [| exact I]. intros Hfl. apply NAC.
      assert (a = fl) by lia. subst a.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [exfalso; lia | right; left; exact Ha | right; right; left; rewrite EL; exact Ha
        | right; right; right; left; destruct Ha as (f1 & k1 & Hin & Hr); exists f1, k1; split; [rewrite EF; right; exact Hin| exact Hr]
        | right; right; right; right; destruct Ha as (f1 & k1 & Hin & Hr); exists f1, k1; split; [rewrite EF; right; exact Hin| exact Hr]]. }
    apply (aevt_evt RT AF PMc MST).
    eapply (nd_leave ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' lo d spq SPQ ROOM TOP (fun ms' => aevt RT PMc Σ2 K ms'));
      [exact SPILL | exact HIGHc | exact SAVED | exact ST3 |].
    intros zt0 zt1 zt2 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 STF.
    apply evt_done.
    eapply HK; [exact FRM' | | exact (proj2 MR4) | | exact EF4 | rewrite EL4; exact EL | rewrite ES4; exact ES | rewrite EC4; lia].
    - split; [exact ART4|]. split; [exact MI4|]. split; [exact (proj1 MR4)| exact STF].
    - apply (abig_intro RT _ _ X xbs xlen). split; [exact XA|]. split; [exact XL|]. split; [exact XN|]. split; [exact LEN|].
      split; [exact ZR|]. split; [exact X8|]. exists g, kg. rewrite EF4. exact XG.
  Qed.
End NDTOP.
