(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lits
  Sj_num_lm_pro Sj_num_lm_enter Sj_num_lm_kit Sj_num_lm_defs Sj_num_lm_a Sj_num_lm_b Sj_num_lm_c3 Sj_num_lm_leave Sj_num_lm_tkit.
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

Section LMTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.

  Variables (Σ0 Σ1 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo d spq f g len0 : Z) (kg : nat) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation Y := B_P5LARGE.
  Hypothesis ETP : tp = Z_to_bv 64 B_TP.
  Hypothesis ROOM : (lo + LMB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis EF : rt_frames RT Σ1 = (f, 5%nat) :: rt_frames RT Σ0.
  Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ0.
  Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ0.
  Hypothesis EC : rt_credit RT Σ1 = (rt_credit RT Σ0 - 1)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 224 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x6ce000 <= f /\ f + 2040 <= lo /\ (f + 2040 <= S \/ S + 255 <= f) /\ 0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XG : In (g, kg) (rt_frames RT Σ0) /\ (g <= X)%Z /\ (X + 504 <= g + fs_size kg - 8)%Z.
  Hypothesis XNUM : (0x6ce000 <= X /\ X + 504 <= lo /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
                    /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
                    /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.
  Hypothesis L0 : (0 <= len0 <= 62)%Z.

  Hypothesis HK : big_k RT PMc Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 me X lo 1 (lmb_G len0).
  Collection TOPH := AF RTF FDO MST ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP L0 HK.

  Notation Q := (fun ms' => aevt RT PMc Σ1 K ms').
  Notation MREL := (lm_mrel RT Σ0 sp X me).
  Notation PARK := (lm_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d spq f).
  Notation TKA := (RT AF Σ0 Σ1 sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP) (only parsing).

  Definition lm_ctx (fc : bv 32) (mb : mem) : Prop := frm0 fc /\ ART RT Σ1 mb /\ MREL mb /\ PARK mb.

  Lemma top_spq : (0 <= d <= 16 /\ spq = SP - 224 - d)%Z.
  Proof using TOPH. destruct SPQ as [[->| ->] ->]; lia. Qed.
  Lemma top_lor1 : (rt_sp0 RT Σ1 - STACK_WIN <= lo)%Z.
  Proof using TOPH. rewrite ES. exact LOR. Qed.
  Lemma top_inF : In (f, 5%nat) (rt_frames RT Σ1).
  Proof using TOPH. rewrite EF. left. reflexivity. Qed.
  Lemma top_inG : In (g, kg) (rt_frames RT Σ1).
  Proof using TOPH. rewrite EF. right. exact (proj1 XG). Qed.
  Lemma top_fpok : forall W, tk_wf sp X lo f W -> fp_ok RT Σ1 lo W.
  Proof using TOPH. exact (tk_fpok RT AF Σ0 Σ1 sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP). Qed.
  Lemma top_wfWL : tk_wf sp X lo f (lm_WL X spq f).
  Proof using TOPH. exact (tk_wf_WL RT AF Σ0 Σ1 sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP). Qed.
  Lemma top_wfW3 : tk_wf sp X lo f [(f, f + 8); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z.
  Proof using TOPH. exact (tk_wf_W3 RT AF Σ0 Σ1 sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP). Qed.
  Lemma top_wfWA : tk_wf sp X lo f [(spq, spq + 120); (f + 528, f + 530); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z.
  Proof using TOPH. exact (tk_wf_WA RT AF Σ0 Σ1 sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP). Qed.
  Lemma top_art : forall W (mb mm : mem), tk_wf sp X lo f W -> ART RT Σ1 mb -> munch W mb mm -> wmono bsegs mb mm -> ART RT Σ1 mm.
  Proof using TOPH. intros W mb mm HW HA MU WM. exact (art_of_munch RT AF Σ1 mb mm lo W HA top_lor1 (top_fpok W HW) MU WM). Qed.
  Lemma top_mrel : forall W (mb mm : mem), tk_wf sp X lo f W -> ART RT Σ1 mb -> MREL mb -> munch W mb mm -> wmono bsegs mb mm -> MREL mm.
  Proof using TOPH. exact (lm_mrel_munch RT AF Σ0 Σ1 sp X lo d spq f g kg me ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP). Qed.
  Lemma top_park : forall (mb mm : mem), PARK mb -> munch (lm_WL X spq f) mb mm -> wmono bsegs mb mm -> PARK mm.
  Proof using TOPH.
    intros mb mm. apply (lm_park_munch RT AF Σ0 Σ1 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP).
    exact (tk_wfp_WL RT AF Σ0 Σ1 sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP).
  Qed.

  Lemma top_ctx_step : forall fc (mb mm : mem), lm_ctx fc mb -> munch (lm_WL X spq f) mb mm -> wmono bsegs mb mm -> lm_ctx fc mm.
  Proof using TOPH.
    intros fc mb mm (FRM & HA & MR & PK) MU WM. split; [exact FRM|]. split; [exact (top_art _ mb mm top_wfWL HA MU WM)|].
    split; [exact (top_mrel _ mb mm top_wfWL HA MR MU WM)| exact (top_park mb mm PK MU WM)].
  Qed.
  Lemma top_cok : forall (mm : mem), stk bsegs mm lo spq -> call_ok RT Σ1 mm (Z_to_bv 64 spq) lo.
  Proof using TOPH.
    intros mm ST. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (stk_lo_nonneg bsegs _ _ _ ST) as LO0. destruct SPQ as [Hd Hs]. unfold LMB_STACK, RT_STACK, USTACK_TOP in *.
    unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST|]. split; [exact top_lor1|]. unfold RT_STACK, USTACK_TOP.
    split; [lia|]. split; [lia| Z.div_mod_to_equations; lia].
  Qed.

  Ltac top_env :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof XNUM as (Q1 & Q2 & Q3 & Q4 & Q5); pose proof SEP as (E1 & E2 & E3 & E4);
    pose proof top_spq as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof top_inF as HinF; pose proof (f64_8 f (proj1 NF)) as F8; pose proof (eq_refl : fs_size 5 = 2048%Z) as FS5;
    pose proof (proj1 XG) as HinG0; pose proof (proj1 (proj2 XG)) as G1; pose proof (proj2 (proj2 XG)) as G2;
    assert (HinG : In (g, kg) (rt_frames RT Σ1)) by (rewrite EF; right; exact HinG0);
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL; pose proof L0 as L0'.

  Lemma lm_kexit : forall F fc mb, lm_ctx fc mb -> lm_exit_k sp gp tp F fc X lo spq f len0 mb Q.
  Proof using TOPH.
    intros F fc mb CTX. unfold lm_exit_k. intros until mm. intros XINV HR.
    destruct XINV as ((ja & jb & SPILL) & (bs & XA & XL & NB) & XN & LEN & ZR & (zsh & ZSH) & MI & MU & WM & ST).
    destruct (top_ctx_step fc mb mm CTX MU WM) as (FRM & ARTm & MRm & PKm). clear CTX MU WM.
    destruct PKm as ((jh & HIGHc) & SAVED & (h & HDR) & _ & ZZC).
    top_env.
    assert (HL : length h = 32%nat) by exact (proj1 (proj1 (proj1 HDR))).
    apply (rw_cells_split_CB bsegs mm f [] 32 h [] [8; 24]%nat) in HDR; [| reflexivity]. cbn [mk_CB_cells app] in HDR.
    eapply (lm_leave1 sp gp tp F fc X lo d spq f mm SPQ ROOM TOP N1 (conj N2 N3) N4 (conj N5 N6) Q (Z_to_bv 64 r));
      [| exact SPILL | exact HDR | exact ZZC | exact MI | apply munch_refl | apply wmono_refl].

    unfold lm_free_k. clear HDR ZZC MI.
    intros yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 ys6 ys9 ys10 ys11 yt3 yt4 yt5 yt6 h' jz' mm2 HDR2 SHZ2 MI2 MU2 WM2.
    apply evt_done.
    transport_after_call bsegs mm mm2 MU2 WM2.
    pose proof (top_art _ mm mm2 top_wfW3 ARTm MU2 WM2) as ART2.
    pose proof (top_mrel _ mm mm2 top_wfW3 ARTm MRm MU2 WM2) as MR2.
    clear HDR2 SHZ2 MU2 WM2.
    eapply (aevt_stack_free5 RT RTF PMc FDO MST Σ1 K) with (f := f) (fr := rt_frames RT Σ0) (lo := lo);
      [reflexivity | exact ETP | exact EF | exact ART2 | exact MI2 | exact (top_cok mm2 ST) | exact FRM |].
    intros Σ2 v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' FRM' RA PR EF2 EL2 ES2 EC2.
    rewrite ?unsigned_lit in RA, PR by lia. destruct RA as (ART' & MI' & WM' & ST').
    pose proof (agree_pres _ _ _ mm2 m' (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ0) spq x) PR (fun x H => H)) as AG.
    unfold LM_SAVED in SAVED.
    clear ST.
    rt_transport_with mm2 m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length, ?XL in Hx; cbv beta; aclient_tac).
    pose proof (lm_mrel_free RT AF Σ0 Σ1 sp X lo d spq f g kg me ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP mm2 m' MR2 WM' PR) as MR'.
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply (lm_leave2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' lo d spq SPQ ROOM TOP (fun ms' => aevt RT PMc Σ2 K ms'));
      [exact SPILL | reflexivity | exact HIGHc | exact SAVED | exact ST' |].
    intros zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 STF.
    apply evt_done.
    eapply (HK Σ2) with (bs' := bs) (len' := len); [exact FRM' | | exact (proj2 MR') | | | rewrite EF2; reflexivity | rewrite EL2; exact EL | rewrite ES2; exact ES | rewrite EC2, EC; lia].
    - split; [exact ART'|]. split; [exact MI'|]. split; [exact (proj1 MR')| exact STF].
    - pose proof (abig_intro RT Σ2 m' X bs len) as AI. unfold abig_raw in AI.
      assert (AB : abig RT Σ2 m' X).
      { apply AI. split; [exact XA|]. split; [exact XL|]. split; [exact XN|]. split; [exact LEN|]. split; [exact ZR|]. split; [exact X8|].
        exists g, kg. rewrite EF2. split; [exact HinG0| split; [exact G1| exact G2]]. }
      destruct AB as (FO & _ & _). split; [exact FO|]. split; [exact XL|]. split; [exact XA|]. split; [exact XN| exact LEN].
    - unfold lmb_G. intros HC. destruct (HR HC) as (HP & -> & HL6). split; [reflexivity|]. split; [exact (NB HP)| exact HL6].
  Qed.
End LMTOP.
