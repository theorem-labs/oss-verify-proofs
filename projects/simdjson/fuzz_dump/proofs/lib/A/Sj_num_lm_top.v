(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lm_pro Sj_num_lm_enter Sj_num_lm_leave
  Sj_num_lm_kit Sj_num_lm_defs Sj_num_lm_tkit Sj_num_lm_a Sj_num_lm_b Sj_num_lm_c1 Sj_num_lm_c2 Sj_num_lm_c3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section LMTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis NLA : num_lits_acc RT.

  Variables (Σ0 Σ1 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo d spq f g : Z) (kg : nat) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation Y := 0x2b3e0%Z.
  Hypothesis ETP : tp = Z_to_bv 64 0x69ec68.
  Hypothesis ROOM : (lo + LMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis EF : rt_frames RT Σ1 = (f, 5%nat) :: rt_frames RT Σ0.
  Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ0.
  Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ0.
  Hypothesis EC : rt_credit RT Σ1 = (rt_credit RT Σ0 - 1)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 256 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x6c1000 <= f /\ f + 2040 <= lo /\ (f + 2040 <= S \/ S + 255 <= f) /\ 0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XG : In (g, kg) (rt_frames RT Σ0) /\ (g <= X)%Z /\ (X + 504 <= g + fs_size kg - 8)%Z.
  Hypothesis XNUM : (0x6c1000 <= X /\ X + 504 <= lo /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
                    /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
                    /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.

  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)%Z] me m' ->
     abig RT Σ' m' X ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - 1 <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs)).
  Collection TOPH := AF RTF FDO MST NLA ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP HK.

  Notation Q := (fun ms' => aevt RT PMc Σ1 K ms').
  Notation MREL := (lm_mrel RT Σ0 sp X me).
  Notation PARK := (lm_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo d spq f).

  Definition lm_ctx (fc : bv 32) (mb : mem) : Prop := frm0 fc /\ ART RT Σ1 mb /\ MREL mb /\ PARK mb.

  Lemma top_spq : (0 <= d <= 16 /\ spq = SP - 256 - d)%Z.
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
  Lemma top_wfWA : tk_wf sp X lo f [(spq + 16, spq + 152); (f + 528, f + 530); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z.
  Proof using TOPH. exact (tk_wf_WA RT AF Σ0 Σ1 sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP). Qed.
  Lemma top_art : forall W (mb mm : mem), tk_wf sp X lo f W -> ART RT Σ1 mb -> munch W mb mm -> wmono asegs mb mm -> ART RT Σ1 mm.
  Proof using TOPH. intros W mb mm HW HA MU WM. exact (art_of_munch RT AF Σ1 mb mm lo W HA top_lor1 (top_fpok W HW) MU WM). Qed.
  Lemma top_mrel : forall W (mb mm : mem), tk_wf sp X lo f W -> ART RT Σ1 mb -> MREL mb -> munch W mb mm -> wmono asegs mb mm -> MREL mm.
  Proof using TOPH. exact (lm_mrel_munch RT AF Σ0 Σ1 sp X lo d spq f g kg me ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP). Qed.
  Lemma top_park : forall (mb mm : mem), PARK mb -> munch (lm_WL X spq f) mb mm -> wmono asegs mb mm -> PARK mm.
  Proof using TOPH.
    intros mb mm. apply (lm_park_munch RT AF Σ0 Σ1 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP).
    exact (tk_wfp_WL RT AF Σ0 Σ1 sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP).
  Qed.

  Lemma top_ctx_step : forall fc (mb mm : mem), lm_ctx fc mb -> munch (lm_WL X spq f) mb mm -> wmono asegs mb mm -> lm_ctx fc mm.
  Proof using TOPH.
    intros fc mb mm (FRM & HA & MR & PK) MU WM. split; [exact FRM|]. split; [exact (top_art _ mb mm top_wfWL HA MU WM)|].
    split; [exact (top_mrel _ mb mm top_wfWL HA MR MU WM)| exact (top_park mb mm PK MU WM)].
  Qed.
  Lemma top_cok : forall (mm : mem), stk asegs mm lo spq -> call_ok RT Σ1 mm (Z_to_bv 64 spq) lo.
  Proof using TOPH.
    intros mm ST. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (stk_lo_nonneg asegs _ _ _ ST) as LO0. destruct SPQ as [Hd Hs]. unfold LMA_STACK, RT_STACK, USTACK_TOP in *.
    unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST|]. split; [exact top_lor1|]. unfold RT_STACK, USTACK_TOP.
    split; [lia|]. split; [lia| Z.div_mod_to_equations; lia].
  Qed.

  Lemma lm_kexit : forall F fc mb, lm_ctx fc mb -> lm_exit_k sp gp tp F fc X spq f mb Q.
  Proof using TOPH.
    intros F fc mb CTX. unfold lm_exit_k. intros until mm. intros XINV.
    destruct XINV as ((ja0 & ja1 & SPILL) & (xbs & XA & XL) & (xlen & XN & LEN) & ZR & MI & MU & WM).
    destruct (top_ctx_step fc mb mm CTX MU WM) as (FRM & ARTm & MRm & PKm). clear CTX MU WM.
    destruct PKm as ((jl & LOWc) & (jh & HIGHc) & SAVED & (h & HDR) & _ & ZZC & ST).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6). pose proof XNUM as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof SEP as (E1 & E2 & E3 & E4).
    pose proof SPQ as [Hd Hs]. pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    assert (HL : length h = 32%nat) by exact (proj1 (proj1 (proj1 HDR))).
    apply (rw_cells_split_CB asegs mm f [] 32 h [] [8; 24]%nat) in HDR; [| reflexivity]. cbn [mk_CB_cells app] in HDR.
    rewrite (firstn_all2 (n := 24) (skipn 8 h)) in HDR by (rewrite length_skipn; lia).
    apply (rw_cells_split_CB asegs mm _ [] 63 _ [] (repeat 1%nat 63)) in ZZC; [| reflexivity]. cbn [app] in ZZC. rewrite app_nil_r in ZZC.
    eapply (lm_leave1 sp gp tp _ _ _ _ _ _ _ _ F fc lo d spq f mm SPQ ROOM TOP N1 (conj N2 N3) N4 (conj N5 N6) Q);
      [| exact SPILL | exact HDR | exact ZZC | exact MI | apply munch_refl | apply wmono_refl].

    unfold lm_free_k. clear HDR ZZC MI.
    intros yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 ys3 res yt3 yt4 yt5 yt6 h' jz' mm2 HDR2 SHZ2 MI2 MU2 WM2.
    apply evt_done.
    transport_after_call asegs mm mm2 MU2 WM2.
    pose proof (top_art _ mm mm2 top_wfW3 ARTm MU2 WM2) as ART2.
    pose proof (top_mrel _ mm mm2 top_wfW3 ARTm MRm MU2 WM2) as MR2.
    clear HDR2 SHZ2 MU2 WM2.
    eapply (aevt_stack_free5 RT RTF PMc FDO MST Σ1 K) with (f := f) (fr := rt_frames RT Σ0) (lo := lo);
      [reflexivity | exact ETP | exact EF | exact ART2 | exact MI2 | exact (top_cok mm2 ST) | exact FRM |].
    intros Σ2 v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' FRM' RA PR EF2 EL2 ES2 EC2.
    rewrite ?unsigned_lit in RA, PR by lia. destruct RA as (ART' & MI' & WM' & ST').
    pose proof (agree_pres _ _ _ mm2 m' (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ0) spq x) PR (fun x H => H)) as AG.
    pose proof (proj1 XG) as HinG. destruct XG as (_ & G1 & G2).
    unfold LM_SAVED in SAVED.
    clear ST.
    rt_transport_with mm2 m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length, ?XL in Hx; cbv beta; aclient_tac).
    pose proof (lm_mrel_free RT AF Σ0 Σ1 sp X lo d spq f g kg me ROOM TOP LOR EF EL ES SPQ NF X8 (conj HinG (conj G1 G2)) XNUM SEP mm2 m' MR2 WM' PR) as MR'.
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply (lm_leave2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' lo d spq SPQ ROOM TOP (fun ms' => aevt RT PMc Σ2 K ms'));
      [exact LOWc | exact SPILL | reflexivity | exact HIGHc | exact SAVED | exact ST' |].
    intros zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 STF.
    apply evt_done.
    eapply HK; [exact FRM' | | exact (proj2 MR') | | rewrite EF2; reflexivity | rewrite EL2; exact EL | rewrite ES2; exact ES | rewrite EC2, EC; lia].
    - split; [exact ART'|]. split; [exact MI'|]. split; [exact (proj1 MR')| exact STF].
    - apply (abig_intro RT _ _ X xbs xlen). split; [exact XA|]. split; [exact XL|]. split; [exact XN|]. split; [exact LEN|].
      split; [exact ZR|]. split; [exact X8|]. exists g, kg. rewrite EF2. split; [exact HinG| split; [exact G1| exact G2]].
  Qed.

  Lemma top_f8 : (f mod 8 = 0)%Z.
  Proof using TOPH. exact (f64_8 f (proj1 NF)). Qed.
  Lemma top_yr : (0 <= Y /\ Y + 40 <= 0x6c1000 /\ Y mod 8 = 0)%Z.
  Proof using TOPH. split; [lia|]. split; [lia| reflexivity]. Qed.
  Lemma top_shpy : forall mb, ART RT Σ1 mb -> forall m', munch (lm_WL X spq f) mb m' -> wmono asegs mb m' -> shz m' Y 40.
  Proof using TOPH.
    intros mb HA m' MU WM.
    pose proof (shzp_lits RT AF Σ1 mb lo (lm_WL X spq f) Y 640 NLA HA top_lor1 (top_fpok _ top_wfWL) ltac:(right; left; reflexivity) m' MU WM) as H.
    eapply shz_sub; [exact H| lia| lia].
  Qed.
  Notation EVA L F fc ybs YL mb := (L sp gp tp F fc X lo d spq f Y ybs mb top_spq ROOM TOP (proj1 NF) (conj (proj1 (proj2 NF)) (proj1 (proj2 (proj2 NF))))
                               (proj1 (proj2 (proj2 (proj2 NF)))) (proj2 (proj2 (proj2 (proj2 NF)))) X8
                               (conj (proj1 XNUM) (proj1 (proj2 XNUM))) (proj1 (proj2 (proj2 XNUM))) (proj2 (proj2 (proj2 XNUM))) SEP top_yr YL) (only parsing).

  Lemma lm_inv_rebase : forall ybs m0 ziw zsh mm xlen zlen, lm_inv X spq f Y ybs m0 ziw zsh mm xlen zlen -> lm_inv X spq f Y ybs mm ziw zsh mm xlen zlen.
  Proof using TOPH.
    intros ybs m0 ziw zsh mm xlen zlen (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & _ & _).
    repeat (split; [assumption|]). split; [apply munch_refl| apply wmono_refl].
  Qed.

  Lemma lm_ctx_call : forall fc fc' (mm m' : mem) D N, lm_ctx fc mm -> frm0 fc' -> rt_after RT Σ1 spq lo mm m' ->
    rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) spq D N mm m' ->
    ((f + 608 <= D /\ D + N <= f + 1104) \/ (X <= D /\ D + N <= X + 496))%Z -> lm_ctx fc' m'.
  Proof using TOPH.
    intros fc fc' mm m' D N (FRM & HA & MR & PK) FRM' (ART' & MI' & WM' & ST') PR HD.
    split; [exact FRM'|]. split; [exact ART'|].
    split; [eapply (lm_mrel_ex RT AF Σ0 Σ1 sp X lo d spq f g kg me ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP mm m' D N HA MR WM' PR); lia|].
    destruct PK as ((jl & P1) & (jh & P2) & P3 & (h & P4) & (zbs & P5 & L5) & P6 & _).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6). pose proof XNUM as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof SEP as (E1 & E2 & E3 & E4).
    pose proof SPQ as [Hd Hs]. pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
    assert (Hd' : (0 <= d <= 16)%Z) by lia. clear Hd.
    pose proof top_inF as HinF. pose proof top_f8 as F8. pose proof (eq_refl : fs_size 5 = 2048%Z) as FS5.
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) spq x /\ ~ (D <= x < D + N)%Z) PR (fun x H => H)) as AG.
    unfold LM_SAVED in P3.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length, ?L5 in Hx; cbv beta; split; [aclient_tac| lia]).
    split; [exists jl; exact P1|]. split; [exists jh; exact P2|]. split; [exact P3|]. split; [exists h; exact P4|].
    split; [exists zbs; split; [exact P5| exact L5]|]. split; [exact P6| exact ST'].
  Qed.
End LMTOP.
