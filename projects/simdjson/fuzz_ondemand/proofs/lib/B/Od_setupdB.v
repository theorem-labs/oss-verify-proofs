(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjStage1 SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim Stdio SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_num_kit Sj_h_arith Atp_h_defs Od_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsB Od_cpsB Od_hkit0A Od_hkit3A Od_setcapA Od_deldtorA Od_lkitB Od_beginB Od_top_defsB
  Od_exitB Od_tailB Od_errxwB Od_errxB Od_exitpB Od_setup_defsB Od_setup_defs2B Od_setupkB Od_setupw2B Od_setupw4B Od_hand_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma od_sbuf_range' : forall L, 0 <= L <= 1048512 -> 64 <= OD_SBUF L <= 1747648.
Proof. intros L H. unfold OD_SBUF, roundup64. Z.div_mod_to_equations. lia. Qed.

Lemma od_implC_dl : forall (m : mem) IMPL IDX OC IA BUF L nidx p12 p28 p50 docj nxt,
  rw_cells bsegs m IMPL (od_implC IDX OC IA BUF L nidx p12 p28 p50 docj nxt) ->
  exists pre8 mid rest, length pre8 = 8%nat /\ length mid = 32%nat /\ length rest = 24%nat
    /\ rw_cells bsegs m IMPL (dl_cells (wz OD_DPI_VPTR) pre8 (wz IDX) mid (wz OC) (wz IA) rest)
    /\ cells_bytes (dl_cells (wz OD_DPI_VPTR) pre8 (wz IDX) mid (wz OC) (wz IA) rest) = cells_bytes (od_implC IDX OC IA BUF L nidx p12 p28 p50 docj nxt).
Proof.
  intros until nxt. intros H. pose proof H as [[WF _] _]. unfold od_implC in WF. cbn [cells_wf cell_wf] in WF.
  destruct WF as (_ & _ & L12 & _ & _ & L44 & _ & _ & L8 & _).
  unfold mid16 in L44. rewrite !length_app in L44. cbn [length] in L44. rewrite !length_le8 in L44.
  exists (le4 (wz nidx) ++ p12), (le4 nxt ++ p28 ++ le8 (wz L) ++ le8 (wz 1024) ++ [Z_to_bv 8 0] ++ [Z_to_bv 8 0] ++ p50), (le8 (wz BUF) ++ le8 (wz L) ++ docj).
  assert (E1 : length (le4 (wz nidx) ++ p12) = 8%nat) by (rewrite length_app, length_le4; lia).
  assert (E2 : length (le4 nxt ++ p28 ++ le8 (wz L) ++ le8 (wz 1024) ++ [Z_to_bv 8 0] ++ [Z_to_bv 8 0] ++ p50) = 32%nat)
    by (rewrite !length_app; cbn [length]; rewrite length_le4, !length_le8; lia).
  assert (E3 : length (le8 (wz BUF) ++ le8 (wz L) ++ docj) = 24%nat) by (rewrite !length_app, !length_le8; lia).
  assert (EB : cells_bytes (dl_cells (wz OD_DPI_VPTR) (le4 (wz nidx) ++ p12) (wz IDX)
                              (le4 nxt ++ p28 ++ le8 (wz L) ++ le8 (wz 1024) ++ [Z_to_bv 8 0] ++ [Z_to_bv 8 0] ++ p50) (wz OC) (wz IA) (le8 (wz BUF) ++ le8 (wz L) ++ docj))
               = cells_bytes (od_implC IDX OC IA BUF L nidx p12 p28 p50 docj nxt)).
  { unfold dl_cells, od_implC, mid16. cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity. }
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact EB].
  apply (rw_cells_recell bsegs m IMPL _ _ H); [unfold dl_cells; cbn [cells_wf cell_wf]; repeat split; assumption| exact EB| reflexivity].
Qed.

Lemma od_lowB_xe : forall (m : mem) S1 F act fl COPY j0 j144 j176 j264 j288 j336 j376 j384 j432,
  rw_cells bsegs m S1 (od_lowB F act fl COPY j0 j144 j176 j264 j288 j336 j376) ->
  rw_cells bsegs m (S1 + 384) [CB 48 j384; CB 8 j432] ->
  rw_cells bsegs m S1 (xe_locals F (wz fl) (wz COPY) (wz (F + 200)) j0 j144 j176
                         (le8 (wz act) ++ j264 ++ le8 (wz (F + 224)) ++ j288 ++ le8 (wz (F + 208)) ++ j336) (j376 ++ j384) j432).
Proof.
  intros until j432. intros LO HI.
  pose proof LO as [[WF _] _]. unfold od_lowB in WF. cbn [cells_wf cell_wf] in WF.
  destruct WF as (L0 & _ & _ & _ & _ & L144 & _ & L176 & _ & _ & L264 & _ & L288 & _ & L336 & _ & L376 & _).
  pose proof HI as [[WF2 _] _]. cbn [cells_wf cell_wf] in WF2. destruct WF2 as (L384 & L432 & _).
  assert (J : rw_cells bsegs m S1 (od_lowB F act fl COPY j0 j144 j176 j264 j288 j336 j376 ++ [CB 48 j384; CB 8 j432])).
  { apply Sj_stage1_kit.rw_cells_app. split; [exact LO|]. unfold od_lowB. cbn [cells_size csize Nat.add]. exact HI. }
  apply (rw_cells_recell bsegs m S1 _ _ J).
  - unfold xe_locals. cbn [cells_wf cell_wf]. rewrite !length_app, !length_le8. repeat split; try assumption; lia.
  - unfold xe_locals, od_lowB, wz. cbn [cells_bytes cbytes app]. rewrite <- !app_assoc. reflexivity.
  - reflexivity.
Qed.

Section PhaseC2.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis DTOR : deldtor_cps RT.
Hypothesis VDES : vdestroy_cpsA RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Local Ltac ul := unfold FUZZ_STACK, OD_NEED in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma od_errx_of_cutC : forall (K : config -> Prop) (Σ0 ΣC : rts RT) (m0 mC : mem) (usp S1 F lo : Z) (dz : list Z)
    (A cap size COPY BUF SB IMPL IDX OC IA code : Z) (out : list Z) (els : list (Z * Z))
    (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs8 xs9 xt3 xt4 xt5 xt6 : word) xF xfc,
  od_cutC RT LIB Σ0 ΣC m0 mC usp S1 F lo dz A cap size COPY BUF SB IMPL IDX OC IA code out els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  0 < code < 64 -> frm0 xfc ->
  od_fin_k RT LIB PMc K Σ0 usp lo cra gp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 (rt_credit RT Σ0 - FUZZ_COST) ->
  aevt ΣC K (ex_regs Od_errxwB.OD_ERRX xra S1 gp (wz 0x656e70) xt0 xt1 xt2 usp xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz code) xs3 F xs5 xs6 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mC).
Proof using AF LIB_loc FDO MST RTF DELA DTOR VDES AFV.
  intros until xfc. intros CC CODER FRM KF.
  destruct CC as [C0 DZ LV CPY CHK CR (j0 & j144 & j176 & j264 & j288 & j336 & j376 & LOWF) (jp & PAR) SH WSB CODE (p12 & p28 & p50 & docj & nxt & IMC) IDXA].
  destruct C0 as [(U16 & UT) (S32 & S1R) (LOW & LOR) (F64 & FPOS) FRS0 LVPOS LVB CR0 ART0 MI0 ST0 FRS SP0 (j384 & j432 & HI) PAD SAVED (h0 & h8 & HDR)
                  VR SZ1 WRS (jd & DOC) LIB0 CP0].
  destruct (od_implC_dl mC IMPL IDX OC IA BUF _ _ p12 p28 p50 docj nxt IMC) as (pre8 & mid & rest & _ & _ & _ & DL & _).
  destruct CHK as ((SBPOS & SB16) & (IMPOS & IM16) & _).
  pose proof (sc_idx_bounds (zlength (od_doc dz))) as IXB.
  assert (LR : 0 <= zlength (od_doc dz) <= 1048512).
  { unfold od_doc, od_copied in *. destruct (zlength (od_s0 dz) <=? SJ_PADMAX) eqn:E; [| unfold zlength; cbn; lia].
    apply Z.leb_le in E. unfold SJ_PADMAX in E. destruct CPY as (_ & _ & X1 & X2 & _). unfold zlength in *. lia. }
  pose proof (od_sbuf_range' (zlength (od_doc dz)) LR) as SBR.
  pose proof (od_lowB_xe mC S1 F _ _ COPY _ _ _ _ _ _ _ _ _ LOWF HI) as XL.
  unfold od_parserC in PAR.
  pose proof (rw_cells_pick 2 1 mC _ (F + 104) _ PAR ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as PIM.
  pose proof (rw_cells_pick 7 1 mC _ (F + 144) _ PAR ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as PSB.
  pose proof (rw_cells_pick 0 1 mC _ F _ HDR ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as FH.
  unfold od_shadow in SH. cbn [map] in SH.
  pose proof (rw_cells_pick 4 3 mC _ (F / 8 + 2147450880 + 4) _ SH ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as SHv.
  pose proof (rw_cells_pick 12 7 mC _ (F / 8 + 2147450880 + 12) _ SH ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as SHp.
  pose proof (rw_cells_pick 24 8 mC _ (F / 8 + 2147450880 + 24) _ SH ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as SHD.
  cbn [firstn skipn] in PIM, PSB, FH, SHv, SHp, SHD.
  destruct VR as (VSZ & VSC & VREST).
  assert (CAP1 : 1 <= cap) by (clear - VSC SZ1; lia).
  assert (VRF : vrepA mC (F + 32) A cap size els) by (exact (conj VSZ (conj VSC VREST))).
  assert (RK : od_ret_k RT PMc K usp lo cra gp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 (rt_live RT Σ0) (rt_sp0 RT ΣC) (rt_credit RT ΣC) mC).
  { eapply (od_ret_k_of_fin RT LIB LIB_loc PMc); [exact KF| exact CP0| exact LIB0| exact SP0|].
    pose proof (mcost_le (OD_SBUF (zlength (od_doc dz))) ltac:(lia)) as M1. pose proof (mcost_le (sc_idx (zlength (od_doc dz))) ltac:(lia)) as M2.
    assert (IXU : sc_idx (zlength (od_doc dz)) <= 4194340) by (clear - LR; unfold sc_idx, roundup64; Z.div_mod_to_equations; lia).
    assert (MC96 : mcost 96 = 2097152) by (vm_compute; reflexivity).
    assert (MC8K : mcost 8192 = 2097152) by (vm_compute; reflexivity).
    assert (MC1K : mcost 1024 = 2097152) by (vm_compute; reflexivity).
    assert (PADC : OD_PAD_COST = 4210688) by (vm_compute; reflexivity).
    rewrite MC96, MC8K, MC1K, PADC in CR. unfold OD_VEC_COST, FUZZ_COST in *. clear - CR M1 M2 SBR IXU. lia. }
  refine (od_errx_core RT AF PMc FDO MST RTF DELA DTOR VDES AFV ΣC K usp S1 F lo IMPL IDX OC IA (sc_idx (zlength (od_doc dz))) SB (OD_SBUF (zlength (od_doc dz)))
            COPY (zlength (od_s0 dz) + 64) A cap size code (if od_copied dz then 0 else 1) els (rt_live RT Σ0)
            (if od_copied dz then [(COPY, zlength (od_s0 dz) + 64)] else [])
            cra gp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
            xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs8 xs9 xt3 xt4 xt5 xt6 (wz COPY) (wz (F + 200)) xF xfc mC
            _ _ _ _ _ _ h0 jd pre8 mid rest
            S32 S1R U16 UT _ _ FRM ART0 MI0 ST0 FRS LV _ _ _ LVPOS _ XL PAD SAVED FH PIM PSB DOC VRF CAP1 SZ1 WRS SHv SHp SHD DL CODER RK).
  - rewrite SP0. exact LOW.
  - clear - LOR S1R. ul.
  - clear - CPY. destruct (od_copied dz); [left; split; [reflexivity|]; split; [unfold zlength; lia|]; split; reflexivity| right; split; [reflexivity| lia]].
  - clear - IXB LR. lia.
  - clear - SBR. lia.
  - clear - IM16. Z.div_mod_to_equations. lia.
Qed.

Hypothesis HANDOVER : od_handover_stmt RT LIB PMc.

Theorem od_phaseC2 : od_phaseC2_stmt RT LIB PMc.
Proof using AF LIB_loc FDO MST RTF DELA DTOR VDES AFV HANDOVER.
  intros K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 _ _ KI KF.
  unfold od_cutC_k.
  intros ΣC S1 F A cap size COPY BUF SB IMPL IDX OC IA code out els xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc mC FRM CC.
  assert (CODER : 0 <= code < 64).
  { destruct (cc_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CC) as [(_ & E)|(_ & E & _)]; [| lia].
    pose proof (stage1_code_range (od_doc dz)) as X. rewrite <- E in X. exact X. }
  destruct (Z.eq_dec code 0) as [C0|CNZ].
  -
    subst code. apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [exact (od_walkC5s _ usp S1 F gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc mC)|].
    cbv beta. intros ms <-. apply evt_done. unfold lh_regs.
    exact (HANDOVER K Σ0 ΣC m0 mC usp S1 F lo dz A cap size COPY BUF SB IMPL IDX OC IA out els gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc CC FRM KI).
  -
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [exact (od_walkC5e _ usp S1 F code gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc mC ltac:(lia))|].
    cbv beta. intros ms <-. apply evt_done.
    exact (od_errx_of_cutC K Σ0 ΣC m0 mC usp S1 F lo dz A cap size COPY BUF SB IMPL IDX OC IA code out els gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc CC ltac:(lia) FRM KF).
Qed.
End PhaseC2.
