(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim Stdio SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_num_kit Sj_h_arith Atp_h_defs Od_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsA Od_cpsA Od_hkit0A Od_hkit3A Od_setcapA Od_deldtorA Od_lkitA Od_beginA Od_topA
  Od_setup_defsA Od_setup_defs2A Od_setupkA Od_setupdA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Hand.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable PMc : Model -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Hypothesis AFG : forall Σ m, ART RT Σ m -> ro_cells asegs m OD_GOT_TABS od_got_cells.
Local Ltac ul := unfold FUZZ_STACK, OD_NEED in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem od_handover : od_handover_stmt RT LIB PMc.
Proof using AF AFV AFG.
  intros K Σ0 ΣC m0 mC usp S1 F lo dz A cap size COPY BUF SB IMPL IDX OC IA out els gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
    xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc CC FRM KI.
  destruct CC as [C0 DZ LV CPY CHK CR (j0 & j192 & j224 & j248 & LOWF) (jp & PAR) SH WSB CODE (p12 & p28 & p50 & docj & nxt & IMC) (ws & UIX & LWS & FWS)].
  destruct C0 as [(U16 & UT) (S32 & S1R) (LOW & LOR) (F64 & FPOS) FRS0 LVPOS LVB CR0 ART0 MI0 ST0 FRS SP0 HIX STp SAVED (h0 & h8 & HDR)
                  VR SZ1 WRS DOCX LIB0 CP0].
  destruct CHK as ((SBPOS & SB16) & (IMPOS & IM16) & (IXPOS & IX16) & (OCPOS & OC16) & (IAPOS & IA16)).

  destruct CODE as [(ECP & EST)|(_ & E13 & _)]; [| discriminate E13].
  rewrite ECP in LV, CPY. destruct CPY as (CPOS & C16 & CBR & CBL & BUFB).
  set (doc := od_doc dz) in *. set (L := zlength doc) in *. set (len0 := zlength (od_s0 dz)) in *.
  assert (DOCOK : bytes_ok doc).
  { subst doc. unfold od_doc. rewrite ECP. pose proof (od_s0_ok dz (proj1 DZ)) as S0OK.
    destruct (Z_lt_ge_dec (zlength (od_s0 dz)) 3) as [L3|L3]; [rewrite strip_bom_short by (unfold zlength in L3; lia); exact S0OK|].
    destruct (strip_bom_cases _ S0OK ltac:(unfold zlength in L3; lia)) as [(_ & E & _)|(_ & E)]; rewrite E; [| exact S0OK].
    unfold bytes_ok in *. rewrite <- (firstn_skipn 3 (od_s0 dz)) in S0OK. apply Forall_app in S0OK. exact (proj2 S0OK). }
  assert (LR : 0 <= L <= 1048512).
  { pose proof (eq_refl (od_copied dz)) as X. rewrite ECP in X at 1. unfold od_copied in X. symmetry in X. apply Z.leb_le in X. unfold SJ_PADMAX in X. fold len0 in X.
    assert (0 <= L) by (subst L; unfold zlength; clear; lia). clear - X CBL CBR H. lia. }
  pose proof (stage1_S1OUT doc out (eq_sym EST)) as S1O.
  pose proof (S1OUT_length_le doc out S1O) as NLE. change (blen doc) with L in NLE.
  pose proof (od_sbuf_range' L LR) as SBR.
  assert (SBX : OD_SBUF L mod 8 = 0 /\ L + 62 <= OD_SBUF L) by (clear - LR; unfold OD_SBUF, roundup64; Z.div_mod_to_equations; lia).
  set (icap := Z.to_nat (roundup64 L + 9)).
  assert (EIC : 4 * Z.of_nat icap = sc_idx L /\ L + 9 <= Z.of_nat icap).
  { subst icap. unfold sc_idx. assert (0 <= roundup64 L + 9 /\ L <= roundup64 L) by (clear - LR; unfold roundup64; Z.div_mod_to_equations; lia). rewrite Z2Nat.id by (clear - H; lia). clear - H. lia. }
  destruct EIC as (EIC & ICL).
  assert (ACTR : 0 <= od_action dz <= 12).
  { clear. unfold od_action. destruct dz as [|b r]; [lia|]. pose proof (Z.mod_pos_bound b 13 ltac:(lia)). lia. }

  pose proof (af_sp0_range RT AF ΣC mC ART0) as SP0R.
  assert (INF : In (F, 3%nat) (rt_frames RT ΣC)) by (rewrite FRS; left; reflexivity).
  pose proof (fframe_ranges RT AF ΣC mC F 3 ART0 INF) as (_ & FR1' & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF ΣC mC F 3 ART0 INF) as (FSL & FSF). pose proof (FSF F 3%nat INF) as FSELF.
  pose proof (af_frames_align RT AF ΣC mC F 3 ART0 INF) as (_ & FSEG).
  pose proof (af_frames_range RT AF ΣC mC F 3%nat ART0 INF) as (_ & _ & _ & FLV).
  change (fs_size 3) with 512 in *. rewrite SP0 in FR1', SHT.
  assert (SHF : shad (F + 512) = shad F + 64) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, FSL.
  assert (LOWC : rt_sp0 RT ΣC - STACK_WIN <= lo) by (rewrite SP0; exact LOW).
  assert (INS : In (IA, 1024) (rt_live RT ΣC) /\ In (OC, 8192) (rt_live RT ΣC) /\ In (IDX, sc_idx L) (rt_live RT ΣC) /\ In (IMPL, 96) (rt_live RT ΣC)
                /\ In (SB, OD_SBUF L) (rt_live RT ΣC) /\ In (COPY, len0 + 64) (rt_live RT ΣC)).
  { rewrite LV. cbn [app]. split; [left; reflexivity|]. split; [right; left; reflexivity|]. split; [do 2 right; left; reflexivity|]. split; [do 3 right; left; reflexivity|].
    split; [do 4 right; left; reflexivity| do 5 right; left; reflexivity]. }
  destruct INS as (INIA & INOC & INIX & INIM & INSB & INCP).
  assert (RNG : forall p n, In (p, n) (rt_live RT ΣC) -> p + n <= lo /\ (F + 512 <= p \/ p + n <= F)
                  /\ (p + n <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= p) /\ (p + n <= 0x10000 \/ 0x66b000 <= p)).
  { intros p n Hin. pose proof (af_live_range RT AF ΣC mC p n ART0 Hin) as (_ & R1 & R2). unfold SEGTOP_A in R2.
    split; [clear - R1 LOWC; lia|]. split; [exact (FLV p n Hin)|]. split; [exact (FSL p n Hin)| exact R2]. }
  pose proof (RNG _ _ INIX) as (X1 & X2 & X3 & X4). pose proof (RNG _ _ INIM) as (I1 & I2 & I3 & I4).
  pose proof (RNG _ _ INSB) as (B1 & B2 & B3 & B4). pose proof (RNG _ _ INCP) as (P1 & P2 & P3 & P4).
  assert (DJ : (SB + OD_SBUF L <= COPY \/ COPY + (len0 + 64) <= SB) /\ (SB + OD_SBUF L <= IDX \/ IDX + sc_idx L <= SB) /\ (SB + OD_SBUF L <= IMPL \/ IMPL + 96 <= SB)).
  { pose proof (af_live_disj RT AF ΣC mC SB (OD_SBUF L) COPY (len0 + 64) [(IA, 1024); (OC, 8192); (IDX, sc_idx L); (IMPL, 96)] _ ART0 LV ltac:(apply in_or_app; right; left; reflexivity)) as D1.
    pose proof (af_live_disj RT AF ΣC mC SB (OD_SBUF L) IDX (sc_idx L) [(IA, 1024); (OC, 8192); (IDX, sc_idx L); (IMPL, 96)] _ ART0 LV ltac:(apply in_or_app; left; do 2 right; left; reflexivity)) as D2.
    pose proof (af_live_disj RT AF ΣC mC SB (OD_SBUF L) IMPL 96 [(IA, 1024); (OC, 8192); (IDX, sc_idx L); (IMPL, 96)] _ ART0 LV ltac:(apply in_or_app; left; do 3 right; left; reflexivity)) as D3.
    repeat split; assumption. }
  destruct DJ as (D1 & D2 & D3).

  set (E := mkOaEnv (mkOdEnv cra (Z_to_bv 64 usp) gp (Z_to_bv 64 0x6488f0) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 lo BUF SB (OD_SBUF L) IMPL IDX icap COPY
                              (od_action dz) doc out (wz OD_DPI_VPTR) p12 nxt (mid16 p28 (wz L) (wz 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (wz OC) (wz IA)) docj
                              ([Z_to_bv 8 0] ++ jp) (wz L) (wz 0xffffffff) (wz 1024) (wz L) [] mC) usp S1 F).
  assert (G : od_geo E).
  { constructor; cbn [E oa_E oa_USP oa_S1 oa_F o_tp o_lo o_BUF o_SB o_CAP o_IMPL o_IDX o_icap o_COPY o_act o_bs o_idxs o_vptr]; try change (blen doc) with L; rewrite ?EIC.
    - exact DOCOK. - exact S1O. - unfold S1_LEN_MAX. clear - LR. lia. - exact ACTR. - reflexivity. - reflexivity.
    - split; [exact U16| clear - UT; ul]. - split; assumption. - split; [clear - LOW SP0R SP0; ul| clear - LOR S1R; ul].
    - split; [exact F64|]. split; [clear - FSEG; ul| clear - FR1' LOW; lia]. - split; [clear - SHT LOW; lia| exact FSELF].
    - split; [exact CPOS|]. split; [clear - C16; Z.div_mod_to_equations; lia|]. split; [exact CBR|]. split; [clear - P1 CBL CBR; lia| clear - P4 CBL CBR; lia].
    - split; [exact SBPOS|]. split; [clear - SB16; Z.div_mod_to_equations; lia|]. split; [exact B1| exact B4].
    - exact (proj2 SBX). - exact (proj1 SBX).
    - split; [exact IMPOS|]. split; [clear - IM16; Z.div_mod_to_equations; lia|]. split; [exact I1| exact I4].
    - split; [exact IXPOS|]. split; [clear - IX16; Z.div_mod_to_equations; lia|]. split; [exact X1| exact X4].
    - unfold tokn. clear - NLE ICL. lia.
    - clear - D1 CBL CBR. lia. - exact D2. - exact D3.
    - clear - P2 CBL CBR. lia. - exact B2. - exact X2. - exact I2. - clear - B3. lia. }

  set (S := F / 8 + 2147450880) in *.
  unfold od_shadow in SH. cbn [map] in SH.
  lazymatch type of SH with rw_cells _ _ _ ?l =>
    let a := eval cbv in (firstn 4 l) in let b := eval cbv in (firstn 3 (skipn 4 l)) in let c := eval cbv in (firstn 5 (skipn 7 l)) in
    let d := eval cbv in (firstn 7 (skipn 12 l)) in let e := eval cbv in (firstn 5 (skipn 19 l)) in let f := eval cbv in (firstn 8 (skipn 24 l)) in
    let g := eval cbv in (skipn 32 l) in
    change l with (a ++ b ++ c ++ d ++ e ++ f ++ g) in SH end.
  apply Sj_stage1_kit.rw_cells_app in SH. destruct SH as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [SHv X].
  apply Sj_stage1_kit.rw_cells_app in X. destruct X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [SHp X].
  apply Sj_stage1_kit.rw_cells_app in X. destruct X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [SHd _].
  cbn [cells_size csize Nat.add] in SHv, SHp, SHd.
  replace (S + Z.of_nat 4) with (S + 4) in * by lia.
  replace (S + 4 + Z.of_nat 3 + Z.of_nat 5) with (S + 12) in * by lia.
  replace (S + 12 + Z.of_nat 7 + Z.of_nat 5) with (S + 24) in * by lia.
  assert (R : od_rt RT ΣC E mC).
  { constructor; cbn [E oa_E oa_USP oa_S1 oa_F o_lo o_BUF o_SB o_CAP o_IMPL o_IDX o_icap o_COPY o_bs o_m0]; try change (blen doc) with L; rewrite ?EIC.
    - exact ART0. - exact FRS. - replace (BUF - COPY + L + 64) with (len0 + 64) by (clear - CBL; lia). exact INCP. - exact INSB. - exact INIM. - exact INIX. - exact LOWC.
    - exact (rw_cells_bytes_at asegs mC _ _ SHp). - exact (rw_cells_bytes_at asegs mC _ _ SHd).
    - intros a _ _. reflexivity. - apply wmono_refl. }

  unfold od_lowB in LOWF.
  apply (rw_cells_split_CB asegs _ _ [CB 184 j0; C8 (wz (od_action dz)); CB 8 j192; C8 (wz F); C8 (wz (F + 96)); C8 (wz (F + 104)); CB 16 j224; C8 (wz (F / 8 + 2147450880))] 104 _ []
           [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in LOWF; [| reflexivity].
  apply (rw_cells_split_CB asegs _ _ [CB 184 j0; C8 (wz (od_action dz)); CB 8 j192; C8 (wz F); C8 (wz (F + 96)); C8 (wz (F + 104))] 16 _ _ [8; 8]%nat) in LOWF; [| reflexivity].
  apply (rw_cells_split_CB asegs _ _ [] 184 _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in LOWF; [| reflexivity].
  cbn [mk_CB_cells app] in LOWF.
  assert (PRE : OD_PRE E mC).
  { unfold OD_PRE. cbn [E oa_E oa_USP oa_S1 oa_F o_lo o_BUF o_SB o_CAP o_IMPL o_IDX o_icap o_COPY o_act o_bs o_m0].
    split; [do 39 eexists; exact LOWF|].
    split; [exact DOCX|].
    split. { unfold od_parser_cells. cbn [E oa_E o_j304 o_IMPL o_w320 o_w328 o_w336 o_w344 o_SB].
             pose proof PAR as [[WF _] _]. unfold od_parserC in WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & L7 & _).
             apply (rw_cells_recell asegs mC (F + 96) _ _ PAR); [cbn [cells_wf cell_wf]; rewrite length_app; cbn [length]; repeat split; lia| reflexivity| reflexivity]. }
    split; [exact IMC|].
    split. { exists ws. split; [exact UIX|]. unfold idx_ok. cbn [E oa_E o_icap o_idxs o_bs]. split; [clear - LWS EIC; lia| exact FWS]. }
    split; [exact BUFB|]. split; [exact WSB|]. split; [exact (AFV ΣC mC ART0)|]. split; [exact (AFG ΣC mC ART0)|]. split; [exact MI0| exact ST0]. }
  assert (OUT : od_outer RT LIB ΣC E A cap size IA OC els (rt_live RT Σ0) cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 mC).
  { constructor; cbn [E oa_E oa_USP oa_S1 oa_F o_lo o_BUF o_SB o_CAP o_IMPL o_IDX o_icap o_COPY o_bs o_vptr]; try change (blen doc) with L; rewrite ?EIC.
    - exact HIX. - exact STp. - exact SAVED.
    - lazymatch type of HDR with rw_cells _ _ _ [?c0; ?c1] => change (rw_cells asegs mC F ([c0] ++ [c1])) in HDR end.
      apply Sj_stage1_kit.rw_cells_app in HDR. exists h0. exact (proj1 HDR).
    - exact VR. - destruct VR as (_ & VSC & _). clear - VSC SZ1. lia. - exact WRS. - exact SHv. - exact SHp. - exact SHd.
    - destruct (od_implC_dl mC IMPL IDX OC IA BUF _ _ p12 p28 p50 docj nxt IMC) as (pre8 & mid & rest & E1 & E2 & E3 & _ & EB).
      exists pre8, mid, rest. split; [exact E1|]. split; [exact E2|]. split; [exact E3| exact EB].
    - rewrite LV. cbn [app]. replace (BUF - COPY + L + 64) with (len0 + 64) by (clear - CBL; lia). reflexivity.
    - exact LVPOS. - exact LIB0. - exact CP0. }
  assert (CRED : rt_credit RT Σ0 - FUZZ_COST + OD_DBL_CREDIT * (o_n E + 2) <= rt_credit RT ΣC).
  { cbn [E oa_E o_idxs]. unfold tokn, OD_DBL_CREDIT.
    pose proof (sc_idx_bounds L ltac:(clear - LR; lia)) as IXB.
    pose proof (mcost_le (OD_SBUF L) ltac:(clear - SBR; lia)) as M1. pose proof (mcost_le (sc_idx L) ltac:(clear - IXB; lia)) as M2.
    assert (IXU : sc_idx L <= 4194340) by (clear - LR; unfold sc_idx, roundup64; Z.div_mod_to_equations; lia).
    assert (MC96 : mcost 96 = 2097152) by (vm_compute; reflexivity).
    assert (MC8K : mcost 8192 = 2097152) by (vm_compute; reflexivity).
    assert (MC1K : mcost 1024 = 2097152) by (vm_compute; reflexivity).
    assert (PADC : OD_PAD_COST = 4210688) by (vm_compute; reflexivity).
    rewrite MC96, MC8K, MC1K, PADC in CR. unfold OD_VEC_COST, FUZZ_COST in *. clear - CR M1 M2 SBR IXU NLE LR. lia. }
  exact (KI ΣC E A cap size IA OC els xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mC
           G R PRE eq_refl OUT eq_refl eq_refl eq_refl SP0 CRED FRM).
Qed.
End Hand.
