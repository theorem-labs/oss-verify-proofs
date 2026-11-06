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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Atp_activewA Od_defsA Od_cpsA Od_hkit0A Od_hkit3A Od_setcapA Od_deldtorA Od_lkitA Od_beginA Od_topA
  Od_errx_defsA Od_setup_defsA Od_setup_defs2A Od_setupkA Od_setupw2A Od_setupw4A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma od_sbuf_range' : forall L, 0 <= L <= 1048512 -> 64 <= OD_SBUF L <= 1747648.
Proof. intros L H. unfold OD_SBUF, roundup64. Z.div_mod_to_equations. lia. Qed.

Lemma od_implC_dl : forall (m : mem) IMPL IDX OC IA BUF L nidx p12 p28 p50 docj nxt,
  rw_cells asegs m IMPL (od_implC IDX OC IA BUF L nidx p12 p28 p50 docj nxt) ->
  exists pre8 mid rest, length pre8 = 8%nat /\ length mid = 32%nat /\ length rest = 24%nat
    /\ rw_cells asegs m IMPL (dl_cells (wz OD_DPI_VPTR) pre8 (wz IDX) mid (wz OC) (wz IA) rest)
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
  apply (rw_cells_recell asegs m IMPL _ _ H); [unfold dl_cells; cbn [cells_wf cell_wf]; repeat split; assumption| exact EB| reflexivity].
Qed.

Section PhaseC2.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).
Hypothesis AF : art_facts RT.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Definition od_handover_stmt : Prop :=
  forall (K : config -> Prop) (Σ0 ΣC : rts RT) (m0 mC : mem) (usp S1 F lo : Z) (dz : list Z) (A cap size COPY BUF SB IMPL IDX OC IA : Z) (out : list Z)
         (els : list (Z * Z)) (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 : word) xF xfc,
    od_cutC RT LIB Σ0 ΣC m0 mC usp S1 F lo dz A cap size COPY BUF SB IMPL IDX OC IA 0 out els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
    frm0 xfc ->
    od_iter_k RT LIB PMc K Σ0 m0 usp lo gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
    aevt ΣC K (MS (mkR xra (wz S1) gp (wz 0x6488f0) xt0 xt1 xt2 (wz usp) (wz S1) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (wz F) (wz 2147450880) (wz (F + 32)) (wz (F + 96)) (wz (F + 192)) (wz COPY) xs8 (wz BUF) xs10 xs11 xt3 xt4 xt5 xt6)
                  xF (wz OD_ITER) xfc None mC (seg_rom asegs)).

Hypothesis ERRX : od_errx_stmt RT LIB PMc.
Hypothesis HANDOVER : od_handover_stmt.

Theorem od_phaseC2 : od_phaseC2_stmt RT LIB PMc.
Proof using AF MST ERRX HANDOVER.
  intros K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 _ _ KI KF.
  unfold od_cutC_k.
  intros ΣC S1 F A cap size COPY BUF SB IMPL IDX OC IA code out els xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 xF xfc mC FRM CC.
  assert (CODER : 0 <= code < 64).
  { destruct (cc_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CC) as [(_ & E)|(_ & E & _)]; [| lia].
    pose proof (stage1_code_range (od_doc dz)) as X. rewrite <- E in X. exact X. }
  destruct (Z.eq_dec code 0) as [C0|CNZ].
  -
    subst code. apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [exact (od_walkC5s _ usp S1 F gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc mC)|].
    cbv beta. intros ms <-. apply evt_done. unfold lh_regs.
    exact (HANDOVER K Σ0 ΣC m0 mC usp S1 F lo dz A cap size COPY BUF SB IMPL IDX OC IA out els gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc CC FRM KI).
  -
    destruct CC as [C0 DZ LV CPY CHK CR (j0 & j192 & j224 & j248 & LOWF) (jp & PAR) SH WSB CODE (p12 & p28 & p50 & docj & nxt & IMC) IDXA].
    destruct (od_implC_dl mC IMPL IDX OC IA BUF _ _ p12 p28 p50 docj nxt IMC) as (pre8 & mid & rest & _ & _ & _ & DL & _).
    destruct CHK as (_ & (_ & IM16) & _).
    pose proof (sc_idx_bounds (zlength (od_doc dz))) as IXB.
    assert (LR : 0 <= zlength (od_doc dz) <= 1048512).
    { unfold od_doc, od_copied in *. destruct (zlength (od_s0 dz) <=? SJ_PADMAX) eqn:E; [| unfold zlength; cbn; lia].
      apply Z.leb_le in E. unfold SJ_PADMAX in E. destruct CPY as (_ & _ & X1 & X2 & _). unfold zlength in *. lia. }
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [exact (od_walkC5e _ usp S1 F code gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc mC ltac:(lia))|].
    cbv beta. intros ms <-. apply evt_done. unfold lh_regs.
    refine (ERRX K Σ0 ΣC m0 mC usp S1 F lo A cap size els gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
              COPY (zlength (od_s0 dz) + 64) SB _ IMPL IDX _ OC IA (od_action dz) code (rt_credit RT Σ0 - FUZZ_COST)
              (if od_copied dz then [(COPY, zlength (od_s0 dz) + 64)] else []) j0 j192 j224 j248 ([Z_to_bv 8 0] ++ jp)
              (le8 (wz (zlength (od_doc dz))) ++ le8 (wz 0xffffffff) ++ le8 (wz 1024) ++ le8 (wz (zlength (od_doc dz)))) pre8 mid rest
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc C0 _ LV _ _ _ LOWF _ SH DL ltac:(lia) _ FRM KF).
    + revert CPY. destruct (od_copied dz); intros CPY; [left; split; [reflexivity|]; destruct CPY as (X & _); split; [exact X| unfold zlength; lia]| right; split; [reflexivity| exact (proj1 CPY)]].
    + clear - IXB LR. lia.
    + pose proof (od_sbuf_range' (zlength (od_doc dz)) LR). lia.
    + clear - IM16. Z.div_mod_to_equations. lia.
    + pose proof PAR as [[WF _] _]. unfold od_parserC in WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & L7 & _).
      apply (rw_cells_recell asegs mC (F + 96) _ _ PAR).
      * unfold od_parserX. cbn [cells_wf cell_wf]. rewrite !length_app, !length_le8. cbn [length]. repeat split; lia.
      * unfold od_parserX, od_parserC. cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
      * reflexivity.
    + pose proof (od_sbuf_range' (zlength (od_doc dz)) LR) as SBR.
      pose proof (mcost_le (OD_SBUF (zlength (od_doc dz))) ltac:(lia)) as M1. pose proof (mcost_le (sc_idx (zlength (od_doc dz))) ltac:(lia)) as M2.
      assert (IXU : sc_idx (zlength (od_doc dz)) <= 4194340) by (clear - LR; unfold sc_idx, roundup64; Z.div_mod_to_equations; lia).
      assert (MC96 : mcost 96 = 2097152) by (vm_compute; reflexivity).
      assert (MC8K : mcost 8192 = 2097152) by (vm_compute; reflexivity).
      assert (MC1K : mcost 1024 = 2097152) by (vm_compute; reflexivity).
      assert (PADC : OD_PAD_COST = 4210688) by (vm_compute; reflexivity).
      rewrite MC96, MC8K, MC1K, PADC in CR. unfold OD_VEC_COST, FUZZ_COST in *. clear - CR M1 M2 SBR IXU. lia.
Qed.
End PhaseC2.
