(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_chain Lept_gmax_defs
  Gm_iface Gq_obj Gq_iface Gq_opcase Gq_dbin_defs Gq_dbin_spec_c0 Gq_dbin_spec_c16.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Lept_fuzzkit Lept_deserkit Gm_kit Gm_livekit Gm_livekit2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.

Section DBIN.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis PCS : pixCreate_sure_cps RT.
Hypothesis PCR : pixCopyResolution_cps RT.
Hypothesis PCI : pixCopyInputFormat_cps RT.
Hypothesis PRC : pixRemoveColormap_gray_cps RT.
Hypothesis PDR : pixDestroy_rc_cps RT.
Hypothesis DES : pixDestroy_cps RT.

Local Ltac eqv :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.

(* [comment removed for export] *)
Lemma dbin_case : forall al, dbin_spec_case RT al ->
  gq_op_case RT al e_pixDitherToBinary RA_FUZZ_OP2 11 6 12 DBIN_COST (fun _ _ _ _ _ _ => True).
Proof using AF GP RC RERR PCS PCR PCI PRC PDR DES.
  intros al SPEC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST -> -> _ POBJ VDATA CNZ UC RAF RAS ENV RES AL.
  unfold lpost_f, lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixDitherToBinary, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pix 64.
  chunk_facts RT AF GP (p_data v) (rsize v).
  unfold pix_cells in PXC.
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a).
  { intros q k a Hq Ha. right; right; left; exists q, k; split; [exact Hq| lia]. }
  hide POBJ.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  carve_frame 48%nat ST.   (* [comment removed for export] *)
  walk_to AF MST [(usp - 48, usp)] [0x9c458].
  idtac "MARK at bne".
  (* [comment removed for export] *)
  assert (DR : 1 <= p_d v <= 32) by (clear - HD1; cbn [In] in HD1; lia).
  rewrite !(sx32_small (p_d v)) by lia.
  destruct (Z.eq_dec (p_d v) 8) as [D8|DN8].
  all: cycle 1.
  (* [comment removed for export] *)
  awalk [e_returnErrorPtr].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  release_frame FR ST usp.
  assert (CR4 : 4 <= rt_credit RT Σ) by (clear - CRB DN8; unfold DBIN_COST, OP_COST, is_d8, MSG_COST in CRB; rewrite (proj2 (Z.eqb_neq (p_d v) 8) DN8) in CRB; exact CRB).
  pose proof RERR as RE. unfold returnError_cps in RE.
  eapply cps_seq.
  { eapply RE with (lo := lo); rt_side idtac.
    1: lit_in_fast.
    1: lit_in_fast.
    lenv_tac. }
  idtac "MARK RE applied".
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  destruct Hc as (S' & HcA & LV' & FR' & SP' & CR').
  exists S', 0, v, cv.
  split.
  2: {
  split; [intros _; exact LV'|].
  split; [intros N; exfalso; apply N; reflexivity|].
  split; [rewrite LV'; exact LVP|].
  split; [rewrite LV'; lia|].
  split; [exact FR'|]. split; [exact SP'|].
  rewrite CR'. clear - CR4 DN8. unfold DBIN_COST, OP_COST, is_d8, MSG_COST. rewrite (proj2 (Z.eqb_neq (p_d v) 8) DN8). lia. }
  eapply (ASTA_conseq RT); [exact HcA|]; intros ms (m' & RET & (AFT & LIB & SSP') & PRES); exists m'.
  rewrite (unsigned_lit usp USP) in AFT, PRES.
  assert (KM : forall a : word, PF (bv_unsigned a) -> m' a = m a).
  { intros a Ha. rewrite (PRES a Ha). apply AGF. exact Ha. }
  split; [exact RET|].
  split; [split; [destruct AFT as (A1 & A2 & A3 & A4); exact (conj A1 (conj A2 A4)) | split; assumption]|].
  split; [intros a Ha Ho; exact (KM a Ha)|].
  split.
  { assert (KL0 : keeps_live (rt_live RT Σ) m m') by (intros b kk Hb a' Ha'; apply KM; exact (PML b kk _ Hb Ha')).
    rewrite LV'. unfold hid in POBJ. exact (pix_obj_keep _ m m' pix v cv KL0 POBJ). }
  left; reflexivity.
  idtac "MARK message arm closed".
  (* [comment removed for export] *)
  awalk [e_pixDitherToBinarySpec].
  idtac "MARK at Spec".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  release_frame FR ST usp.
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mj _))) _ => rename mj into mJ end.   (* [comment removed for export] *)
  assert (KM1 : forall a : word, PF (bv_unsigned a) -> mJ a = m a) by (intros a Ha; apply AGF; exact Ha).
  assert (KL1 : keeps_live (rt_live RT Σ) m mJ) by (intros b kk Hb a' Ha'; apply KM1; exact (PML b kk _ Hb Ha')).
  assert (POBJ1 : pix_obj (rt_live RT Σ) mJ pix v cv) by (unfold hid in POBJ; exact (pix_obj_keep _ m mJ pix v cv KL1 POBJ)).
  pose proof UC as UCX. unfold uctx in UCX. rewrite ESP in UCX. rewrite (unsigned_lit usp USP) in UCX.
  assert (UC1 : uctx mJ (Z_to_bv 64 usp) s0 ras).
  { unfold uctx. rewrite (unsigned_lit usp USP). apply (chain_ok_keep ras m mJ usp (bv_unsigned s0) UCX).
    eapply agree_sub; [exact AGF|]. intros zx Hzx; unfold PF. left; exact Hzx. }
  eapply cps_conseq.
  { eapply (SPEC Σ PMc) with (lo := lo) (pix := pix) (v := v) (cv := cv) (ras := ras).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact POBJ1.
    - exact VDATA.
    - exact CNZ.
    - exact D8.
    - exact UC1.
    - exact RAF.
    - exact RAS.
    - lenv_tac.
    - unfold lres; rewrite D8 in CRB; repeat split; [exact FRB| exact LVB| exact CRB| exact LVP].
    - first [exact AL | rewrite (unsigned_lit usp USP); exact AL]. }
  { intros c Hc; exact Hc. }
  cbv beta. intros c Hc.
  destruct Hc as (S' & r & vr & cvr & HcA & LV0 & LVD & LVP' & LVL & FR' & SP' & CR').
  subst QF. cbv beta. exists S', r, vr, cvr.
  split.
  2: { rewrite D8. repeat (split; [assumption|]). exact CR'. }
  eapply (ASTA_conseq RT); [exact HcA|]; intros ms (m' & RET & LPF & PRES & POBJ' & RR); exists m'.
  unfold lpost_f, keepsL in LPF, PRES. rewrite (unsigned_lit usp USP) in LPF, PRES.
  split; [exact RET|].
  split; [exact LPF|].
  split; [| exact (conj POBJ' RR)].
  intros a Ha Ho. rewrite (PRES a Ha Ho). apply KM1. exact Ha.
Qed.

Theorem pixDitherToBinary_ok : pixDitherToBinary_cps RT.
Proof using AF GP RC RERR PCS PCR PCI PRC PDR DES.
  unfold pixDitherToBinary_cps.
  apply (gq_op_of_cases RT).
  - exact (dbin_case 0 (dbin_spec_c0 RT AF GP RC RERR PCS PCR PCI PRC PDR DES)).
  - exact (dbin_case 16 (dbin_spec_c16 RT AF GP RC RERR PCS PCR PCI PRC PDR DES)).
Qed.
End DBIN.
