(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_gmax_defs Gm_iface GmL_k3h_kit GmL_e3h_loop Gm_k3h_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tlia ::= sf_clear_big;
              first [ sf_unhide; unpark_all; zify_prune_sub; Zify.zify; xlia zchecker
                    | Zify.zify; xlia zchecker
                    | sf_unhide; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].

Section E3HC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis TPL : pixCreateTemplate_cps RT.

Lemma e3h_c16 : gray3h_case RT e_pixErodeGray3h 16.
Proof using AF GP TPL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pixs vs cvs
    FDO MST -> -> POBJ D8 NOCM VDATA ENV RES AL.
  unfold lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). unfold GRAY3H_COST, TEMPLATE_COST, RASTER_COST in *.
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixErodeGray3h, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof TPL as TP. unfold pixCreateTemplate_cps in TP.
  set (PF0 := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pixs 64.
  chunk_facts RT AF GP (p_data vs) (rsize vs).
  unfold pix_cells in PXC.
  hide POBJ.
  carve_frame 176%nat ST.
  walk_to AF MST [(usp - 176, usp)] [e_stack_malloc 0%nat].

  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; clear - P LOR; split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF0 (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 0%nat 64 pixs 64.
  fframe_chunk RT AF fr 0%nat 64 (p_data vs) (rsize vs).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 176, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0xa6f8c].

  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                       destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH.
  park_disj.
  rewrite D8 in *.
  walk_to AF MST [(usp - 336, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_pixCreateTemplate].

  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF0 a).
  { intros q k a Hq Ha. right; right; left; exists q, k; split; [exact Hq| lia]. }
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in POBJ.
  lazymatch type of AGF with agree_on _ _ ?mc =>
    assert (POBJ1 : pix_obj (rt_live RT Σ) mc pixs vs cvs)
      by (apply (pix_obj_agree (rt_live RT Σ) PF0 m mc pixs vs cvs POBJ AGF PML); unfold pix_cells; rewrite D8; exact PXC) end.
  eapply cps_seq.
  { eapply TP with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
    - repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. exact POBJ1.
    - lenv_tac.
    - unfold TEMPLATE_COST, RASTER_COST; lres_tac. }

  after_call RT AF.

  lazymatch goal with H : live_destroy ?pd ?vd0 ?cvd0 (rt_live RT ?S1) = _ |- _ =>
    rename pd into pixd; rename vd0 into vd; rename cvd0 into cvd; rename S1 into Σ1; rename H into LDES end.
  lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => destruct (H NOCM) as (VDC & LVD); clear H end.
  lazymatch goal with H : pix_obj (rt_live RT Σ1) _ pixd vd cvd |- _ => rename H into POBJD end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).

  pose proof POBJD as (PDC & (PDIN & PD0 & PD16 & _) & (HD1d & HW1d & HH1d & HWPLd & HRSd) & PDATAD & _).
  destruct PDATAD as [DZd|((DDIN & DD0 & DD16 & DDSZ) & DDNE)]; [contradiction|].

  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  assert (FRS1 : rt_frames RT Σ1 = (fr, 0%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  chunk_facts RT AF GP pixd 64.
  chunk_facts RT AF GP (p_data vd) (rsize vd).
  fframe_chunk RT AF fr 0%nat 64 pixd 64.
  fframe_chunk RT AF fr 0%nat 64 (p_data vd) (rsize vd).

  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH.

  park_disj.
  unfold pix_cells in PDC.
  walk_to AF MST [(usp - 336, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (p_data vd, p_data vd + rsize vd)] [e_pixGetDimensions].

  (* [comment removed for export] *)
  awalk [0xa7020].

  sx32_fix.
  awalk [0xa7020]. sx32_fix.

  (* [comment removed for export] *)
  assert (NUMS : (0 < p_w vs <= 20000 /\ 0 < p_h vs <= 20000) /\ p_wpl vs = (p_w vs * 8 + 31) / 32 /\ 0 < 4 * (p_wpl vs * p_h vs) <= 67108864).
  { destruct POBJ1 as (_ & _ & (_ & A & B & C & D) & _). rewrite D8 in C. clear - A B C D. tauto. }
  assert (NUMD : p_wpl vd = p_wpl vs /\ p_h vd = p_h vs).
  { destruct POBJD as (_ & _ & (_ & _ & _ & C & _) & _). destruct POBJ1 as (_ & _ & (_ & _ & _ & C1 & _) & _).
    split; [| congruence]. rewrite C, C1. repeat match goal with H : p_w vd = _ |- _ => rewrite H end.
    repeat match goal with H : p_d vd = _ |- _ => rewrite H end. rewrite ?D8. reflexivity. }
  destruct NUMD as (EWPLD & EHD). unfold rsize in *. rewrite EWPLD, EHD in *.
  set (w := p_w vs) in *. set (h := p_h vs) in *. set (wpl := p_wpl vs) in *. set (datas := p_data vs) in *. set (datad := p_data vd) in *.
  destruct NUMS as ((HWR & HHR) & EWPL & HSZ).
  assert (WPLR : 0 < wpl <= 5000 /\ w <= 4 * wpl) by (clear - HWR EWPL; Z.div_mod_to_equations; lia).
  destruct WPLR as (WPLR & WLE).
  lazymatch goal with A1 : ART RT Σ1 ?m1, WMx : wmono asegs ?m1 ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wr_at_transport asegs m1 mm datas (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ1 m1 datas (4 * (wpl * h)) A1 ltac:(solve [in_live_tac]))) WMx) as WRS;
    pose proof (wr_at_transport asegs m1 mm datad (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ1 m1 datad (4 * (wpl * h)) A1 ltac:(solve [in_live_tac]))) WMx) as WRD end.

  apply wr_at_rw_CB in WRS; [| clear - HSZ; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC. destruct SBC as [HBS _].
  apply wr_at_rw_CB in WRD; [| clear - HSZ; lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
  rewrite (sx32_small w) in FRM by (clear - HWR; lia). rewrite (sx32_small h) in FRM by (clear - HHR; lia).
  pose proof FRM as WC; split_at WC 4%nat WC2; split_at WC2 1%nat WC3; clear WC WC3.
  pose proof FRM as HC; split_at HC 6%nat HC2; split_at HC2 1%nat HC3; clear HC HC3.

  assert (QSP : rt_sp0 RT Σ <= 140737488355328) by (pose proof (af_sp0_range RT AF Σ m ART0) as X; unfold USTACK_TOP in X; clear - X; lia).
  assert (QSEP : datad + 4 * (wpl * h) <= datas \/ datas + 4 * (wpl * h) <= datad).
  { lazymatch goal with A1 : ART RT Σ1 ?m1 |- _ =>
      apply (af_live_disj RT AF Σ1 m1 datad (4 * (wpl * h)) datas (4 * (wpl * h)) [] ((pixd, 64) :: rt_live RT x) A1 LVD) end.
    cbn [app]. right. repeat match goal with H : rt_live RT x = _ |- _ => rewrite H end. exact DIN. }
  assert (Q1 : Z.of_nat (Z.to_nat h) = h - 0) by (clear - HHR; lia).
  assert (Q3 : (1 <= Z.to_nat h)%nat) by (clear - HHR; lia).
  assert (QK : 10 <= w -> (1 <= Z.to_nat ((w - 10) / 8 + 1))%nat /\ 8 * (Z.of_nat (Z.to_nat ((w - 10) / 8 + 1)) - 1) + 9 < w <= 8 * (Z.of_nat (Z.to_nat ((w - 10) / 8 + 1)) - 1) + 17).
  { clear. intros HW. assert (0 <= (w - 10) / 8) by (apply Z.div_pos; lia). rewrite Z2Nat.id by lia. split; [lia|]. Z.div_mod_to_equations. lia. }
  assert (QS8 : datas = 8 * (datas / 8)) by (clear - D16; Z.div_mod_to_equations; lia).
  assert (QS0 : 0 < datas / 8) by (clear - D0 D16; Z.div_mod_to_equations; lia).
  assert (QD8 : datad = 8 * (datad / 8)) by (clear - DD16; Z.div_mod_to_equations; lia).
  assert (QD0 : 0 < datad / 8) by (clear - DD0 DD16; Z.div_mod_to_equations; lia).
  assert (QSH : datas + 4 * (wpl * h) <= 2^47) by (clear - CKR0 QSP; lia).
  assert (QDH : datad + 4 * (wpl * h) <= 2^47) by (clear - CKR2 QSP; lia).
  assert (QSS : hid (datas + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datas)) by (clear - CKH0; unfold hid, parked in *; lia).
  assert (QDS : hid (datad + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad)) by (clear - CKH2; unfold hid, parked in *; lia).
  assert (QDG : hid (datad + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datad)) by (clear - CKS2; unfold hid, parked, SEGTOP_A in *; lia).
  assert (QSD : hid (datas + 4 * (wpl * h) <= datad \/ datad + 4 * (wpl * h) <= datas)) by (clear - QSEP; unfold hid; lia).
  assert (QW0 : 0 < fr + 32) by (clear - FR0; lia).
  assert (QWH : fr + 32 + 4 <= 2^47) by (clear - FRHI QSP; lia).
  assert (QWS : hid (fr + 32 + 4 <= datad \/ datad + 4 * (wpl * h) <= fr + 32)) by (clear - FCD2; unfold hid, parked in *; lia).
  assert (QH0 : 0 < fr + 48) by (clear - FR0; lia).
  assert (QHH : fr + 48 + 4 <= 2^47) by (clear - FRHI QSP; lia).
  assert (QHS : hid (fr + 48 + 4 <= datad \/ datad + 4 * (wpl * h) <= fr + 48)) by (clear - FCD2; unfold hid, parked in *; lia).

  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (e3h_rows (Z.to_nat h) 0 (Z.to_nat ((w - 10) / 8 + 1)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm
                     datas datad (4 * (wpl * h)) w h (fr + 32) (fr + 48) (datas / 8) (datad / 8) wpl sbs dbs
                     Q1 ltac:(lia) Q3 ltac:(clear - HWR WLE; lia) ltac:(clear - WPLR; lia) HHR eq_refl QK
                     QS8 QS0 QSH QSS QD8 QD0 QDH QDS QDG QSD QW0 QWH QWS QH0 QHH QHS
                     HBS ltac:(rewrite SBL; clear - HSZ; lia) ltac:(assumption) DBC ltac:(rewrite DBL; clear - HSZ; lia) ltac:(assumption) WC2 HC2 MIx) as ZR end.
    unfold SHB in ZR.
    replace (datas + 4 * (wpl * 0)) with datas in ZR by (clear; lia).
    replace (datad + 4 * (wpl * 0)) with datad in ZR by (clear; lia).
    exact ZR. }

  (* [comment removed for export] *)
  intros ms' PO. unfold e3h_exit in PO.
  destruct PO as (ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s5' & s6' & s7' & s11' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI').
  unfold SHB.
  assert (FCS2' : datad + 4 * (wpl * h) <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 8 <= datad)
    by (clear - FCS2; unfold parked in FCS2; Z.div_mod_to_equations; lia).
  lazymatch goal with A1 : ART RT Σ1 ?m1 |- _ =>
    assert (NCD : forall a, PF0 a -> a < datad \/ datad + 4 * (wpl * h) <= a)
      by (intros a Ha; apply (new_chunk_apart RT AF Σ1 m1 datad (4 * (wpl * h)) ((pixd, 64) :: rt_live RT x) (rt_frames RT Σ1) usp a A1 LVD eq_refl);
          [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
          | apply (aclient_mono _ _ usp _ _ usp _ Ha); [intros e He; right; repeat match goal with H : rt_live RT x = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia] ]);
    assert (QPD : pixd + 64 <= datad \/ datad + 4 * (wpl * h) <= pixd)
      by (pose proof (af_live_disj RT AF Σ1 m1 datad (4 * (wpl * h)) pixd 64 [] ((pixd, 64) :: rt_live RT x) A1 LVD ltac:(left; reflexivity)) as X; clear - X; lia)
  end.

  loop_art RT AF Σ1 m' lo MU'
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
            split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]]).

  lazymatch goal with A1 : ART RT Σ1 ?m1 |- _ =>
    assert (QPS : pixs + 64 <= datad \/ datad + 4 * (wpl * h) <= pixs)
      by (pose proof (af_live_disj RT AF Σ1 m1 datad (4 * (wpl * h)) pixs 64 [] ((pixd, 64) :: rt_live RT x) A1 LVD
                        ltac:(right; repeat match goal with H : rt_live RT x = _ |- _ => rewrite H end; exact PIN)) as X; clear - X; lia) end.
  clear HBS SBL DBC DBL WC2 HC2 Q1 Q3 QK QS8 QS0 QD8 QD0 QSH QDH QSS QDS QDG QSD QW0 QWH QWS QH0 QHH QHS.
  lazymatch type of MU' with munch _ ?mm m' =>
    loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR2 CKS2 FCD2 FCS2' QPD QPS LOW LOR SPT; unfold parked in *; lia) end.
  clear MU' WM'.
  (* [comment removed for export] *)

  awalk [0xa7450].

  frame_release_w RT AF GP MST Σ fr 0%nat 64 PF0 AGF PFS usp lo 0xa7458
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
            split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                    destruct (NFA _ Hx) as [N1 N2]; let P2 := fresh "P" in pose proof (NCD _ Hx) as P2; unfold shad, SHB in N1, N2 |- *; clear - P P2 N1 N2 LOR FR64;
                    repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
    ltac:(fun Hx => exact Hx)
    ltac:(fun fl FLN => idtac).

  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 176, usp)] (@nil Z).
  lazymatch goal with ST' : stk asegs _ lo (usp + -176) |- _ => release_frame FR ST' usp end.

  cps_stop.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. exists pixd, vd.
  split.
  2:{ unfold rsize, GRAY3H_COST, TEMPLATE_COST, RASTER_COST in *. rewrite ?EWPLD, ?EHD. fold wpl h datad. alg_tac. }

  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split.
  { split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption].
    repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }

  split.
  { repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. intros a Ha Ho; exact (AGF a Ha). }

  destruct POBJD as (_ & CHD & HOKD & PDATD & _).
  split.
  { split; [unfold pix_cells; rewrite EWPLD, EHD; exact PDC|].
    repeat match goal with H : rt_live RT _ = rt_live RT Σ1 |- _ => rewrite H end.
    split; [exact CHD|]. split; [exact HOKD|]. split; [exact PDATD|]. left. exact VDC. }

  unfold w, h. repeat split; first [assumption | congruence | lia].

Qed.
End E3HC.
