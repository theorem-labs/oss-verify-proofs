(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit Lept_deserkit Lept_gmax_defs D_iface D_defs Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_leaf Gq_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Lemma tr_noinit_create : In [RA_NOINIT_MALLOC; 0x93300] CLIENT_TRACES.
Proof. apply ct_mem_In. vm_compute. reflexivity. Qed.

Section CRS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis NIS : pixCreateNoInit_sure_cps RT.

Theorem pixCreate_sure_ok : pixCreate_sure_cps RT.
Proof using AF RC GP NIS.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    w h d FDO MST -> A0 A1 A2 HAOK ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct A0 as [W32 ->]. destruct A1 as [H32 ->]. destruct A2 as [D32 ->].
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixCreate, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  assert (SP0H : hid (rt_sp0 RT Σ <= 2^47)) by (unfold hid; clear - SP0R; lia).
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  pose proof NIS as NI. unfold pixCreateNoInit_sure_cps in NI.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  hide HAOK.
  carve_frame 16%nat ST.
  Time walk_to AF MST [(usp - 16, usp)] [0x93410; 0x60ce0; 0x90e84].
  cwalk [0x93410; 0x60ce0; 0x90e84].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  unfold hid in HAOK.
  eapply cps_seq.
  { eapply NI with (lo := lo) (w := w) (h := h) (d := d) (ras := @nil Z); rt_side idtac.
    all: lazymatch goal with
         | |- s32 _ _ => split; [lia| reflexivity]
         | |- hdr_args_ok _ _ _ => exact HAOK
         | |- uctx _ _ _ _ => unfold uctx; cbn [chain_ok]; unfold link_invalid; rewrite ?unsigned_lit by ul; left; lia
         | |- In _ CLIENT_TRACES => exact tr_noinit_create
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold RASTER_COST; lres_tac
         | |- ?g => idtac "LEFT:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S1 end.
  lazymatch goal with H : pix_obj _ _ ?p ?vv _ |- _ => rename H into POD; set (pixd := p) in *; set (vd := vv) in * end.
  lazymatch goal with H : rt_live RT _ = (p_data vd, _) :: _ |- _ => rename H into LVN end.
  lazymatch goal with H : p_w vd = _ |- _ => rename H into VW end.
  lazymatch goal with H : p_h vd = _ |- _ => rename H into VH end.
  lazymatch goal with H : p_d vd = _ |- _ => rename H into VD end.
  lazymatch goal with H : p_data vd <> 0 |- _ => rename H into VDATA end.
  lazymatch goal with H : p_cmap vd = 0 |- _ => rename H into VCMAP end.
  pose proof POD as (PXD & (PDIN & PD0 & PD16 & _) & HOKD & PDDATA & _).
  destruct PDDATA as [PDZ|((DIN & DA0 & DA16 & DAN) & DNE)]; [exfalso; exact (VDATA PDZ)|].
  unfold rsize in *.
  set (dat := p_data vd) in *. set (rs := 4 * (p_wpl vd * p_h vd)) in *.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
    assert (SUBL : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S) /\ fst e <> dat)
      by (intros e He; split; [rewrite LVN; right; right; exact He|];
          apply (fresh_chunk_ne RT AF S mm [] dat rs _ e A LVN); [ cbn [app]; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]);
    assert (NCD : forall a, PF a -> a < dat \/ dat + rs <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF S mm dat rs (rt_live RT Σ) (rt_frames RT Σ) usp a A DIN SUBL);
          [ solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
  unfold pix_cells in PXD. fold dat in PXD.
  pose proof HOKD as (HD1 & HW1 & HH1 & HWPL & HRS). fold rs in HRS.
  hide POD. hide SUBL. hide HOKD.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 16, usp)] [0x93410; 0x60ce0; 0x90e84].
  cwalk [0x93410; 0x60ce0; 0x90e84].
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  assert (DATB : 0 <= dat <= 2^47)
    by (lazymatch goal with H : dat + rs <= rt_sp0 RT Σ - _ |- _ => pose proof SP0H as SP0x; unfold hid in SP0x; clear - H SP0x DA0 DAN; lia end).
  eapply cps_seq.
  { pose proof (rc_asan_memset RT RC) as MS0; unfold memset_icontract in MS0;
    eapply MS0 with (lo := lo) (d := dat) (n := rs) (c := Z_to_bv 8 0); rt_side idtac.
    all: lazymatch goal with
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ =>
             assert (WPLB : 0 < p_wpl vd <= 16777216) by (clear - HRS HH1; subst rs; nia);
             f_equal; unfold zx32; rewrite ?unsigned_lit by (clear - WPLB HH1; lia); rewrite ?(Z.mod_small _ (2^32)) by (clear - WPLB HH1; lia);
             rewrite ?Z.mod_small by (clear - WPLB HH1; lia); unfold rs; clear; lia
         | |- (0 <= _ <= _) => exact DATB
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by lia;
             split; [intros _; split; [assumption| left; exists dat, rs; split; [exact DIN| clear; lia]]|];
             split; [intros i Hi; right; right; left; exists dat, rs; split; [exact DIN| clear - Hi; lia]|
                     lazymatch goal with A : ART RT ?S ?mm |- wr_at _ ?mm _ _ => exact (proj1 (af_acc_live RT AF S mm dat rs A DIN)) end]
         end. }
  lazymatch goal with A : ART RT S1 ?mm |- _ =>
    pose proof (live_apart2 RT AF S1 mm pixd 64 dat rs A PDIN DIN ltac:(intros E; inversion E; apply DNE; symmetry; assumption)) as DPD end.
  after_call RT AF.
  unfold hid in POD.
  lazymatch goal with AG : agree_on ?P ?m1 ?m2, PX : rw_cells asegs ?m2 pixd _, A : ART RT ?S ?m2 |- _ =>
    assert (POD2 : pix_obj (rt_live RT S) m2 pixd vd (mkCmapv 0 0 0 0))
      by (apply (pix_obj_agree_cm (rt_live RT S) P m1 m2 pixd vd (mkCmapv 0 0 0 0) POD AG); [| unfold pix_cells; fold dat; exact PX];
          intros NZ; exfalso; exact (NZ VCMAP)) end.
  clear POD.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact (proj1 (SUBL e He))| solve [frames_sub_tac]| lia]|
                                  pose proof (NCD _ Hx) as NCDx; clear - NCDx; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 16, usp)] (@nil Z).
  cwalk (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -16), FRx : rw_cells asegs _ (usp + -16) _ |- _ => release_frame FRx ST' usp end).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S3 _ _ _ => exists S3, pixd, vd end.
  split.
  2:{ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
      unfold RASTER_COST in *. repeat split; first [assumption | reflexivity | lia]. }
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end. }
  split; [intros a Ha _; apply AGF; exact Ha|].
  split; [exact POD2|]. split; [exact VW|]. split; [exact VH|]. split; [exact VD|]. split; [exact VDATA| exact VCMAP].
Qed.
End CRS.
