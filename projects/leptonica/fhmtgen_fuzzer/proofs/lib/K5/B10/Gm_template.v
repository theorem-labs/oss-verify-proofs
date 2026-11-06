(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit Lept_deserkit Lept_gmax_defs D_iface D_defs Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_leaf LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section TPL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis TNI : pixCreateTemplateNoInit_cps RT.

Theorem pixCreateTemplate_ok : pixCreateTemplate_cps RT.
Proof using AF RC GP TNI.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pixs vs cvs FDO MST -> -> POS SDNZ ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POS as (PXS & (PSIN & PS0 & PS16 & _) & HOKS & _ & PSCM).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixCreateTemplate, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, TEMPLATE_COST, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  assert (SP0H : hid (rt_sp0 RT Σ <= 2^47)) by (unfold hid; clear - SP0R; lia).
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  pose proof TNI as TN. unfold pixCreateTemplateNoInit_cps in TN.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pixs 64.
  unfold pix_cells in PXS.
  hide POS. hide PSCM. hide HOKS.
  carve_frame 32%nat ST.
  Time walk_to AF MST [(usp - 32, usp)] [0x92b24; 0x61400; 0x91520].
  cwalk [0x92b24; 0x61400; 0x91520].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  unfold hid in POS.
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a)
    by (intros q k a Hq Ha; right; right; left; exists q, k; split; [exact Hq| lia]).
  lazymatch goal with PX : rw_cells asegs ?mc pixs _, A : ART RT Σ ?mc |- _ =>
    assert (POS1 : pix_obj (rt_live RT Σ) mc pixs vs cvs)
      by (apply (pix_obj_agree (rt_live RT Σ) PF m mc pixs vs cvs POS AGF PML); unfold pix_cells; exact PX) end.
  hide POS.
  eapply cps_seq.
  { eapply TN with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
    all: lazymatch goal with
         | |- pix_obj _ _ _ _ _ => exact POS1
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold TEMPLATE_COST, RASTER_COST; lres_tac
         | |- ?g => idtac "LEFT:" g
         end. }
  clear POS1.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact He| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S1 end.
  lazymatch goal with H : pix_obj _ _ ?p ?vv ?cc |- _ => rename H into POD; set (pixd := p) in *; set (vd := vv) in *; set (cvd := cc) in * end.
  lazymatch goal with H : live_destroy pixd vd cvd _ = _ |- _ => rename H into LDS end.
  lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => rename H into LNC end.
  lazymatch goal with H : forall p n, In (p, n) (rt_live RT ?S) -> 0 < n |- cps _ (ASTA RT ?S _ _) _ => rename H into LVP1 end.
  lazymatch goal with H : Z.of_nat (length (rt_live RT ?S)) <= _ |- cps _ (ASTA RT ?S _ _) _ => rename H into LVX1 end.
  lazymatch goal with H : p_w vd = _ |- _ => rename H into VW end.
  lazymatch goal with H : p_h vd = _ |- _ => rename H into VH end.
  lazymatch goal with H : p_d vd = _ |- _ => rename H into VD end.
  lazymatch goal with H : p_data vd <> 0 |- _ => rename H into VDATA end.
  pose proof POD as (PXD & (PDIN & PD0 & PD16 & _) & HOKD & PDDATA & _).
  destruct PDDATA as [PDZ|((DIN & DA0 & DA16 & DAN) & DNE)]; [exfalso; exact (VDATA PDZ)|].
  unfold rsize in *.
  set (dat := p_data vd) in *. set (rs := 4 * (p_wpl vd * p_h vd)) in *.
  assert (SUBL : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S1) /\ fst e <> dat)
    by (intros e He; rewrite <- LDS in He; destruct (live_destroy_In _ _ _ _ _ He) as (Q1 & Q2 & Q3 & _); split; [exact Q1| exact (Q3 VDATA)]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
    assert (NCD : forall a, PF a -> a < dat \/ dat + rs <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF S mm dat rs (rt_live RT Σ) (rt_frames RT Σ) usp a A DIN SUBL);
          [ solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
  unfold pix_cells in PXD. fold dat in PXD.
  pose proof HOKD as (HD1 & HW1 & HH1 & HWPL & HRS). fold rs in HRS.
  hide POD. hide SUBL. hide HOKD. hide LDS. hide LNC.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 32, usp)] [0x92b24; 0x61400; 0x91520].
  cwalk [0x92b24; 0x61400; 0x91520].
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
    assert (POD2 : pix_obj (rt_live RT S) m2 pixd vd cvd)
      by (apply (pix_obj_agree_cm (rt_live RT S) P m1 m2 pixd vd cvd POD AG); [| unfold pix_cells; fold dat; exact PX];
          intros NZ a Ha; destruct POD as (_ & _ & _ & _ & [Z0|((_ & (CI & _) & _) & _ & _ & CND & _)]); [exfalso; exact (NZ Z0)|];
          split; [right; right; left; exists (p_cmap vd), 24; split; [exact CI| exact Ha]|];
          pose proof (live_apart2 RT AF S m2 (p_cmap vd) 24 dat rs A CI DIN ltac:(intros E; inversion E; apply CND; assumption)) as Q;
          clear - Q Ha; lia) end.
  clear POD.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact (proj1 (SUBL e He))| solve [frames_sub_tac]| lia]|
                                  pose proof (NCD _ Hx) as NCDx; clear - NCDx; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 32, usp)] (@nil Z).
  cwalk (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -32), FRx : rw_cells asegs _ (usp + -32) _ |- _ => release_frame FRx ST' usp end).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S3 _ _ _ => exists S3, pixd, vd, cvd end.
  split.
  2:{ unfold hid in LNC, LDS. split; [exact LNC|]. split; [exact LDS|]. split; [exact LVP1|]. split; [exact LVX1|].
      unfold TEMPLATE_COST, RASTER_COST in *. repeat split; first [assumption | lia]. }
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end. }
  split; [intros a Ha _; apply AGF; exact Ha|].
  split; [exact POD2|]. split; [exact VW|]. split; [exact VH|]. split; [exact VD| exact VDATA].
Qed.
End TPL.
