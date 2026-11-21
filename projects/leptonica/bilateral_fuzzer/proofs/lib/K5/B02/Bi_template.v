(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics, in the form of leptonica/paintcmap_fuzzer's plain proof of pixCopy). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 Pm_ckit Pm_okit Cf_iface Cf_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit LeptB_guard LeptB_guard2 LeptB_guard3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma pix_obj_rc_mono : forall live live' (m : mem) pix v cv rc, (forall e, In e live -> In e live') ->
  pix_obj_rc live m pix v cv rc -> pix_obj_rc live' m pix v cv rc.
Proof.
  intros live live' m pix v cv rc S. unfold pix_obj_rc, cmap_obj, chunk.
  intros (C & (CIN & CH) & HOK & HD & HCM).
  split; [exact C|]. split; [split; [apply S; exact CIN| exact CH]|]. split; [exact HOK|].
  split.
  - destruct HD as [HD|((DIN & DH) & DNE)]; [left; exact HD| right; split; [split; [apply S; exact DIN| exact DH]| exact DNE]].
  - destruct HCM as [HCM|((CC & (MIN & MH) & (AIN & AH) & COK & CNE) & R)]; [left; exact HCM|].
    right. split; [| exact R]. split; [exact CC|]. split; [split; [apply S; exact MIN| exact MH]|].
    split; [split; [apply S; exact AIN| exact AH]|]. split; [exact COK| exact CNE].
Qed.

Local Ltac shbr_inv8m :=
  match goal with
  | K : shk ?m ?b ?X, ACC : acc asegs ?m ?a ?n |- evt _ _ (MS _ _ (if _ then _ else _) _ _ ?m _) =>
      let OK := fresh "SHOK" in
      assert (OK : sh_ok b (X + 8 - 1)) by (apply (shk_ok m a n X 8 b ACC K); lia);
      apply sh_ok_8 in OK; [ | lia ]; rewrite ?OK; brT; clear K OK
  end.

Section PIXTEMPLATE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis TMPL : pixCreateTemplateNoInit_nn_cpsF RT.

Theorem pixCreateTemplate_ok : pixCreateTemplate_cps RT.
Proof using AF GP FKC TMPL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix rc v
    FDO MST -> -> POS RCB PD8 PCM0 VDAT ENV RES SECB.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixCreateTemplate, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof TMPL as TM. unfold pixCreateTemplateNoInit_nn_cpsF in TM. unfold RASTER_COST in TM.
  pose proof POS as (PXS & (PIN & PS0 & PS16 & _) & HOKS & _ & _).
  unfold pix_cells_rc in PXS.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pix 64.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 32, usp)] [0x9a3e0; 0x669cc; 0x96a88].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply TM with (lo := lo) (pixs := pix) (v := v) (cv := mkCmapv 0 0 0 0) (rc := rc); rt_side idtac.
    all: lazymatch goal with
         | |- pix_obj_rc _ ?mc _ _ _ _ => exact (pix_obj_rc_keep_all _ m mc pix v _ rc POS (keeps_live_of_agf _ _ _ _ _ AGF))
         | |- (_ <= _ <= _) => lia
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with HC : pm_hdr_copy _ ?vv _ ?cc |- _ =>
    lazymatch goal with H : pix_obj _ _ ?p vv cc |- _ => rename H into POBJ1; rename HC into HCOPY; set (pixd := p) in * end end.
  lazymatch goal with H : pixd <> 0 |- _ => rename H into PNZ end.
  lazymatch goal with H : rt_live RT _ = pm_copy_live pixd _ _ _ |- _ => rename H into LVH end.
  lazymatch type of POBJ1 with pix_obj _ _ _ ?vv ?cc => set (vd := vv) in *; set (cvd := cc) in * end.
  destruct HCOPY as (VW & VH & VD & VWPL & VDATA & VCMZ & VCM).
  pose proof (VCMZ PCM0) as VDC0.
  pose proof POBJ1 as (PXD & (PDIN & PD0 & PD16 & _) & (HDd & HWd & HHd & HWPLd & HRSd) & DATd & _).
  destruct DATd as [DZ|((DIN & DA0 & DA16 & DAN) & DNE)]; [contradiction|].
  unfold pix_cells in PXD. unfold rsize in *.
  set (dat := p_data vd) in *. set (rs := 4 * (p_wpl vd * p_h vd)) in *.
  unfold pm_copy_live, rsize in LVH. rewrite VDC0 in LVH. cbn [Z.eqb app] in LVH. fold dat in LVH. fold rs in LVH.
  lazymatch goal with A : ART RT ?S1 ?mm |- cps _ (ASTA RT ?S1 _ _) _ =>
    assert (SUB01 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S1)) by (intros e He; rewrite LVH; right; right; exact He);
    assert (NCD : forall a, PF a -> a < dat \/ dat + rs <= a)
      by (intros a Ha; apply (fresh_chunk_apart RT AF S1 mm [] dat rs ((pixd, 64) :: rt_live RT Σ) (rt_frames RT S1) usp a A LVH eq_refl);
          [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul| apply (aclient_mono _ _ usp _ _ usp _ Ha); [intros e He; right; exact He| solve [frames_sub_tac]| lia]]);
    assert (NEQDP : dat + rs <= pixd \/ pixd + 64 <= dat) by (apply (live_apart2 RT AF S1 mm dat rs pixd 64 A DIN PDIN DNE))
  end.
  park LVH.
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 32, usp)] [0x9a3e0; 0x669cc; 0x96a88].
  repeat (shbr_inv8m; awalk [0x9a3e0; 0x669cc; 0x96a88]).
  assert (WPLBd : 0 < p_wpl vd <= 20001) by (rewrite HWPLd; clear - HDd HWd; cbn in HDd; Z.div_mod_to_equations; nia).
  rewrite ?(zx32_small (p_wpl vd)), ?(zx32_small (p_h vd)) by lia.
  rewrite ?(unsigned_lit (p_wpl vd)), ?(unsigned_lit (p_h vd)) by lia.
  rewrite ?(Z.mod_small (p_wpl vd * 4)) by lia.
  try (replace (p_wpl vd * 4 * p_h vd) with rs by (unfold rs; lia)).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm))) _ =>
    pose proof (af_acc_live RT AF S mm dat rs A DIN) as (WRD & ACCD) end.
  eapply cps_seq.
  { pose proof (fk_asan_memset RT FKC) as MS0; unfold memset_icontractF in MS0; eapply MS0 with (lo := lo) (d := dat) (n := rs) (c := Z_to_bv 8 0); rt_side idtac.
    all: lazymatch goal with
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ =>
             f_equal; unfold zx32; rewrite ?unsigned_lit by lia; rewrite ?(Z.mod_small _ (2^32)) by lia; rewrite ?Z.mod_small by lia; unfold rs; lia
         | |- (0 <= _ <= _) => change (2^47) with 140737488355328; lia
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by lia; split; [intros _; split; [exact ACCD| left; exists dat, rs; split; [exact DIN| lia]]|];
             split; [intros i Hi; right; right; left; exists dat, rs; split; [exact DIN| lia]| exact WRD]
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                   [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (SUB01 e He)| solve [frames_sub_tac]| lia]|
                                 pose proof (NCD _ Hx); lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 32, usp)] (@nil Z).
  cps_stop.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?SF _ _ _ => exists SF, pixd, vd end.
  split.
  2:{ unpark LVH. split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; unfold pix_new_live, rsize; reflexivity|]. clear LVH. alg_tac. }
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
  split; [split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity| cbn [ms_fregs MS]; fs_agree_tac]|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
  split; [intros a Ha _; apply AGF; exact Ha|].
  split.
  { apply (pix_obj_rc_mono (rt_live RT Σ)); [exact SUB01|].
    lazymatch goal with |- pix_obj_rc _ ?mf _ _ _ _ => exact (pix_obj_rc_keep_all _ m mf pix v _ rc POS (keeps_live_of_agf _ _ _ _ _ AGF)) end. }
  split; [exact PNZ|].
  split.
  { split; [| split; [rewrite VD; exact PD8| split; [exact VDC0| exact VDATA]]].
    lazymatch type of POBJ1 with pix_obj ?lv1 ?ma _ _ _ => lazymatch type of PXD with rw_cells _ ?mb _ _ =>
      pose proof (pix_obj_retarget lv1 lv1 ma mb pixd vd vd cvd POBJ1 PXD eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                    (fun e He => He) (fun CNZ => False_ind _ (CNZ VDC0))) as POBJ2 end end.
    destruct POBJ2 as (Q1 & Q2 & Q3 & Q4 & _).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4| left; exact VDC0]. }
  split; [exact VW| exact VH].
Qed.
End PIXTEMPLATE.
