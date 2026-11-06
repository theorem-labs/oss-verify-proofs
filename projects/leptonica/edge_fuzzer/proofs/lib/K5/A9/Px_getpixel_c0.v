(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_gmax_defs Ed_iface Px_defs Px_getpixel_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section GPC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Lemma getpixel_c0 : getpixel_case RT 0.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix pval x y v cv old
    FDO MST -> -> [XR ->] [YR ->] -> POBJ D1 VDATA OPM PMC ENV RES AL.
  unfold lpost, lenv, keeps, keepsL, lres, optrF in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). destruct OPM as (OWNF & PM0 & PM8 & PMSH & PMSEG).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixGetPixel, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, GETPIXEL_COST in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF0 := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pval, pval + 4)] a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (OWN : accok (rt_live RT Σ) (rt_frames RT Σ) m pval 4) by (right; exact OWNF).
  assert (PMCL : forall zz, pval <= zz < pval + 4 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp zz)
    by (intros zz Hzz; exact (accok_aclient _ _ m usp pval 4 zz OWN Hzz)).
  assert (PMFF : forall zz, pval <= zz < pval + 4 -> in_fframe (rt_frames RT Σ) zz)
    by (intros zz Hzz; destruct OWNF as (f & k & Hin & H1 & H2 & _); exists f, k; split; [exact Hin| lia]).
  assert (PMLO : pval + 4 <= lo).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _).
    pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN in R. lia. }
  assert (PMP : pval + 4 <= pix \/ pix + 64 <= pval).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). specialize (R pix 64 PIN). lia. }
  assert (PMD : pval + 4 <= p_data v \/ p_data v + rsize v <= pval).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). specialize (R (p_data v) (rsize v) DIN). lia. }
  chunk_facts RT AF GP pix 64.
  chunk_facts RT AF GP (p_data v) (rsize v).
  unfold pix_cells in PXC.
  pose proof (af_acc_live RT AF Σ m (p_data v) (rsize v) ART0 DIN) as (WRD & _).
  unfold rsize in *. apply wr_at_rw_CB in WRD; [| lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL.
  pose proof DBC as DBC0. hide DBC0.
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a).
  { intros q k a Hq Ha. split; [right; right; left; exists q, k; split; [exact Hq| lia]|]. cbn [outside]. split; [| exact I].
    destruct OWNF as (f & kf & Hin & H1 & H2 & _).
    pose proof (af_frames_range RT AF Σ m f kf ART0 Hin) as (_ & _ & _ & R). specialize (R q k Hq). lia. }
  hide POBJ.
  carve_frame 160%nat ST.
  walk_to AF MST [(usp - 160, usp)] [e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF0 (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
  park OWNF.
  fframe_chunk RT AF fr 1%nat 128 pix 64.
  fframe_chunk RT AF fr 1%nat 128 (p_data v) (4 * (p_wpl v * p_h v)).
  fframe_optr RT AF fr 1%nat 128 OWN usp. park OWN.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 160, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xf5580].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    unpark_accok_munch OWN MUx (rt_live RT Σ) (rt_frames RT Σ) usp
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH. local_acc FSH fr 8%nat 64 FR64 FR1 ACCDP.
  assert (AGF1 : agree_on PF m _) by (eapply agree_sub; [exact AGF| intros zz [Hz _]; exact Hz]). clear AGF. rename AGF1 into AGF.
  park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pval, pval + 4)]
               [e_stack_malloc 1%nat; 0xf577c; 0xf56a0].
  sx32_fix.
  rewrite (sx32_small (p_w v)) in FRM by lia. rewrite (sx32_small (p_h v)) in FRM by lia. rewrite D1 in FRM.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) in FRM by (apply bv_eq; vm_compute; reflexivity).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with MIx : mem_inv asegs mm |- _ => pose proof (jt_getpixel mm MIx) as JT end end.
  unfold JT_GETPIXEL, JT_GETPIXEL_0 in JT.
  assert (CASES : (0 <= x < p_w v /\ 0 <= y < p_h v) \/ ~ (0 <= x < p_w v /\ 0 <= y < p_h v)) by lia.
  destruct CASES as [[[INX0 INX1] [INY0 INY1]]|OUTP].
  - (* [comment removed for export] *)
    awalk [e_stack_malloc 1%nat; 0xf577c; 0xf56a0; 0xf58d0].
    sx32_fix. awalk [e_stack_malloc 1%nat; 0xf577c; 0xf56a0; 0xf58d0].
    sx32_fix. awalk [e_stack_malloc 1%nat; 0xf577c; 0xf56a0; 0xf58d0].
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
    match goal with |- context [Z_to_bv 64 (?e + 202956)] => let vv := eval vm_compute in (e + 202956) in change (e + 202956) with vv end.
    sx32_fix. awalk [e_stack_malloc 1%nat; 0xf577c; 0xf56a0; 0xf58d0].
    replace (sx32 (Z_to_bv 64 802156)) with (Z_to_bv 64 802156) by (apply bv_eq; vm_compute; reflexivity).
    change (bv_unsigned (Z_to_bv 64 802156) + 202956) with 1005112.
    rewrite (ret_pc_even 1005112) by (first [lia | reflexivity]).
    assert (XW : x / 32 + 1 <= p_wpl v) by (rewrite HWPL, D1; clear - INX0 INX1; Z.div_mod_to_equations; lia).
    assert (WY : 0 <= p_wpl v * y /\ p_wpl v * y + p_wpl v <= p_wpl v * p_h v) by (clear - INY0 INY1 XW INX0; nia).
    swrap32_fix.
    rewrite (Z.mod_small (p_wpl v * y) 18446744073709551616) by lia.
    awalk [e_stack_malloc 1%nat; 0xf577c; 0xf56a0; 0xf58d0].
    rewrite (srliw_idx x 32) by lia.
    awalk [e_stack_malloc 1%nat; 0xf577c; 0xf56a0; 0xf58d0].
    (* [comment removed for export] *)
    set (kw := p_wpl v * y + x / 32).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with DBCx : rw_cells asegs mm (p_data v) [CB _ dbs] |- _ =>
        pose proof (raster_read mm (p_data v) dbs kw (Z_to_bv 64 (p_data v + p_wpl v * y * 4 + x / 32 * 4))
                      (proj1 (u8arr_of_rw_cells asegs mm _ _ _ DBCx)) ltac:(unfold kw; lia) ltac:(rewrite DBL; unfold kw; lia)
                      ltac:(unfold kw, wa; f_equal; lia)) as RD end end.
    pose proof (raster_word_range dbs kw) as WDR. set (wd := raster_word dbs kw) in *.
    awalk [e_stack_malloc 1%nat; 0xf577c; 0xf56a0; 0xf58d0].
    clear RD.
    rewrite (getbit_eq wd x WDR ltac:(lia)).
    set (b := Z.b2z (Z.testbit (bv_unsigned wd) (31 - x mod 32))).
    assert (B01 : b = 0 \/ b = 1) by (subst b; destruct (Z.testbit _ _); cbn; lia).
    (* [comment removed for export] *)
    awalk [e_stack_malloc 1%nat; 0xf577c; 0xf56a0].
    awalk [e_stack_malloc 1%nat; 0xf56a0; 0xf57e8].
    frame_release_w RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xf57e8
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; apply (aclient_mono _ _ usp _ _ _ _ (PMCL zz Hzz)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); destruct (NFA _ (proj1 Hx)) as [N1 N2]; destruct Hx as [_ HxO];
                        cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN =>
                assert (FLPM : fl < pval \/ pval + 4 <= fl)
                  by (destruct (Z_lt_ge_dec fl pval) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (pval + 4)) as [FG2|]; [| right; lia];
                      exfalso; apply FLN; right; right; right; left; destruct (PMFF fl ltac:(lia)) as (f0 & k0 & Hin0 & Hr0); exists f0, k0;
                      split; [| exact Hr0]; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; right; exact Hin0)).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 160, usp)] (@nil Z).
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, b end.
    split; [| alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    assert (RV : getpixel_ret v x y = 0).
    { unfold getpixel_ret, in_pixb. destruct (Z.leb_spec 0 x); destruct (Z.ltb_spec x (p_w v)); destruct (Z.leb_spec 0 y); destruct (Z.ltb_spec y (p_h v)); cbn; lia. }
    rewrite RV.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
    split.
    { repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. intros a Ha Ho; exact (AGF a (conj Ha Ho)). }
    split; [lazymatch goal with PMCx : rw_cells asegs _ pval _ |- _ => exact PMCx end|].
    split.
    { intros _. exists wd. split; [| reflexivity]. unfold hid in DBC0. unfold pixel_word_addr.
      replace (p_data v + 4 * (y * p_wpl v + x / 32)) with (p_data v + 4 * kw) by (unfold kw; lia).
      apply (raster_cell m (p_data v) _ dbs kw DBC0); [unfold kw; lia| unfold kw; lia]. }
    split. { intros NI. exfalso. apply NI. unfold in_pix. lia. }
    exact B01.
  - (* [comment removed for export] *)
    lazymatch goal with
    | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
      eapply (evt_cut segs (fun ms' => exists ua ub : word,
         ms' = MS (@bvmap_set 5 word (Z_to_bv 5 11) ua (@bvmap_set 5 word (Z_to_bv 5 12) ub
                 (@bvmap_set 5 word (Z_to_bv 5 24) (Z_to_bv 64 fr) (@bvmap_set 5 word (Z_to_bv 5 10) (Z_to_bv 64 2) R)))) F (Z_to_bv 64 0xf577c) fc rv mm ro));
      [ | let ms := fresh "ms" in let E := fresh "E" in intros ms (ua & ub & E); subst ms; norm_regset ]
    end.
    { destruct (Z_lt_ge_dec x 0) as [CX0|CX0].
      - brT. awalk [0xf577c]. apply evt_done; do 2 eexists; norm_regset; reflexivity.
      - brF. awalk [0xf577c; 0xf56a0]. destruct (Z_lt_ge_dec y 0) as [CY0|CY0].
        + brT. awalk [0xf577c]. apply evt_done; do 2 eexists; norm_regset; reflexivity.
        + brF. awalk [0xf577c; 0xf56a0]. sx32_fix. destruct (Z_lt_ge_dec x (p_w v)) as [CXW|CXW].
          * brF. awalk [0xf577c; 0xf56a0]. sx32_fix. brT. awalk [0xf577c]. apply evt_done; do 2 eexists; norm_regset; reflexivity.
          * brT. awalk [0xf577c]. apply evt_done; do 2 eexists; norm_regset; reflexivity. }
    awalk [e_stack_malloc 1%nat; 0xf56a0; 0xf57e8].
    frame_release_w RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xf57e8
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; apply (aclient_mono _ _ usp _ _ _ _ (PMCL zz Hzz)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); destruct (NFA _ (proj1 Hx)) as [N1 N2]; destruct Hx as [_ HxO];
                        cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN =>
                assert (FLPM : fl < pval \/ pval + 4 <= fl)
                  by (destruct (Z_lt_ge_dec fl pval) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (pval + 4)) as [FG2|]; [| right; lia];
                      exfalso; apply FLN; right; right; right; left; destruct (PMFF fl ltac:(lia)) as (f0 & k0 & Hin0 & Hr0); exists f0, k0;
                      split; [| exact Hr0]; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; right; exact Hin0)).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 160, usp)] (@nil Z).
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, 0 end.
    split; [| alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    assert (RV : getpixel_ret v x y = 2).
    { unfold getpixel_ret, in_pixb. destruct (Z.leb_spec 0 x); destruct (Z.ltb_spec x (p_w v)); destruct (Z.leb_spec 0 y); destruct (Z.ltb_spec y (p_h v)); cbn; lia. }
    rewrite RV.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
    split.
    { repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. intros a Ha Ho; exact (AGF a (conj Ha Ho)). }
    split; [lazymatch goal with PMCx : rw_cells asegs _ pval _ |- _ => exact PMCx end|].
    split. { intros IP. exfalso. apply OUTP. exact IP. }
    split; [intros _; reflexivity| left; reflexivity].
Qed.

End GPC.
