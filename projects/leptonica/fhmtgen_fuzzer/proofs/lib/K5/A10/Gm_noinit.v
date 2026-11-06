(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Gm_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition NI_FLAG_LOAD : Z := 0x91e00.
Definition NI_FLAG_DONE : Z := 0x91e08.

Lemma ni_traces_ra_lo : Forall (Forall (fun x => 4096 <= x)) CLIENT_TRACES.
Proof.
  apply Forall_forall. intros t Ht. apply Forall_forall. intros x Hx.
  assert (B : forallb (fun t => forallb (fun x => 4096 <=? x) t) CLIENT_TRACES = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B t Ht). rewrite forallb_forall in B. specialize (B x Hx). apply Z.leb_le in B. exact B.
Qed.

Section NOINIT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis HDRS : pixCreateHeader_sure_cps RT.
Hypothesis PAD : pixSetPadBits_cps RT.

Theorem pixCreateNoInit_sure_ok : pixCreateNoInit_sure_cps RT.
Proof using AF RC GP HDRS PAD.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo w h d ras
    FDO MST -> (WR & ->) (HR & ->) (DR & ->) HOKA UCTX TRM ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). unfold uctx in UCTX.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (RALO : 4096 <= bv_unsigned ra).
  { pose proof ni_traces_ra_lo as TLO. rewrite Forall_forall in TLO. specialize (TLO _ TRM).
    apply Forall_inv_tail in TLO. apply Forall_inv in TLO. exact TLO. }
  pose proof (bv_unsigned_in_range 64 ra) as RRA. pose proof (bv_unsigned_in_range 64 s0) as RS0.
  unfold bv_modulus in RRA, RS0. change (2 ^ Z.of_N 64) with (2^64) in RRA, RS0.
  unfold entry_st, e_pixCreateNoInit, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, RASTER_COST, NI_FLAG_LOAD, NI_FLAG_DONE in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof HDRS as HD. unfold pixCreateHeader_sure_cps in HD.
  pose proof PAD as PD. unfold pixSetPadBits_cps in PD.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)

    carve_frame 96%nat ST.
    Time walk_to AF MST [(usp - 96, usp)] [0x4bf48; 0x91ed4; 0x62678; 0x95ec8; 0x91420; 0x62674].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact Ha).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]
                 [0x4bf48; 0x91ed4; 0x62678; 0x95ec8; 0x91420; 0x62674].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { eapply HD with (lo := lo) (w := w) (h := h) (d := d); rt_side idtac.
      all: lazymatch goal with
           | |- s32 _ _ => split; [lia| reflexivity]
           | |- hdr_args_ok _ _ _ => exact HOKA
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with H : pix_obj _ _ ?p ?vv _ |- _ => rename H into POBJ; set (pix := p) in *; set (v := vv) in * end.
    lazymatch goal with H : rt_live RT _ = (pix, 64) :: _ |- _ => rename H into LVH end.
    lazymatch goal with H : p_w v = w |- _ => rename H into VW end.
    lazymatch goal with H : p_h v = h |- _ => rename H into VH end.
    lazymatch goal with H : p_d v = d |- _ => rename H into VD end.
    lazymatch goal with H : p_data v = 0 |- _ => rename H into VDATA end.
    lazymatch goal with H : p_cmap v = 0 |- _ => rename H into VCMAP end.
    destruct POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & _ & _).
    chunk_facts RT AF GP pix 64.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (NCP : forall a, PF a -> a < pix \/ pix + 64 <= a)
        by (intros a Ha; apply (new_chunk_apart RT AF S mm pix 64 (rt_live RT Σ) (rt_frames RT S) usp a A);
            [ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity | reflexivity
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | apply (aclient_mono _ _ usp _ _ usp _ Ha); [auto| solve [frames_sub_tac]| lia] ]) end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSh : rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ)
        by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
    fframe_chunk RT AF fr 0%nat 64 pix 64. norm_fshadow.
    assert (WPLB : 0 < p_wpl v <= 20001) by (rewrite HWPL; clear - HD1 HW1; cbn in HD1; Z.div_mod_to_equations; nia).
    unfold pix_cells in PXC.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]
                 [0x4bf48; 0x91ed4; 0x62678; 0x95ec8; 0x91420; 0x62674; 0x91e00].
    pose proof FR as FRrec. split_at FRrec 10%nat FRrec2. split_at FRrec2 2%nat FRrest. clear FRrec FRrest.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { pose proof (gp_malloc RT GP) as MC; unfold malloc_contractC in MC; eapply MC with (lo := lo) (n := 4 * (p_wpl v * p_h v)); rt_side idtac.
      all: lazymatch goal with
           | |- (1 <= _ <= _) => clear - HRS; lia
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ =>
               f_equal; rewrite (sx32_small (p_wpl v)) by lia; rewrite unsigned_lit by lia; rewrite <- VH;
               rewrite Z.mod_small by (clear - WPLB HH1; nia); lia
           | |- (Z.of_nat _ < LIVE_MAX) =>
               repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold LIVE_MAX in *; lia
           | |- (mcost _ <= _) => unfold mcost; destruct (_ <=? _); lia
           | |- unwind_okC _ _ _ _ =>
               exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by ul; split; [| exact TRM];
               apply (chain_ok_push _ (usp + -96) usp (bv_unsigned ra) (bv_unsigned s0) ras);
                 [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | lia | lia
                 | rewrite !Z_to_bv_bv_unsigned; exact FRrec2 | ];
               apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCTX);
               eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
    lazymatch goal with H : rt_live RT ?S = (?p, 4 * (p_wpl v * p_h v)) :: _ |- _ => rename H into LVD; set (dat := p) in * end.
    set (rs := 4 * (p_wpl v * p_h v)) in *.
    chunk_facts RT AF GP dat rs. chunk_facts RT AF GP pix 64.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSm : rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ)
        by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
    fframe_chunk RT AF fr 0%nat 64 dat rs. norm_fshadow.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (NCDAT : forall a, PF a -> a < dat \/ dat + rs <= a)
        by (intros a Ha; apply (new_chunk_apart RT AF S mm dat rs ((pix, 64) :: rt_live RT Σ) (rt_frames RT S) usp a A);
            [ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity | reflexivity
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | apply (aclient_mono _ _ usp _ _ usp _ Ha); [intros e He; right; exact He| solve [frames_sub_tac]| lia] ]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (pix, pix + 64)]
                 [0x4bf48; 0x91ed4; 0x62678; 0x95ec8; 0x91420; 0x62674; 0x91e00].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                          split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        pose proof (NCP _ Hx); repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (NCD : dat + rs <= pix \/ pix + 64 <= dat)
        by (apply (af_live_disj RT AF S mm dat rs pix 64 [] _ A LVD); cbn [app];
            repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; left; reflexivity) end.
    eapply cps_seq.
    { eapply PD with (lo := lo) (pix := pix) (cv := mkCmapv 0 0 0 0)
        (v := mkPixv (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_xres v) (p_yres v) (p_inf v) (p_spec v) (p_cmap v) dat); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ =>
               unfold pix_obj, pix_cells, chunk, pix_hdr_ok, rsize;
               cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
               split; [exact PXC|]; split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| lia]]]|];
               split; [split; [exact HD1| unfold rs in *; repeat split; first [assumption | lia]]|];
               split; [right; split; [split; [rewrite LVD; left; reflexivity| split; [lia| split; [assumption| unfold rs; lia]]]| lia]| left; exact VCMAP]
           | |- (_ <> 0) => cbn [p_data]; lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]|
                                   cbn [outside]; split; [pose proof (NCDAT _ Hx); lia| exact I]]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]
                 [0x4bf48; 0x91ed4; 0x62678; 0x95ec8; 0x91420; 0x62674; 0x91e00].
    frame_release RT AF GP MST Σ fr 0%nat 64 PF AGF PFS usp lo 0x91e08
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 96, usp)] (@nil Z).
    cps_stop.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ =>
      exists S, pix, (mkPixv (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_xres v) (p_yres v) (p_inf v) (p_spec v) (p_cmap v) dat) end.
    split.
    2:{ unfold rsize. cbn [p_data p_wpl p_h]. alg_tac. }
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end. }
    split; [intros a Ha _; apply AGF; exact Ha|].
    cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data].
    split; [| repeat split; first [assumption | lia]].
    unfold pix_obj, pix_cells, chunk, pix_hdr_ok, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data].
    split; [exact PXC|].
    split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| lia]]]|].
    split; [split; [exact HD1| unfold rs in *; repeat split; first [assumption | lia]]|].
    split; [right; split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| unfold rs; lia]]]| unpark_all; lia]| left; exact VCMAP].

  -

    carve_frame 112%nat ST.
    Time walk_to AF MST [(usp - 112, usp)] [0x4bf48; 0x91ed4; 0x62678; 0x95ec8; 0x91420; 0x62674].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact Ha).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 112, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]
                 [0x4bf48; 0x91ed4; 0x62678; 0x95ec8; 0x91420; 0x62674].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { eapply HD with (lo := lo) (w := w) (h := h) (d := d); rt_side idtac.
      all: lazymatch goal with
           | |- s32 _ _ => split; [lia| reflexivity]
           | |- hdr_args_ok _ _ _ => exact HOKA
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with H : pix_obj _ _ ?p ?vv _ |- _ => rename H into POBJ; set (pix := p) in *; set (v := vv) in * end.
    lazymatch goal with H : rt_live RT _ = (pix, 64) :: _ |- _ => rename H into LVH end.
    lazymatch goal with H : p_w v = w |- _ => rename H into VW end.
    lazymatch goal with H : p_h v = h |- _ => rename H into VH end.
    lazymatch goal with H : p_d v = d |- _ => rename H into VD end.
    lazymatch goal with H : p_data v = 0 |- _ => rename H into VDATA end.
    lazymatch goal with H : p_cmap v = 0 |- _ => rename H into VCMAP end.
    destruct POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & _ & _).
    chunk_facts RT AF GP pix 64.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (NCP : forall a, PF a -> a < pix \/ pix + 64 <= a)
        by (intros a Ha; apply (new_chunk_apart RT AF S mm pix 64 (rt_live RT Σ) (rt_frames RT S) usp a A);
            [ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity | reflexivity
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | apply (aclient_mono _ _ usp _ _ usp _ Ha); [auto| solve [frames_sub_tac]| lia] ]) end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSh : rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ)
        by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
    fframe_chunk RT AF fr 0%nat 64 pix 64. norm_fshadow.
    assert (WPLB : 0 < p_wpl v <= 20001) by (rewrite HWPL; clear - HD1 HW1; cbn in HD1; Z.div_mod_to_equations; nia).
    unfold pix_cells in PXC.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 112, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]
                 [0x4bf48; 0x91ed4; 0x62678; 0x95ec8; 0x91420; 0x62674; 0x91e00].
    pose proof FR as FRrec. split_at FRrec 12%nat FRrec2. split_at FRrec2 2%nat FRrest. clear FRrec FRrest.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { pose proof (gp_malloc RT GP) as MC; unfold malloc_contractC in MC; eapply MC with (lo := lo) (n := 4 * (p_wpl v * p_h v)); rt_side idtac.
      all: lazymatch goal with
           | |- (1 <= _ <= _) => clear - HRS; lia
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ =>
               f_equal; rewrite (sx32_small (p_wpl v)) by lia; rewrite unsigned_lit by lia; rewrite <- VH;
               rewrite Z.mod_small by (clear - WPLB HH1; nia); lia
           | |- (Z.of_nat _ < LIVE_MAX) =>
               repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold LIVE_MAX in *; lia
           | |- (mcost _ <= _) => unfold mcost; destruct (_ <=? _); lia
           | |- unwind_okC _ _ _ _ =>
               exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by ul; split; [| exact TRM];
               apply (chain_ok_push _ (usp + -112) usp (bv_unsigned ra) (bv_unsigned s0) ras);
                 [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | lia | lia
                 | rewrite !Z_to_bv_bv_unsigned; exact FRrec2 | ];
               apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCTX);
               eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
    lazymatch goal with H : rt_live RT ?S = (?p, 4 * (p_wpl v * p_h v)) :: _ |- _ => rename H into LVD; set (dat := p) in * end.
    set (rs := 4 * (p_wpl v * p_h v)) in *.
    chunk_facts RT AF GP dat rs. chunk_facts RT AF GP pix 64.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSm : rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ)
        by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
    fframe_chunk RT AF fr 0%nat 64 dat rs. norm_fshadow.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (NCDAT : forall a, PF a -> a < dat \/ dat + rs <= a)
        by (intros a Ha; apply (new_chunk_apart RT AF S mm dat rs ((pix, 64) :: rt_live RT Σ) (rt_frames RT S) usp a A);
            [ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity | reflexivity
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | apply (aclient_mono _ _ usp _ _ usp _ Ha); [intros e He; right; exact He| solve [frames_sub_tac]| lia] ]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 112, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (pix, pix + 64)]
                 [0x4bf48; 0x91ed4; 0x62678; 0x95ec8; 0x91420; 0x62674; 0x91e00].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                          split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        pose proof (NCP _ Hx); repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (NCD : dat + rs <= pix \/ pix + 64 <= dat)
        by (apply (af_live_disj RT AF S mm dat rs pix 64 [] _ A LVD); cbn [app];
            repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; left; reflexivity) end.
    eapply cps_seq.
    { eapply PD with (lo := lo) (pix := pix) (cv := mkCmapv 0 0 0 0)
        (v := mkPixv (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_xres v) (p_yres v) (p_inf v) (p_spec v) (p_cmap v) dat); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ =>
               unfold pix_obj, pix_cells, chunk, pix_hdr_ok, rsize;
               cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
               split; [exact PXC|]; split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| lia]]]|];
               split; [split; [exact HD1| unfold rs in *; repeat split; first [assumption | lia]]|];
               split; [right; split; [split; [rewrite LVD; left; reflexivity| split; [lia| split; [assumption| unfold rs; lia]]]| lia]| left; exact VCMAP]
           | |- (_ <> 0) => cbn [p_data]; lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]|
                                   cbn [outside]; split; [pose proof (NCDAT _ Hx); lia| exact I]]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 112, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]
                 [0x4bf48; 0x91ed4; 0x62678; 0x95ec8; 0x91420; 0x62674; 0x91e00].
    frame_release RT AF GP MST Σ fr 0%nat 64 PF AGF PFS usp lo 0x91e08
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 112, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -112) |- _ => release_frame FR ST' usp end.
    cps_stop.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ =>
      exists S, pix, (mkPixv (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_xres v) (p_yres v) (p_inf v) (p_spec v) (p_cmap v) dat) end.
    split.
    2:{ unfold rsize. cbn [p_data p_wpl p_h]. alg_tac. }
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end. }
    split; [intros a Ha _; apply AGF; exact Ha|].
    cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data].
    split; [| repeat split; first [assumption | lia]].
    unfold pix_obj, pix_cells, chunk, pix_hdr_ok, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data].
    split; [exact PXC|].
    split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| lia]]]|].
    split; [split; [exact HD1| unfold rs in *; repeat split; first [assumption | lia]]|].
    split; [right; split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| unfold rs; lia]]]| unpark_all; lia]| left; exact VCMAP].

Qed.
End NOINIT.
