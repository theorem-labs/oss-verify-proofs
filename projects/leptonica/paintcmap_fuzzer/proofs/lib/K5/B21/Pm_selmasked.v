(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_iface Pm_kit Pm_walkkit Pm_getters LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section SELMASKED.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis LSE : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorInt.
Hypothesis GCM : pixGetColormap_cps RT.

Theorem pixSetSelectMaskedCmap_ok : pixSetSelectMaskedCmap_cps RT.
Proof using AF RC GP LSE RERR GCM.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv
    FDO MST -> -> -> POBJ ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixSetSelectMaskedCmap, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)
    carve_frame 192%nat ST.
    walk_to AF MST [(usp - 192, usp)] [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & _).
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (PINS : In (pix, 64) (rt_live RT S)) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact PIN) end.
    chunk_facts RT AF GP pix 64.
    walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                 [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
    lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (KL1 : keeps_live (rt_live RT S) m0 m1)
        by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -192) A ltac:(rewrite FRS; left; reflexivity)
                     ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end.
    repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in KL1 end.
    lazymatch type of KL1 with keeps_live _ ?ma ?mb =>
      assert (KL0 : keeps_live (rt_live RT Σ) m ma)
        by (intros bb kk Hin a Ha; apply AGF; right; right; left; exists bb, kk; split; [exact Hin| exact Ha]);
      pose proof (pix_obj_keep _ ma mb pix v cv KL1 (pix_obj_keep _ m ma pix v cv KL0 POBJ)) as POBJ1 end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof GCM as GC. unfold pixGetColormap_cps, getter_post in GC.
    eapply cps_seq.
    { eapply GC with (lo := lo) (pix := pix) (v := v) (cv := cv); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact POBJ1
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- ?g => idtac "LEFT-GC:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    destruct (Z.eq_dec (p_cmap v) 0) as [CZ|CNZ].
    + (* [comment removed for export] *)
      rewrite CZ in *.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
      at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
      pose proof RERR as RE. unfold returnError_cps in RE.
      eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
      after_call RT AF.
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
      frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x94c2c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 192, usp)] (@nil Z).
      try (lazymatch goal with ST' : stk asegs _ lo (usp + -192) |- _ => release_frame FR ST' usp end).
      cps_stop.
      lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
        lazymatch goal with
        | _ : ART RT S mf |- _ => idtac
        | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
            assert (ARTf : ART RT S mf)
              by (apply (art_client_writes RT AF S mm mf (usp + -192) W A MUx WMx);
                  [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
                  | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
        end end.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      eexists. split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
      intros a Ha _. apply AGF.
      lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
      exact Ha.
    + (* [comment removed for export] *)
      destruct POBJ1 as (_ & _ & _ & _ & [CZ0|((_ & (CIN & CM0 & _) & _) & _)]); [contradiction|].
      chunk_facts RT AF GP (p_cmap v) 24.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
      ds_msg_call RT AF GP LSE AGF PFS NFA usp lo [true].
      unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
      frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x94c2c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 192, usp)] (@nil Z).
      try (lazymatch goal with ST' : stk asegs _ lo (usp + -192) |- _ => release_frame FR ST' usp end).
      cps_stop.
      lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
        lazymatch goal with
        | _ : ART RT S mf |- _ => idtac
        | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
            assert (ARTf : ART RT S mf)
              by (apply (art_client_writes RT AF S mm mf (usp + -192) W A MUx WMx);
                  [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
                  | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
        end end.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      eexists. split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
      intros a Ha _. apply AGF.
      lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
      exact Ha.
  - (* [comment removed for export] *)
    carve_frame 208%nat ST.
    walk_to AF MST [(usp - 208, usp)] [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & _).
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (PINS : In (pix, 64) (rt_live RT S)) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact PIN) end.
    chunk_facts RT AF GP pix 64.
    walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                 [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
    lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (KL1 : keeps_live (rt_live RT S) m0 m1)
        by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -208) A ltac:(rewrite FRS; left; reflexivity)
                     ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end.
    repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in KL1 end.
    lazymatch type of KL1 with keeps_live _ ?ma ?mb =>
      assert (KL0 : keeps_live (rt_live RT Σ) m ma)
        by (intros bb kk Hin a Ha; apply AGF; right; right; left; exists bb, kk; split; [exact Hin| exact Ha]);
      pose proof (pix_obj_keep _ ma mb pix v cv KL1 (pix_obj_keep _ m ma pix v cv KL0 POBJ)) as POBJ1 end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof GCM as GC. unfold pixGetColormap_cps, getter_post in GC.
    eapply cps_seq.
    { eapply GC with (lo := lo) (pix := pix) (v := v) (cv := cv); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact POBJ1
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- ?g => idtac "LEFT-GC:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    destruct (Z.eq_dec (p_cmap v) 0) as [CZ|CNZ].
    + (* [comment removed for export] *)
      rewrite CZ in *.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
      at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
      pose proof RERR as RE. unfold returnError_cps in RE.
      eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
      after_call RT AF.
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
      frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x94c2c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 208, usp)] (@nil Z).
      try (lazymatch goal with ST' : stk asegs _ lo (usp + -208) |- _ => release_frame FR ST' usp end).
      cps_stop.
      lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
        lazymatch goal with
        | _ : ART RT S mf |- _ => idtac
        | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
            assert (ARTf : ART RT S mf)
              by (apply (art_client_writes RT AF S mm mf (usp + -208) W A MUx WMx);
                  [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
                  | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
        end end.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      eexists. split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
      intros a Ha _. apply AGF.
      lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
      exact Ha.
    + (* [comment removed for export] *)
      destruct POBJ1 as (_ & _ & _ & _ & [CZ0|((_ & (CIN & CM0 & _) & _) & _)]); [contradiction|].
      chunk_facts RT AF GP (p_cmap v) 24.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
      ds_msg_call RT AF GP LSE AGF PFS NFA usp lo [true].
      unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixGetColormap; e_returnErrorInt; e_lept_stderr; 0x94c24].
      frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x94c2c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 208, usp)] (@nil Z).
      try (lazymatch goal with ST' : stk asegs _ lo (usp + -208) |- _ => release_frame FR ST' usp end).
      cps_stop.
      lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
        lazymatch goal with
        | _ : ART RT S mf |- _ => idtac
        | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
            assert (ARTf : ART RT S mf)
              by (apply (art_client_writes RT AF S mm mf (usp + -208) W A MUx WMx);
                  [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
                  | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
        end end.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      eexists. split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
      intros a Ha _. apply AGF.
      lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
      exact Ha.
Qed.
End SELMASKED.
