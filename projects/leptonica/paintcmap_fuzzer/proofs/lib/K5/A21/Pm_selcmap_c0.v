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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_gaps_iface Pm_iface Pm_iface2 Pm_kit Pm_walkkit Pm_getters.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Pm_objkit Pm_selkit Pm_selcmap_defs Pm_selcmap_al.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section SELCMAP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis PG : pm_gaps RT.
Hypothesis LSE : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorInt.
Hypothesis GCM : pixGetColormap_cps RT.
Hypothesis GCNT : pixcmapGetCount_cps RT.
Hypothesis GIDX : pixcmapGetIndex_cps RT.
Hypothesis ADDC : pixcmapAddColor_cps RT.


(* [comment removed for export] *)
Definition selc_tail_stmt_0 : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
         (pix b : Z) (v : pixv) (cv : cmapv) (fr : Z),
    selc_ctx RT Σ PMc usp lo m pix b v -> selc_cut_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix b v cv fr.
Hypothesis TAIL : selc_tail_stmt_0.

Theorem selc_front_ok_0 : pixSetSelectCmap_cps_al RT 0.
Proof using AF RC GP PG LSE RERR GCM GCNT GIDX ADDC TAIL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix b v cv
    AL FDO MST -> -> -> -> -> -> -> POBJ DNZ BOBJ BNE ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixSetSelectCmap, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  (* [comment removed for export] *)
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  set (PFW := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside (pm_fp v cv) a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  (* [comment removed for export] *)
    carve_frame 192%nat ST.
    pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & _).
    chunk_facts RT AF GP pix 64.
    walk_to AF MST [(usp - 192, usp)] [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (pg_stack_malloc_2 RT PG) as SM2; unfold stack_malloc_2_contract in SM2; eapply SM2 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 2%nat 256 ltac:(fun Ha => exact Ha).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    idtac "PREFIX-DONE".
    (* [comment removed for export] *)
    fframe_chunk RT AF fr 2%nat 256 pix 64. norm_fshadow.
    walk_to AF MST [(usp - 192, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                 [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    idtac "T1-WALK".
    (* [comment removed for export] *)
    assert (LOW2 : forall S (mm : mem) slo q n a, ART RT S mm -> In (fr, 2%nat) (rt_frames RT S) -> rt_sp0 RT S - 8388608 <= slo ->
                   In (q, n) (rt_live RT S) -> q <= a < q + n ->
                   outside [(slo, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] a).
    { intros S mm slo q n a HA FIN SLO QIN Ha.
      pose proof (af_live_range RT AF S mm q n HA QIN) as (_ & R1 & _).
      pose proof (af_frames_range RT AF S mm fr 2%nat HA FIN) as (_ & _ & _ & FLV). specialize (FLV q n QIN).
      pose proof (af_fshadow_apart RT AF S mm fr 2%nat HA FIN) as (SA1 & _). specialize (SA1 q n QIN).
      change (fs_size 2) with 256 in *. unfold shad, SHB, STACK_WIN in *.
      cbn [outside]. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]. }
    idtac "T2-LOW2".
    lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (KL1 : keeps_live (rt_live RT S) m0 m1)
        by (intros bb kk Hin a Ha; apply MUx;
            apply (LOW2 S m0 (usp + -192) bb kk _ A ltac:(rewrite FRS; left; reflexivity)
                     ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia) Hin Ha)) end.
    repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in KL1 end.
    lazymatch type of KL1 with keeps_live _ ?ma ?mb =>
      assert (KL0 : keeps_live (rt_live RT Σ) m ma)
        by (intros bb kk Hin a Ha; apply AGF; right; right; left; exists bb, kk; split; [exact Hin| exact Ha]);
      pose proof (pix_obj_keep _ ma mb pix v cv KL1 (pix_obj_keep _ m ma pix v cv KL0 POBJ)) as POBJ1 end.
    idtac "T2-POBJ1".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    idtac "T3-ATCALL".
    pose proof GCM as GC. unfold pixGetColormap_cps, getter_post in GC.
    eapply cps_seq.
    { eapply GC with (lo := lo) (pix := pix) (v := v) (cv := cv); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact POBJ1
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- ?g => idtac "LEFT-GC:" g
           end. }
    after_call RT AF.
    (* [comment removed for export] *)
    lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      assert (KL2 : keeps_live (rt_live RT Σ) ma mb)
        by (intros bb kk Hin a Ha; apply AGx; split; [| exact I]; right; right; left; exists bb, kk;
            split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]);
      pose proof (pix_obj_keep _ ma mb pix v cv KL2 POBJ1) as POBJ2 end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    idtac "T3-AFTER".
    (* [comment removed for export] *)
    destruct (Z.eq_dec (p_cmap v) 0) as [CZ|CNZ].
    + (* [comment removed for export] *)
      rewrite CZ in *.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 192, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                   [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      pose proof RERR as RE. unfold returnError_cps in RE.
      eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
      idtac "T4-CALL".
      after_call RT AF.
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 192, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                   [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      idtac "T4-WALK".
    (* [comment removed for export] *)
      frame_release RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0x93980
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      idtac "T5-REL".
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
      idtac "T5-ART".
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      eexists. exists cv. split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
      idtac "T5-POST".
    (* [comment removed for export] *)
      assert (AGL : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> _ a = m a) by (intros a Ha; exact (AGF a Ha)).
      split; [| split; [| repeat split; reflexivity]].
      * intros a Ha _. apply AGL.
        lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
        exact Ha.
      * lazymatch goal with |- pix_obj ?lv ?mf _ _ _ =>
          replace lv with (rt_live RT Σ) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
          apply (pix_obj_keep _ m mf pix v cv); [| exact POBJ] end.
        intros bb kk Hin a Ha. apply AGL. right; right; left. exists bb, kk. split; [exact Hin| exact Ha].
    (* [comment removed for export] *)
    + (* [comment removed for export] *)
      pose proof POBJ2 as (PXC2 & _ & _ & _ & [CZ0|((_ & (CIN & CM0 & _) & _) & _)]); [contradiction|]. unfold pix_cells in PXC2.
      chunk_facts RT AF GP (p_cmap v) 24.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                   [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      idtac "T7-WALK".
    (* [comment removed for export] *)
      (* [comment removed for export] *)
      pose proof POBJ2 as (_ & _ & (DIN & _) & _).
      assert (DR : 0 <= p_d v < 2^31) by (cbn [In] in DIN; clear - DIN; lia).
      rewrite (sx32_small (p_d v)) by exact DR.
      brfork DBIG.
      idtac "T8-FORK".
      all: lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    (* [comment removed for export] *)
      1:{ (* [comment removed for export] *)
      awalk [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      pose proof RERR as RE. unfold returnError_cps in RE.
      eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
      idtac "L-CALL".
      after_call RT AF.
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 192, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                   [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      idtac "L-WALK".
      frame_release RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0x93980
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      idtac "L-REL".
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
      idtac "L-ART".
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      eexists. exists cv. split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
      idtac "L-POST".
      assert (AGL : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> _ a = m a) by (intros a Ha; exact (AGF a Ha)).
      split; [| split; [| repeat split; reflexivity]].
      - intros a Ha _. apply AGL.
        lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
        exact Ha.
      - lazymatch goal with |- pix_obj ?lv ?mf _ _ _ =>
          replace lv with (rt_live RT Σ) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
          apply (pix_obj_keep _ m mf pix v cv); [| exact POBJ] end.
        intros bb kk Hin a Ha. apply AGL. right; right; left. exists bb, kk. split; [exact Hin| exact Ha].
      }
      idtac "T9-END".
    (* [comment removed for export] *)
      awalk [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      idtac "T10-WALK".
    (* [comment removed for export] *)
      assert (D4 : p_d v = 1 \/ p_d v = 2 \/ p_d v = 4 \/ p_d v = 8) by (cbn [In] in DIN; clear - DIN DBIG; lia).
      lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        assert (EC : c = false) by (clear - D4; destruct D4 as [ -> | [ -> | [ -> | -> ] ] ]; vm_compute; reflexivity); rewrite EC; cbv iota; clear EC end.
      idtac "T11-MASK".
      awalk [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      idtac "T11-WALK".
    (* [comment removed for export] *)
      assert (CTX : selc_ctx RT Σ PMc usp lo m pix b v).
      { unfold selc_ctx.
        split; [exact FDO|]. split; [exact MST|]. split; [exact ART0|].
        do 6 (split; [first [assumption | clear - LOW LOR STa SPT SPA SPB; lia]|]).
        split; [exact LVP|]. split; [exact CNZ|]. split; [exact DNZ|]. split; [exact D4| exact BNE]. }
      idtac "CTX-DONE".
    (* [comment removed for export] *)
      lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        assert (KL3 : keeps_live (rt_live RT S) m0 m1)
          by (intros bb kk Hin a Ha; apply MUx;
              apply (LOW2 S m0 (usp + -256) bb kk _ A ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                       ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia) Hin Ha)) end.
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in KL3 end.
      lazymatch type of KL3 with keeps_live _ ?ma ?mb => pose proof (pix_obj_keep _ ma mb pix v cv KL3 POBJ2) as POBJ3 end.
      pose proof POBJ3 as (_ & _ & _ & _ & [CZ1|(COBJ3 & _)]); [contradiction|].
      idtac "T12-COBJ".
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      idtac "T12-ATCALL".
      pose proof GCNT as GN. unfold pixcmapGetCount_cps, getter_post in GN.
      eapply cps_seq.
      { eapply GN with (lo := lo) (cmap := p_cmap v) (cv := cv); rt_side idtac.
        all: lazymatch goal with
             | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact COBJ3
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- ?g => idtac "LEFT-GN:" g
             end. }
      after_call RT AF.
      lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
        assert (KL4 : keeps_live (rt_live RT Σ) ma mb)
          by (intros bb kk Hin a Ha; apply AGx; split; [| exact I]; right; right; left; exists bb, kk;
              split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]);
        pose proof (pix_obj_keep _ ma mb pix v cv KL4 POBJ3) as POBJ4 end.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
      idtac "T12-AFTER".
    (* [comment removed for export] *)
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                   [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      idtac "T13-WALK".
    (* [comment removed for export] *)
      assert (CNB : 0 <= c_n cv <= 256).
      { destruct COBJ3 as (_ & _ & _ & (CD & CNA & CNR) & _). cbn [In] in CD.
        assert (c_nalloc cv <= 256) by (rewrite CNA; destruct CD as [E|[E|[E|[E|[]]]]]; rewrite <- E; cbn; lia). lia. }
      brfork NSM.
      idtac "T14-FORK".
      all: lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    (* [comment removed for export] *)
      1:{ (* [comment removed for export] *)
      awalk [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      pose proof RERR as RE. unfold returnError_cps in RE.
      eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
      idtac "L-CALL".
      after_call RT AF.
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 192, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                   [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      idtac "L-WALK".
      frame_release RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0x93980
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      idtac "L-REL".
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
      idtac "L-ART".
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      eexists. exists cv. split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
      idtac "L-POST".
      assert (AGL : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> _ a = m a) by (intros a Ha; exact (AGF a Ha)).
      split; [| split; [| repeat split; reflexivity]].
      - intros a Ha _. apply AGL.
        lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
        exact Ha.
      - lazymatch goal with |- pix_obj ?lv ?mf _ _ _ =>
          replace lv with (rt_live RT Σ) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
          apply (pix_obj_keep _ m mf pix v cv); [| exact POBJ] end.
        intros bb kk Hin a Ha. apply AGL. right; right; left. exists bb, kk. split; [exact Hin| exact Ha].
      }
      idtac "T15-END".
    (* [comment removed for export] *)
      awalk [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      idtac "T16-WALK".
    (* [comment removed for export] *)
      (* [comment removed for export] *)
      split_last_CB FRM [104%nat; 4%nat; 116%nat].
      idtac "T17-SPLIT".
    (* [comment removed for export] *)
      lazymatch type of FRM with rw_cells _ ?mm _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: CB 4 ?bs :: ?post) =>
        destruct (cb4_c4_in mm fr [c1; c2; c3; c4] post bs FRM) as (xi & FRMx); clear FRM; cbn [app] in FRMx end.
      split_at FRMx 4%nat FRMI. split_at FRMI 1%nat FRMR.
      pose proof FSH as SHI. split_at SHI 16%nat SHI16. split_at SHI16 1%nat SHI17. clear SHI SHI17.
      idtac "T18-CELLS".
      (* [comment removed for export] *)
      lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        assert (KL5 : keeps_live (rt_live RT S) m0 m1)
          by (intros bb kk Hin a Ha; apply MUx;
              apply (LOW2 S m0 (usp + -256) bb kk _ A ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                       ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia) Hin Ha)) end.
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in KL5 end.
      lazymatch type of KL5 with keeps_live _ ?ma ?mb => pose proof (pix_obj_keep _ ma mb pix v cv KL5 POBJ4) as POBJ5 end.
      pose proof POBJ5 as (_ & _ & _ & _ & [CZ2|(COBJ5 & _)]); [contradiction|].
      idtac "T18-COBJ".
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      idtac "T18-ATCALL".
    (* [comment removed for export] *)
      pose proof GIDX as GI. unfold pixcmapGetIndex_cps in GI.
      eapply cps_seq.
      { eapply GI with (lo := lo) (cmap := p_cmap v) (pi := fr + 128) (cv := cv) (x := xi); rt_side idtac.
        all: lazymatch goal with
             | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact COBJ5
             | |- optrF _ _ _ _ _ =>
                 unfold optrF, own_frame, parked in *; split;
                 [ exists fr, 2%nat; split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity|];
                   change (fs_size 2) with 256;
                   split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                   split; [lia|]; split; [lia|];
                   replace (shad (fr + 128)) with (fr / 8 + 2147450896) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                   destruct SHI16 as [[_ B] _]; exact B
                 | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
             | |- rw_cells _ _ _ [C4 _] => exact FRMI
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- ?g => idtac "LEFT-GI:" g
             end. }
      idtac "T19-CALL".
    (* [comment removed for export] *)
      clear SHI16.
      after_call RT AF.
      idtac "T20-AFTER".
      lazymatch goal with AGx : agree_on _ ?ma ?mb, A : ART RT ?S0 ?ma |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
        assert (KL6 : keeps_live (rt_live RT Σ) ma mb)
          by (intros bb kk Hin a Ha;
              assert (HinS : In (bb, kk) (rt_live RT S0)) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin);
              pose proof (LOW2 S0 ma (usp + -256) bb kk _ A ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                            ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia) HinS Ha) as OUT;
              cbn [outside] in OUT; destruct OUT as (_ & OF & _);
              apply AGx; split; [right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]|];
              cbn [outside]; split; [clear - OF; lia| exact I]);
        pose proof (pix_obj_keep _ ma mb pix v cv KL6 POBJ5) as POBJ6 end.
      idtac "T20-POBJ6".
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                                     | cbn [outside]; destruct (NFA _ Hx) as [N1 _]; split; [clear - N1; lia| exact I]]).
      idtac "T20-FOLD".
    (* [comment removed for export] *)
      lazymatch goal with H : (?r = 0 /\ 0 <= ?i < c_n cv) \/ (?r = 1 /\ ?i = 0) |- _ => rename H into GIR; set (girv := r) in *; set (gii := i) in * end.
      lazymatch goal with H : rw_cells asegs _ (fr + 128) [C4 (Z_to_bv 64 gii)] |- _ => rename H into FRMI2 end.
      destruct GIR as [(GR0 & GIB)|(GR1 & GI0)].
      * (* [comment removed for export] *)
        rewrite GR0 in *.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                     [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978; 0x93504].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        idtac "C21-WALK".
    (* [comment removed for export] *)
        pose proof (TAIL Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix b v cv fr CTX) as CUT.
        idtac "C22-CUT".
        (* [comment removed for export] *)
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL7 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk2 RT AF S m0 m1 fr usp (usp + -256) A
                         ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end.
        repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in KL7 end.
        lazymatch type of KL7 with keeps_live _ ?ma ?mb => pose proof (pix_obj_keep _ ma mb pix v cv KL7 POBJ6) as POBJ7 end.
        idtac "C22-POBJ7".
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
        lazymatch goal with MUx : munch _ ?mm _ |- _ =>
          agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
        idtac "C22-AGF".
        (* [comment removed for export] *)
        pose proof BOBJ as (BXC0 & (INB & _)).
        lazymatch type of AGF with agree_on _ _ ?mc =>
          assert (BOBJc : box_obj (rt_live RT Σ) mc b 278 35 122 50)
            by (split; [| exact (proj2 BOBJ)];
                apply (keeps_live_cells (rt_live RT Σ) m mc b 20 b (box_cells 278 35 122 50)); [| exact INB| clear; lia| cbn; clear; lia| exact BXC0];
                intros bb kk Hin a Ha; apply AGF; right; right; left; exists bb, kk; split; [exact Hin| exact Ha]);
          assert (AGFW : agree_on PFW m mc) by (eapply agree_sub; [exact AGF| intros z [Hz _]; exact Hz]) end.
        idtac "C22-BOBJ".
        to_entry.
        unfold selc_cut_stmt_0 in CUT.
        lazymatch goal with |- cps ?sg ?P _ => change (cps sg P (selc_post RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv)) end.
        idtac "C22-CHANGE".
        eapply CUT with (cvx := cv) (idx := gii).
        all: lazymatch goal with
             | |- ART _ _ _ => eassumption
             | |- mem_inv _ _ => assumption
             | |- wmono _ _ _ => assumption
             | |- stk _ _ _ _ => eassumption
             | |- rw_cells _ _ _ (C8 _ :: CB 16 _ :: _) => exact FR
             | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; CB 104 _] => exact FRMx
             | |- rw_cells _ _ _ [C4 _] => exact FRMI2
             | |- rw_cells _ _ _ [CB 116 _] => exact FRMR
             | |- rw_cells _ _ _ (selc_fshadow _) => unfold selc_fshadow; exact FSH
             | |- LIBH _ => assumption
             | |- io_ssp _ => assumption
             | |- agree_on _ _ _ => exact AGFW
             | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
             | |- _ <= rt_credit RT ?Sb =>
                 first [ (repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; clear; lia)
                       | (lazymatch goal with CRx : rt_credit RT _ - _ <= rt_credit RT Sb |- _ =>
                            repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in CRx end; clear - CRx; lia end) ]
             | |- pix_obj _ _ _ _ _ => exact POBJ7
             | |- box_obj _ _ _ _ _ _ _ => exact BOBJc
             | |- _ = _ => reflexivity
             | |- _ <= _ <= _ => first [clear - GIB CNB; lia | clear - GIB CNB0 CNB1; lia | unfold parked in *; clear - GIB CNB0 CNB1; lia]
             | |- ?g => idtac "LEFTOVER:" g
             end.
    (* [comment removed for export] *)
      * (* [comment removed for export] *)
        rewrite GR1 in *.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                     [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        idtac "U21-WALK".
    (* [comment removed for export] *)
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL7 : keeps_live (rt_live RT S) m0 m1)
            by (intros bb kk Hin a Ha; apply MUx;
                apply (LOW2 S m0 (usp + -256) bb kk _ A ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia) Hin Ha)) end.
        repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in KL7 end.
        lazymatch type of KL7 with keeps_live _ ?ma ?mb => pose proof (pix_obj_keep _ ma mb pix v cv KL7 POBJ6) as POBJ7 end.
        pose proof POBJ7 as (_ & _ & _ & _ & [CZ3|(COBJ7 & _)]); [contradiction|].
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        idtac "U22-ATCALL".
    (* [comment removed for export] *)
        pose proof COBJ7 as (_ & _ & (AIN & ARR0 & ARR16 & _) & _ & _).
        chunk_facts RT AF GP (c_arr cv) (4 * c_nalloc cv).
        fframe_chunk RT AF fr 2%nat 256 (p_cmap v) 24. fframe_chunk RT AF fr 2%nat 256 (c_arr cv) (4 * c_nalloc cv).
        pose proof POBJ7 as (_ & _ & _ & _ & [CZ4|(_ & CNP & ANP & _ & _)]); [contradiction|].
        pose proof (live_apart RT AF Σ m (p_cmap v) 24 pix 64 ART0 CIN PIN CNP) as CPD.
        pose proof (live_apart RT AF Σ m (c_arr cv) (4 * c_nalloc cv) pix 64 ART0 AIN PIN ANP) as APD.
        idtac "N2-FACTS".
        pose proof ADDC as AC. unfold pixcmapAddColor_cps in AC.
        eapply cps_seq.
        { eapply AC with (lo := lo) (cmap := p_cmap v) (cv := cv); rt_side idtac.
          all: lazymatch goal with
               | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact COBJ7
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ => lres_tac
               | |- ?g => idtac "LEFT-AC:" g
               end. }
        idtac "N2-CALL".
        clear AC.
    (* [comment removed for export] *)
        park_disj.
        after_call RT AF.
        idtac "N3A-AFTER".
    (* [comment removed for export] *)
        (* [comment removed for export] *)
        pose proof BOBJ as (BXC0 & (INB & _)).
        assert (NA20 : 20 <> 4 * c_nalloc cv).
        { match goal with H : cmap_obj _ _ _ cv |- _ => pose proof H as (_ & _ & _ & (CD & CNA & _) & _) end.
          cbn [In] in CD. rewrite CNA. destruct CD as [E|[E|[E|[E|[]]]]]; rewrite <- E; cbn; lia. }
        idtac "N3X-FACTS".
    (* [comment removed for export] *)
        lazymatch goal with H : (?r = 0 /\ _ /\ _) \/ (?r = 1 /\ _ /\ _) |- _ => rename H into ACR; set (acrv := r) in * end.
        pose proof (pm_live_apart_sz RT AF Σ m b 20 (p_cmap v) 24 ART0 INB CIN ltac:(clear; lia)) as BPC.
        pose proof (pm_live_apart_sz RT AF Σ m b 20 (c_arr cv) (4 * c_nalloc cv) ART0 INB AIN ltac:(clear - NA20; lia)) as BPA.
        idtac "N3-APART".
    (* [comment removed for export] *)
        lazymatch goal with AGx : agree_on _ ?ma ?mb, A : ART RT ?S0 ?ma |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KLP : keeps_live [(pix, 64); (b, 20)] ma mb)
            by (intros bb kk Hin a Ha; apply AGx; split;
                [ right; right; left; exists bb, kk; split; [| exact Ha];
                  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
                  destruct Hin as [E|[E|[]]]; injection E as <- <-; assumption
                | cbn [outside]; destruct Hin as [E|[E|[]]]; injection E as <- <-;
                  [ clear - CPD APD Ha; unfold parked in *; lia | clear - BPC BPA Ha; unfold parked in *; lia ] ]);
          assert (BOBJ8 : box_obj (rt_live RT Σ) mb b 278 35 122 50)
            by (apply (box_obj_keep _ ma mb); [| intros bb kk Hin; apply (KLP bb kk); right; exact Hin];
                split; [| exact (proj2 BOBJ)];
                apply (keeps_live_cells (rt_live RT Σ) m ma b 20 b (box_cells 278 35 122 50)); [| exact INB| clear; lia| cbn; clear; lia| exact BXC0];
                intros bb kk Hin a Ha; apply AGF; right; right; left; exists bb, kk; split; [exact Hin| exact Ha])
        end.
        idtac "N3-KEEP".
    (* [comment removed for export] *)
        set (PF1 := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(p_cmap v + 16, p_cmap v + 20); (c_arr cv, c_arr cv + 4 * c_nalloc cv)] a).
        lazymatch type of AGF with agree_on _ _ ?mc => assert (AGF1 : agree_on PF1 m mc) by (eapply agree_sub; [exact AGF| intros z [Hz _]; exact Hz]) end.
        clear AGF. rename AGF1 into AGF.
        assert (PFS1 : forall a, PF1 a -> usp <= a \/ a < lo) by (intros a [Ha _]; exact (PFS a Ha)).
        assert (NFA1 : forall a, PF1 a -> (a < fr \/ fr + 256 <= a) /\ (a < fr / 8 + 2147450880 \/ fr / 8 + 32 + 2147450880 <= a)) by (intros a [Ha _]; exact (NFA a Ha)).
        fold_ag ltac:(fun Hx => destruct Hx as [Hx HO]; split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | exact HO]).
        idtac "N4-FOLD".
    (* [comment removed for export] *)
        destruct ACR as [(ACZ & NLT & COBJ8)|(ACO & NEQ & COBJ8)].
        { (* [comment removed for export] *)
          rewrite ACZ in *.
          lazymatch type of KLP with keeps_live _ ?ma ?mb =>
            assert (POBJ8 : pix_obj (rt_live RT Σ) mb pix v (cmapv_n cv (c_n cv + 1)))
              by (apply (pix_obj_cmap_rebuild _ ma mb pix v cv _ POBJ7);
                  [ intros bb kk Hin; apply (KLP bb kk); destruct Hin as [E|[]]; left; exact E | exact CNZ | | reflexivity ];
                  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in COBJ8 end; exact COBJ8) end.
          idtac "N5-POBJ8".
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                       [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978; 0x93504].
          lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
          idtac "N5-WALK".
    (* [comment removed for export] *)
          pose proof (TAIL Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix b v cv fr CTX) as CUT.
          lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            assert (KL9 : keeps_live (rt_live RT S) m0 m1)
              by (apply (keeps_live_walk2 RT AF S m0 m1 fr usp (usp + -256) A
                           ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end.
          repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in KL9 end.
          lazymatch type of KL9 with keeps_live _ ?ma ?mb =>
            pose proof (pix_obj_keep _ ma mb pix v _ KL9 POBJ8) as POBJ9;
            assert (BOBJ9 : box_obj (rt_live RT Σ) mb b 278 35 122 50)
              by (apply (box_obj_keep _ ma mb _ _ _ _ _ BOBJ8); intros bb kk [E|[]]; injection E as <- <-; exact (KL9 b 20 INB)) end.
          idtac "N6-OBJ".
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
          lazymatch goal with MUx : munch _ ?mm _ |- _ =>
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); destruct (NFA1 _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
          lazymatch type of AGF with agree_on _ _ ?mc =>
            assert (AGFW : agree_on PFW m mc)
              by (eapply agree_sub; [exact AGF|]; intros z [Hz HO]; split; [exact Hz|];
                  unfold pm_fp in HO; replace (p_cmap v =? 0) with false in HO by (symmetry; apply Z.eqb_neq; exact CNZ);
                  cbn [outside app] in HO |- *; destruct HO as (_ & HO1 & HO2 & _); split; [clear - HO1; lia| split; [exact HO2| exact I]]) end.
          idtac "N6-AGFW".
          to_entry.
          unfold selc_cut_stmt_0 in CUT.
          lazymatch goal with |- cps ?sg ?P _ => change (cps sg P (selc_post RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv)) end.
          idtac "N6-CHANGE".
          eapply CUT with (cvx := cmapv_n cv (c_n cv + 1)) (idx := c_n cv).
          all: lazymatch goal with
               | |- ART _ _ _ => eassumption
               | |- mem_inv _ _ => assumption
               | |- wmono _ _ _ => assumption
               | |- stk _ _ _ _ => eassumption
               | |- rw_cells _ _ _ (C8 _ :: CB 16 _ :: _) => exact FR
               | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; CB 104 _] => exact FRMx
               | |- rw_cells _ _ _ [C4 _] => exact FRMI2
               | |- rw_cells _ _ _ [CB 116 _] => exact FRMR
               | |- rw_cells _ _ _ (selc_fshadow _) => unfold selc_fshadow; exact FSH
               | |- LIBH _ => assumption
               | |- io_ssp _ => assumption
               | |- agree_on _ _ _ => exact AGFW
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- pix_obj _ _ _ _ _ => exact POBJ9
               | |- box_obj _ _ _ _ _ _ _ => exact BOBJ9
               | |- _ = _ => reflexivity
               | |- _ <= _ <= _ => clear - CNB0 CNB1; lia
               | |- _ <= rt_credit RT ?Sb =>
                   lazymatch goal with CRx : rt_credit RT _ - 1 <= rt_credit RT Sb |- _ =>
                     repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in CRx end; clear - CRx; lia end
               | |- ?g => idtac "LEFTOVER:" g
               end.
        }
    (* [comment removed for export] *)
        { (* [comment removed for export] *)
          rewrite ACO in *.
          lazymatch type of KLP with keeps_live _ ?ma ?mb =>
            assert (POBJ8 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_cmap_rebuild _ ma mb pix v cv _ POBJ7);
                  [ intros bb kk Hin; apply (KLP bb kk); destruct Hin as [E|[]]; left; exact E | exact CNZ | | reflexivity ];
                  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in COBJ8 end; exact COBJ8) end.
          idtac "N7-POBJ8".
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                       [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978; 0x93504].
          lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
          idtac "N7-WALK".
    (* [comment removed for export] *)
          lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            assert (KL9 : keeps_live (rt_live RT S) m0 m1)
              by (apply (keeps_live_walk2 RT AF S m0 m1 fr usp (usp + -256) A
                           ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end.
          repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in KL9 end.
          lazymatch type of KL9 with keeps_live _ ?ma ?mb => pose proof (pix_obj_keep _ ma mb pix v cv KL9 POBJ8) as POBJ9 end.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); destruct (NFA1 _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof RERR as RE. unfold returnError_cps in RE.
          eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
          idtac "N8-CALL".
          clear RE.
          after_call RT AF.
          lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
            assert (KL10 : keeps_live (rt_live RT Σ) ma mb)
              by (intros bb kk Hin a Ha; apply AGx; right; right; left; exists bb, kk;
                  split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]);
            pose proof (pix_obj_keep _ ma mb pix v cv KL10 POBJ9) as POBJ10 end.
          fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
          idtac "N8-AFTER".
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          walk_to AF MST [(usp - 192, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
                       [e_stack_malloc_2; e_pixGetColormap; e_pixcmapGetCount; e_pixcmapGetIndex; e_pixcmapAddColor; e_boxGetGeometry; e_returnErrorInt; e_lept_stderr; 0x935f4; 0x93978].
          lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
          idtac "N8-WALK".
    (* [comment removed for export] *)
          lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            assert (KL11 : keeps_live (rt_live RT S) m0 m1)
              by (apply (keeps_live_walk2 RT AF S m0 m1 fr usp (usp + -192) A
                           ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end.
          repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in KL11 end.
          lazymatch type of KL11 with keeps_live _ ?ma ?mb => pose proof (pix_obj_keep _ ma mb pix v cv KL11 POBJ10) as POBJ11 end.
          idtac "N9-POBJ11".
          frame_release RT AF GP MST Σ fr 2%nat 256 PF1 AGF PFS1 usp lo 0x93980
            ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
            ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); destruct (NFA1 _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          idtac "N9-REL".
          lazymatch goal with KR : forall b kk, In (b, kk) (rt_live RT ?S) -> forall a : word, _ -> ?mb a = ?ma a |- _ =>
            assert (KL12 : keeps_live (rt_live RT Σ) ma mb)
              by (intros bb kk Hin a Ha; apply (KR bb kk); [| exact Ha];
                  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin);
            pose proof (pix_obj_keep _ ma mb pix v cv KL12 POBJ11) as POBJ12 end.
          idtac "N9-POBJ12".
          refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          walk_to AF MST [(usp - 192, usp)] (@nil Z).
          try (lazymatch goal with ST' : stk asegs _ lo (usp + -192) |- _ => release_frame FR ST' usp end).
          cps_stop.
          idtac "N9-END".
    (* [comment removed for export] *)
          apply cps_finish; intros c Hc; subst QF; cbv beta.
          lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
          eexists. exists cv. split; [| alg_tac].
          eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
          split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
          split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
          { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
          idtac "N10-POST".
          split; [| split; [| repeat split; reflexivity]].
          + intros a Ha Ho. apply AGF. split.
            * lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
              exact Ha.
            * unfold pm_fp in Ho; replace (p_cmap v =? 0) with false in Ho by (symmetry; apply Z.eqb_neq; exact CNZ);
              cbn [outside app] in Ho |- *; destruct Ho as (_ & HO1 & HO2 & _); split; [clear - HO1; lia| split; [exact HO2| exact I]].
          + lazymatch goal with |- pix_obj ?lv ?mf _ _ _ =>
              replace lv with (rt_live RT Σ) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
            exact POBJ12.
        }
Qed.

End SELCMAP.
