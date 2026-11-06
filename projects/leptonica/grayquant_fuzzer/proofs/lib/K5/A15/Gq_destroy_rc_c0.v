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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain LeptC_leaf LeptM_destroy_defs Gm_iface Gq_iface Gq_destroy_rc_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Section DESTROY_RC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixDestroy_rc_case_ok : pixDestroy_rc_case RT 0.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv rc
    FDO MST -> -> OP PPC POBJ RCB PPX ENV RES AL.
  unfold lpost, lenv, lres, keeps, keepsL, optrL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct OP as (OWN & PP0 & PP8 & PPH & PPS).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixDestroy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  clearbody usp.
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (LVF := rt_live RT Σ) in *.
  (* [comment removed for export] *)
  set (PF0 := fun a => aclient LVF (rt_frames RT Σ) usp a).
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pp, pp + 8); (pix + 20, pix + 24)] a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ)) by (intros e He; exact He).
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (PPLO : pp + 8 <= lo).
  { destruct OWN as [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & _)].
    - pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (_ & R & _). unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. lia.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. lia. }
  destruct POBJ as (PXC & (PIN & PX0 & PX16 & _) & HDROK & PDAT & PCM).
  pose proof (af_live_range RT AF Σ m pix 64 ART0 PIN) as (_ & PXR & PXS). unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in PXR, PXS.
  pose proof (gp_live_hi RT GP Σ m pix 64 ART0 PIN) as PXH.      (* [comment removed for export] *)
  pose proof PPC as PPC0. hide PPC0.     (* [comment removed for export] *)
  unfold pix_cells_rc in PXC.
  clear PCM PDAT.
  pose proof OWN as OWN0. park OWN0.       (* [comment removed for export] *)
  (* [comment removed for export] *)
  park_disj. carve_frame 96%nat ST. park OWN.
    Time walk_to AF MST [(usp - 96, usp)] [0x4b928; 0x62054; 0x97dc0; 0x90c20].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    unpark_accok OWN AGF.
    eapply cps_seq.
    { pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF0 (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact Ha).
    fframe_chunk RT AF fr 0%nat 64 pix 64.
    fframe_optr RT AF fr 0%nat 64 OWN usp. park OWN.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x93f38].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      unpark_accok_munch OWN MUx LVF (rt_frames RT Σ) usp
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    (* [comment removed for export] *)
    lazymatch type of AGF with agree_on _ _ ?mm =>
      assert (PPC1 : rw_cells asegs mm pp [C8 (Z_to_bv 64 pix)])
        by (unfold hid in PPC0; apply (rw_cells_agree_nw asegs m mm pp _ PPC0); apply (agree_sub PF0 _ m mm AGF); intros zx Hx;
            cbn [cells_size csize Nat.add] in Hx; exact (accok_aclient _ _ _ usp pp 8 zx OWN ltac:(lia))) end.
    (* [comment removed for export] *)
    assert (AGF1 : agree_on PF m _) by (eapply agree_sub; [exact AGF| intros zz [Hz _]; exact Hz]). clear AGF. rename AGF1 into AGF.
    assert (PFS1 : forall a, PF a -> usp <= a \/ a < lo) by (intros a [Ha _]; exact (PFS a Ha)).
    assert (PFO : forall a, PF a -> (a < pp \/ pp + 8 <= a) /\ (a < pix + 20 \/ pix + 24 <= a)).
    { intros a [_ Ho]. cbn [outside] in Ho. lia. }
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (pix + 20, pix + 24); (pp, pp + 8)]
                 [0x4b928; 0x62054; 0x97dc0; 0x90c20; 0x94080].
    assert (AMO : amo_aligned AW (Z_to_bv 64 (pix + 20)) = true).
    { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. clear - PX16. Z.div_mod_to_equations; lia. }
    amo_step AMO.
    Time awalk [0x4b928; 0x62054; 0x97dc0; 0x90c20; 0x94080].
    (* [comment removed for export] *)
    rewrite (amo_dec_bytes rc ltac:(lia)). try (rewrite (rc_bne_taken rc ltac:(lia)); cbv iota).   (* [comment removed for export] *)
    mem_after_store.
    Time awalk [0x4b928; 0x62054; 0x97dc0; 0x90c20; 0x94080].
    lazymatch goal with H : rw_cells asegs _ pp [C8 _] |- _ => pose proof H as PPCz; hide PPCz end.   (* [comment removed for export] *)
    frame_release_g RT AF GP MST Σ fr 0%nat 64 PF AGF PFS1 usp lo 0x94088
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
              split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]|
              split; [intros zz Hzz; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ zz);
                        [ unfold parked in OWN0; exact (accok_aclient _ _ _ usp pp 8 zz OWN0 ltac:(lia))
                        | intros e He; lvf_keep LVFS He
                        | solve [frames_sub_tac] | lia ]
                     | exact I]]]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); pose proof (PFO _ Hx); destruct Hx as [Hx Ho]; destruct (NFA _ Hx) as [N1 N2];
                      cbn [outside] in Ho; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia])
      LVF
      ltac:(intros e He; lvf_keep LVFS He)
      ltac:(fun Hx => destruct Hx as [Hx _]; exact Hx).
    (* [comment removed for export] *)
    lazymatch goal with MUx : munch [(?fl, _)] ?ma ?mb, FLNx : ~ aclient _ _ USTACK_TOP ?fl |- _ =>
      assert (FPP : fl < pp \/ pp + 8 <= fl)
        by (apply (flag_apart _ _ fl pp (pp + 8) FLNx); intros zx Hzx;
            apply (aclient_mono LVF (rt_frames RT Σ) USTACK_TOP _ _ USTACK_TOP zx);
            [ unfold parked in OWN0; exact (accok_aclient _ _ _ USTACK_TOP pp 8 zx OWN0 ltac:(lia))
            | intros e He; lvf_keep LVFS He
            | solve [frames_sub_tac] | lia ]);
      unfold hid in PPCz;
      apply (rw_cells_agree_nw asegs ma mb pp _) in PPCz;
        [| intros zx Hzx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzx; apply MUx; cbn [outside];
           split; [clear - Hzx FPP; lia| exact I]];
      clear FLNx
    end.
    hide PPCz.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 96, usp)] (@nil Z).
    try (lazymatch goal with ST' : stk asegs _ lo (usp + -96) |- _ => release_frame FR ST' usp end).   (* [comment removed for export] *)
    cps_stop.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    eexists. split.
    + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [exact ART2| split; [assumption| split; [exact WM| assumption]]]| split; assumption]|].
      split; [| split; [unfold hid in PPCz; exact PPCz| unfold pix_cells_rc; exact PXC]].
      intros a Ha Ho. apply AGF. split; [| exact Ho].
      lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with LVF in Ha; [exact Ha|] end.
      unfold LVF. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. reflexivity.
    + unfold LVF.
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
      repeat split; auto; lia.
Qed.
End DESTROY_RC.
