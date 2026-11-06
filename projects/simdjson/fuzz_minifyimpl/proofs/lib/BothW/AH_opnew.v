(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree WStr Uri_kit Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AU_kit AU_iface AHarnessU_iface AU_parts_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Set Keyed Unification.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.

Section CANSEC1. Context {rc : runConstT}.
Section OpNew.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  Theorem opnew_proofA : opnew_stmtA AI.
  Proof.
    unfold opnew_stmtA. intros until lo. intros AH MI ST BOT LOS TOPS SP16 TP A0 Hn HU RSTK ROK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _).
    unfold OPNEW_STACK_A, AMALLOC_STACK in LOS. unfold AREQMAX in *.
    unfold HarnessM.opnew. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    carve_frame 16%nat ST.
    subst a0 tp. unfold AOPNEW.
    do 3 zstep. zstep. zstep.
    replace (n + Z.b2z (n <? 1)) with n by (destruct (Z.ltb_spec n 1); cbn; lia).
    zstep. zstep. apply evtF_done.
    (* [comment removed for export] *)
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
        by (eapply (AI_frame AI); [exact AH| exact MU| exact WM| constructor; [left; left; cbn; lia| constructor]])
    end.
    eapply implMA_bind.
    { eapply (implMA_amalloc_call AI) with (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
        first [ reflexivity | exact AH1 | exact MI | exact ST | exact HU | exact ROK
              | (apply aunw_data; rewrite ?unsigned_lit by lia; [lia | lia | exact HU])
              | (eapply rng_sub'; [exact RSTK| lia])
              | (unfold AMALLOC_PC, AMALLOC_STACK, AREQMAX; cbn; lia)
              | (clear - SP16 RSP LOS LAY4 BOT; Z.div_mod_to_equations; lia) ]. }
    cbv beta. intros r s' RNG' ms1 [SOE PO].
    destruct PO as (LE & u0 & u1 & u2 & xa0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & HPR & RR).
    cbn [fst snd] in RR, HPR, ST2, MI2. rewrite ?unsigned_lit in ST2, HPR by lia.
    destruct r as [p|]; [| destruct RR].
    destruct RR as (A & junk2 & -> & BR & AH2 & BLK & RA & RSA & _).
    pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    unfold AOPNEW_RET. retlit.
    assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra])
      by (eapply aheap_pres_rw_cells; [exact HPR| exact FR0| left; left; cbn; lia]).
    cbn [new_handlerA]. apply implMA_ret.
    pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTK'.
    zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    do 3 zstep. zstep.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evtF_done. unfold opnew_postA. split; [exact LE|].
    do 14 eexists. exists m2, A, junk2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split.
    { eapply aheap_pres_trans.
      - eapply aheap_pres_of_munch; [exact MU| exact WM|]. intros a Hc. cbn.
        pose proof (AI_aci_img AI) as CIB.
        destruct Hc as [Hc|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]]; unfold AIMG_HI in *.
        + lia.
        + pose proof (CIB iv Hiv). lia.
        + pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb). unfold AIMG_HI in *. lia.
        + rewrite shad_div. unfold ASHOFF.
          assert (A47 : a' < 2^47).
          { destruct Ha' as [H|[(iv & Hiv & Hr)|(c & FA & fn & Hb & Hr)]]; [lia| pose proof (CIB iv Hiv); lia|].
            pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb). cbn in *. atop_facts. lia. }
          split; [| exact I]. clear - A47 LAY4 BOT LOS. Z.div_mod_to_equations. lia.
      - eapply aheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]. }
    split; [exact SOE|]. split; [exact BR|]. split; [exact AH2|]. split; [exact BLK|]. split; [exact RA| exact RSA].
  Qed.

  (* [comment removed for export] *)
  Theorem opdelete_proofA : opdelete_stmtA AI.
  Proof.
    split; unfold opdelete_stmtA_at; intros until tr; intros AH HIN MI ST BOT LOS TOP TP A0 UC HU NS8 RA4 RAPC LTR SP16 RSTK ROK;
      unfold HarnessM.opdelete; apply implMA_from_evtF; unfold AOPDEL_SZ, AOPDEL.
    - zstep. zstep. apply evtF_done. eapply (implMA_afree_call AI); eauto using aunw_chain.
    - zstep. apply evtF_done. eapply (implMA_afree_call AI); eauto using aunw_chain.
  Qed.
End OpNew.
End CANSEC1.
