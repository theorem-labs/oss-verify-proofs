(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree WStr Uri_kit Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AU_kit AU_iface AHarnessU_iface AU_parts_iface AH_opnew.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Set Keyed Unification.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section OpNewNT.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Hypothesis OPNEW : opnew_stmtA AI.

  Theorem opnew_nt_proofA : opnew_nt_stmtA AI.
  Proof.
    split; unfold opnew_nt_stmtA_at; intros until lo; intros AH MI ST BOT LOS TOPS SP16 TP A0 Hn HU RSTK ROK;
      pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _);
      unfold OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK in LOS;
      pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU; pose proof (wmono_refl asegs m) as WM;
      apply implMA_from_evtF;
      carve_frame 16%nat ST;
      subst a0 tp; unfold AOPNEW_NT, AOPNEW_ARR_NT.
    - zstep. zstep. zstep. apply evtF_done.
      lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
          by (eapply (AI_frame AI); [exact AH| exact MU| exact WM| constructor; [left; left; cbn; lia| constructor]])
      end.
      eapply implMA_post_evtF.
      { eapply (OPNEW L RNG) with (lo := lo); rewrite ?unsigned_lit by lia;
          first [ reflexivity | exact AH1 | exact MI | exact ST | exact HU | exact ROK | exact Hn | exact RSTK
                | (eapply rng_sub'; [exact RSTK| lia])
                | (unfold OPNEW_STACK_A, AMALLOC_STACK; lia)
                | lia
                | (clear - SP16 RSP LOS LAY4 BOT; Z.div_mod_to_equations; lia) ]. }
      intros p s' RNG' ms1 PO. unfold opnew_postA in PO.
      destruct PO as (LE & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & A & jk & -> & MI2 & ST2 & HPR & SOE & BR & AH2 & BLK & RA & RSA).
      rewrite ?unsigned_lit in ST2, HPR by lia.
      pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTK'.
      match type of FR0 with rw_cells _ _ ?A0 ?cs0 =>
        assert (FR2 : rw_cells asegs m2 A0 cs0) by (eapply aheap_pres_rw_cells; [exact HPR| exact FR0| left; left; cbn; lia]) end.
      replace (ret_pc (Z_to_bv 64 0xe2e38)) with (Z_to_bv 64 0xe2e38) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep. zstep. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done. unfold opnew_postA. split; [exact LE|].
      do 14 eexists. exists m2, A, jk. split; [reflexivity|].
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
    - zstep. zstep. zstep. zstep. apply evtF_done.
      lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
          by (eapply (AI_frame AI); [exact AH| exact MU| exact WM| constructor; [left; left; cbn; lia| constructor]])
      end.
      eapply implMA_post_evtF.
      { eapply (OPNEW L RNG) with (lo := lo); rewrite ?unsigned_lit by lia;
          first [ reflexivity | exact AH1 | exact MI | exact ST | exact HU | exact ROK | exact Hn | exact RSTK
                | (eapply rng_sub'; [exact RSTK| lia])
                | (unfold OPNEW_STACK_A, AMALLOC_STACK; lia)
                | lia
                | (clear - SP16 RSP LOS LAY4 BOT; Z.div_mod_to_equations; lia) ]. }
      intros p s' RNG' ms1 PO. unfold opnew_postA in PO.
      destruct PO as (LE & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & A & jk & -> & MI2 & ST2 & HPR & SOE & BR & AH2 & BLK & RA & RSA).
      rewrite ?unsigned_lit in ST2, HPR by lia.
      pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTK'.
      match type of FR0 with rw_cells _ _ ?A0 ?cs0 =>
        assert (FR2 : rw_cells asegs m2 A0 cs0) by (eapply aheap_pres_rw_cells; [exact HPR| exact FR0| left; left; cbn; lia]) end.
      replace (ret_pc (Z_to_bv 64 0xe2e6c)) with (Z_to_bv 64 0xe2e6c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep. zstep. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done. unfold opnew_postA. split; [exact LE|].
      do 14 eexists. exists m2, A, jk. split; [reflexivity|].
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
  Theorem opdelete_arr_proofA : opdelete_arr_stmtA AI.
  Proof.
    unfold opdelete_arr_stmtA, opdelete_stmtA_at; intros until tr; intros AH HIN MI ST BOT LOS TOP TP A0 UC HU NS8 RA4 RAPC LTR SP16 RSTK ROK;
      unfold HarnessP.opdelete; apply implMA_from_evtF; unfold AOPDEL_ARR.
    zstep. zstep. apply evtF_done. eapply (implMA_afree_call AI); eauto using aunw_chain.
  Qed.
End OpNewNT.
End CANSEC1.
