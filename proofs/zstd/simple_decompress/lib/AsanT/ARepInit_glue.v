(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem ITree Nodes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA ModelX.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanProgDeps ProgA AsanHandoff.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntryAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import AsanMain.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ AFake_iface AFake_init
     ADepot_iface ADepot ADepot_init F_adepot ARepFrame ARepInit_kit ARepInit_A ARepInit_D ARepInit AMain_asm.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Glue.
  Variable A0 : (nat -> Z) -> alw.
  Hypothesis A0I : A0_init_stmt A0.
  (* [comment removed for export] *)
  Hypothesis ASH : forall V (p : word), bv_unsigned p mod 4096 = 0 ->
    shad (a_space_beg0 V) <= bv_unsigned p < shad (a_space_beg0 V) + 17179869184 -> 0 <= shad (a_space_beg0 V) -> A0 V p.
  Variable U : list (list Z).
  Hypothesis HU : (length U <= 4096)%nat.
  Hypothesis HU' : Forall (fun u => (length u <= 254)%nat) U.
  Variable ASEC : alayout -> astate -> aconc -> amem -> Prop.

  Theorem aheapP_at_main : forall en inp w V m ms mo,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    bmain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
    ASEC (mkALayout (LV V) w U) (ainit (a_space_beg0 V) (a_ptr_array0 V)) X0 m ->
    AHEAP_P (mkAHoles AQUAR ASEC (ADEPOT adepot_iface) AFAKE) (mkALayout (LV V) w U) (RNG0 A0 V mo)
            (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) [] m.
  Proof.
    intros en inp w V m ms mo _ _ HM HA HS.
    pose proof HM as (_ & _ & PIN & HMF & HPF & _ & _ & _ & SH0 & _).
    apply Forall_app in HMF as [HMF HMW]. apply Forall_app in HPF as [HPF _].
    assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP).
    { destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
    change (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) with (ST0 V).
    unfold RNG0. apply AHEAP_P_init_qdf; try assumption.
    - intros p Hp Ha. apply A0I; assumption.
    - assert (E : al_space_beg (mkALayout (LV V) w U) = a_space_beg0 V) by (unfold al_space_beg, a_space_beg0; cbn [al_V LV Nat.eqb]; lia).
      rewrite E. intros p Hp Hr. apply (ASH V p Hp Hr).
      pose proof (ARepInit_D.sb_facts V w U HPF HU HAT) as (S1 & _). rewrite E in S1. rewrite ARepFrame.shad_div. unfold ASHOFF, AsanEmbed.ASHOFF. clear -S1. Z.div_mod_to_equations. lia.
  Qed.
End Glue.
End CANSEC1.
