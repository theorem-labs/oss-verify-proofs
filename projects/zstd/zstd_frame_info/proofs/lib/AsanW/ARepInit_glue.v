(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem ITree Nodes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA ModelX.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanProgDeps ProgA AsanHandoff.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import AsanMain.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ AFake_iface AFake_init
     ADepot_iface ADepot ADepot_init F_adepot ARepFrame ARepInit_kit ARepInit_A ARepInit_D ARepInit AMain_asm.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Glue.
  Variable A0 : (nat -> Z) -> alw.
  Hypothesis A0I : A0_init_stmt A0.
  (* [comment removed for export] *)
  Hypothesis ASH : forall V (p : word) (c k : Z), 0 <= a_space_beg0 V -> a_space_beg0 V mod 4096 = 0 ->
    bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
    (bv_unsigned p = shad (a_space_beg0 V) + 536870912 * c - 4096
     \/ (0 <= k <= 14336 /\ bv_unsigned p = shad (a_space_beg0 V) + 536870912 * c + 32768 * k)) -> A0 V p.
  Variable U : list (list Z).
  Hypothesis HU : (length U <= 4096)%nat.
  Hypothesis HU' : Forall (fun u => (length u <= 254)%nat) U.
  Variable ASEC : alayout -> astate -> aconc -> amem -> Prop.

  #[using="A0I ASH HU HU'"] Theorem aheapP_at_main : forall en inp w V m ms mo,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
    amain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
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
    - Local Ltac2 Set LiaHints.tbl := fun () => "0050>16835598296.3618926759668.3018933043916.3032017048862.2536770060565.3000000700;00?00C00GS2HU2S1S2HUS2HUS2HUS2HU".
assert (E : al_space_beg (mkALayout (LV V) w U) = a_space_beg0 V) by (unfold al_space_beg, a_space_beg0; cbn [al_V LV Nat.eqb]; lia).
      pose proof (ARepInit_D.sb_facts V w U HPF HU HAT) as (S1 & _ & S3 & S4). rewrite ?E in S1. rewrite ?E in S3. rewrite ?E in S4.
      assert (SAL : a_space_beg0 V mod 4096 = 0).
      { unfold K_ALIGN in S3. apply (Z.mod_divide _ 65536) in S3; [|lia]. destruct S3 as [q Hq]. rewrite Hq.
        replace (q * 65536) with ((q * 16) * 4096) by lia. apply Z.mod_mul. lia. }
      rewrite E. intros p c k Hp Hc Hr. exact (ASH V p c k ltac:(lia) SAL Hp Hc Hr).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Glue.
End CANSEC1.
