(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP ARepQ ARepQP ASec ASecFrame
     ADepot_iface F_adepot F_amalloc_arep F_afree_arep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AFK0 : alayout -> list ablock -> amem -> Prop :=
  fun _ LB _ => forall c F n, ~ In (mkABlock (ABFake c) F n) LB.

Definition AHI : aholes := mkAHoles AQUAR ASEC_of (ADEPOT adepot_iface) AFK0.

Lemma AHI_eq : AHI = AH adepot_iface AQUAR ASEC_of AFK0.
Proof. reflexivity. Qed.
Lemma AHI_eqQ : AHI = AHQ adepot_iface ASEC_of AFK0.
Proof. reflexivity. Qed.

Theorem AHI_laws : ahole_laws AHI.
Proof.
  constructor; cbn [AHI ah_quar ah_sec ah_depot ah_fake].
  - exact AQUAR_frame.
  - exact asec_hs_frame.
  - exact (adi_frame adepot_iface).
  - intros L LB m m' W HF MU WM UT. exact HF.
  - intros L LB LB' m HF EQ c F n Hin. apply (HF c F n). apply (proj1 (EQ c F n)). exact Hin.
Qed.

Corollary AH_laws : ahole_laws (AH adepot_iface AQUAR ASEC_of AFK0).
Proof. rewrite <- AHI_eq. exact AHI_laws. Qed.
Corollary AHQ_laws : ahole_laws (AHQ adepot_iface ASEC_of AFK0).
Proof. rewrite <- AHI_eqQ. exact AHI_laws. Qed.
End CANSEC1.
