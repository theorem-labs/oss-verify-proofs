(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP ARepQ ARepQP ASec ASecFrame
     ADepot_iface F_adepot AFake_iface AFake_arep F_afree_arep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition achunk_kind_ok (ch : achunk) (n : Z) : Prop :=
  match ch with CPrim _ _ => is_primary n = true | CSec _ _ _ => is_primary n = false end.

Definition AHI : aholes := mkAHoles AQUAR ASEC_of (ADEPOT adepot_iface) AFAKE.

Lemma AHI_eq : AHI = AH adepot_iface AQUAR ASEC_of.
Proof. reflexivity. Qed.

Theorem AHI_laws : ahole_laws AHI.
Proof.
  constructor; cbn [AHI ah_quar ah_sec ah_depot ah_fake].
  - exact AQUAR_frame.
  - exact asec_hs_frame.
  - exact (adi_frame adepot_iface).
  - intros L LB m m' W HF MU WM UT. eapply afake_frame; [exact HF| exact MU| exact WM| exact UT].
  - intros L LB LB' m HF EQ. eapply afake_blocks; [exact HF| exact EQ].
Qed.

Corollary AH_laws : ahole_laws (AH adepot_iface AQUAR ASEC_of).
Proof. rewrite <- AHI_eq. exact AHI_laws. Qed.
Lemma AHI_eqQ : AHI = F_afree_arep.AHQ adepot_iface ASEC_of AFAKE.
Proof. reflexivity. Qed.
Corollary AHQ_laws : ahole_laws (F_afree_arep.AHQ adepot_iface ASEC_of AFAKE).
Proof. rewrite <- AHI_eqQ. exact AHI_laws. Qed.
End CANSEC1.
