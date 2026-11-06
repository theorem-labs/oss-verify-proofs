(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP ARepQ ARepQP ASec ASecFrame ADepot_iface F_adepot AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
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
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ARep.TwinB ALayout.TwinB AHeapP.TwinB ARepQ.TwinB ARepQP.TwinB ASec.TwinB ASecFrame.TwinB ADepot_iface.TwinB F_adepot.TwinB AFake_iface.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
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
End CANSEC1.
End TwinB.
