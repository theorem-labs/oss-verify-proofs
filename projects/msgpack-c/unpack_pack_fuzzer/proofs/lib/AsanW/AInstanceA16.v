(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface ARep AHeapP AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AInstance AInstanceM AInstanceF ADepot_iface ARepQ F_adepot ASec. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1_16. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aaligned_iseg AEmbRep AMalloc_x AInstanceX AInstanceU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section Inst.
Context {rc : runConstT} {ov : annOV}.
Hypothesis EXHW : exh_first_stmt.

Theorem AHU_aligned16_h : aaligned16_stmt_h aci_I AHEAPu.
Proof.
  unfold aaligned16_stmt_h. intros until RESV. intros OVF PRIM N16 [g AH]. intros.
  eapply implF_epost_mono; [eapply (@AHI_aligned16_h rc ov g EXHW); eassumption|].
  intros [st' [p|]] RNG' ms'; unfold amalloc_post_h; cbn [snd fst].
  - intros (LE & P). split; [exact LE|].
    destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI & ST & PR & M).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [exact PR|].
    cbn [snd fst] in M |- *. destruct M as (A & junk & M1 & M2 & M3 & M4). exists A, junk. split; [exact M1|]. split; [exact M2|]. split; [exists g; exact M3| exact M4].
  - intros (LE & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI & ST & PR & M & ER). split; [exact LE|].
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [exact PR|].
    split; [exists g; exact M| exact ER].
Qed.
End Inst.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB ARep.TwinB AHeapP.TwinB AFake_iface.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep. Import AInstance.TwinB AInstanceM.TwinB AInstanceF.TwinB ADepot_iface.TwinB ARepQ.TwinB F_adepot.TwinB ASec.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1_16. Import F_aaligned_iseg.TwinB AEmbRep.TwinB AMalloc_x.TwinB AInstanceX.TwinB AInstanceU.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section Inst.
Context {rc : runConstT} {ov : annOV}.
Hypothesis EXHW : exh_first_stmt.

Theorem AHU_aligned16_h : aaligned16_stmt_h aci_I AHEAPu.
Proof.
  unfold aaligned16_stmt_h. intros until RESV. intros OVF PRIM N16 [g AH]. intros.
  eapply implF_epost_mono; [eapply (@AHI_aligned16_h rc ov g EXHW); eassumption|].
  intros [st' [p|]] RNG' ms'; unfold amalloc_post_h; cbn [snd fst].
  - intros (LE & P). split; [exact LE|].
    destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI & ST & PR & M).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [exact PR|].
    cbn [snd fst] in M |- *. destruct M as (A & junk & M1 & M2 & M3 & M4). exists A, junk. split; [exact M1|]. split; [exact M2|]. split; [exists g; exact M3| exact M4].
  - intros (LE & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI & ST & PR & M & ER). split; [exact LE|].
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [exact PR|].
    split; [exists g; exact M| exact ER].
Qed.
End Inst.
End TwinB.
