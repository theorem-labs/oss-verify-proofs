(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface ARep ARepFrame AHeapP AInstance AInstanceM AInstanceU AMalloc_iface2 AInstanceU2 AArenaLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Theorem AHU2_arena : arena_law AHEAPu2.
Proof.
  intros L RNG st LB m p A n (ov & [g AH] & _) Hin PRIM.
  pose proof AH as (ALO & _ & [X [AR BL]] & _).
  destruct (hb_cases (ov:=ov) (gb:=g) L st X LB m p A n ALO AR BL Hin)
    as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & _ & KB & P5 & P4 & _)|(mb & ms & _ & _ & _ & NP & _)]; [| congruence].
  exists (xb_class b). unfold K_NUM_CLASSES in CLB. split; [lia|].
  pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ16.
  unfold xb_user, aregion in *. subst A. rewrite Nb. split; lia.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB ARep.TwinB ARepFrame.TwinB AHeapP.TwinB AInstance.TwinB AInstanceM.TwinB AInstanceU.TwinB AMalloc_iface2.TwinB AInstanceU2.TwinB AArenaLaw.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Theorem AHU2_arena : arena_law AHEAPu2.
Proof.
  intros L RNG st LB m p A n (ov & [g AH] & _) Hin PRIM.
  pose proof AH as (ALO & _ & [X [AR BL]] & _).
  destruct (hb_cases (ov:=ov) (gb:=g) L st X LB m p A n ALO AR BL Hin)
    as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & _ & KB & P5 & P4 & _)|(mb & ms & _ & _ & _ & NP & _)]; [| congruence].
  exists (xb_class b). unfold K_NUM_CLASSES in CLB. split; [lia|].
  pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ16.
  unfold xb_user, aregion in *. subst A. rewrite Nb. split; lia.
Qed.
End CANSEC1.
End TwinB.
