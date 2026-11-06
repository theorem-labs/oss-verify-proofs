(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface RT_state RT_rep RT_artfacts.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_artfacts.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac cs_range :=
  let i := fresh "i" in let Hi := fresh "Hi" in
  intros i Hi; split; [split|];
  [ unfold in_ranges, CLIENT_STATIC; do 2 eexists; split; [left; reflexivity| lia]
  | unfold in_ranges, RT_STATIC; intros (lo & hi & Hin & Hr); cbn [In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); exact Hin
  | lia ].

Section Globals.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.

  (* [comment removed for export] *)
  Lemma af_acc_crc : forall Σ m, ART RT Σ m -> acc bsegs m 0xd13e0 1024.
  Proof. intros Σ m HA. apply (af_acc_static RT AF Σ m 0xd13e0 1024 HA); [lia| cs_range]. Qed.

  (* [comment removed for export] *)
  Lemma af_acc_rnums : forall Σ m, ART RT Σ m -> acc bsegs m 0xd1940 2048.
  Proof. intros Σ m HA. apply (af_acc_static RT AF Σ m 0xd1940 2048 HA); [lia| cs_range]. Qed.
  (* [comment removed for export] *)
  Lemma af_acc_incs : forall Σ m, ART RT Σ m -> acc bsegs m 0xd18e0 56.
  Proof. intros Σ m HA. apply (af_acc_static RT AF Σ m 0xd18e0 56 HA); [lia| cs_range]. Qed.
End Globals.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface RT_state RT_rep RT_artfacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac cs_range :=
  let i := fresh "i" in let Hi := fresh "Hi" in
  intros i Hi; split; [split|];
  [ unfold in_ranges, CLIENT_STATIC; do 2 eexists; split; [left; reflexivity| lia]
  | unfold in_ranges, RT_STATIC; intros (lo & hi & Hin & Hr); cbn [In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); exact Hin
  | lia ].

Section Globals.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.

  (* [comment removed for export] *)
  Lemma af_acc_crc : forall Σ m, ART RT Σ m -> acc asegs m 0xc4000 1024.
  Proof. intros Σ m HA. apply (af_acc_static RT AF Σ m 0xc4000 1024 HA); [lia| cs_range]. Qed.

  (* [comment removed for export] *)
  Lemma af_acc_rnums : forall Σ m, ART RT Σ m -> acc asegs m 0xc4500 2048.
  Proof. intros Σ m HA. apply (af_acc_static RT AF Σ m 0xc4500 2048 HA); [lia| cs_range]. Qed.
End Globals.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
