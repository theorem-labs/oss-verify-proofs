(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the member loop's INDUCTION of parse_items' image-B walk (lane PItemsB, owner). The
   segment lanes prove one step each at the cut PI_O_BODY (0x87bbc, where both grow calls join): PItemsBody's
   pi_body_holds gives pi_body_spec d N from pi_body_spec d N' for every N' < N (through PItemsValue's
   pi_val_holds, whose re-entry after a comma is at a strictly shorter rest). This file closes that strong
   induction on the rest's length bound N. Pure: no instruction is stepped here.
   Rule 24: no function is proved in this file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
From Stdlib Require Import Wf_nat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_pres.


Section loop. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L} {PL : PAListing L}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* the strong induction on the rest's length bound: one step at the cut for every N gives the cut for every N *)
Lemma pi_body_all : forall (d : nat) (CTX0 CW : list (list Z)),
  (forall N : nat, (forall N' : nat, (N' < N)%nat -> pi_body_spec B ARx SK d CTX0 CW N') ->
     pi_body_spec B ARx SK d CTX0 CW N) ->
  forall N : nat, pi_body_spec B ARx SK d CTX0 CW N.
Proof.
intros d CTX0 CW STEP N. induction N as [N IH] using lt_wf_ind. apply STEP. exact IH.
Qed.

End loop.
