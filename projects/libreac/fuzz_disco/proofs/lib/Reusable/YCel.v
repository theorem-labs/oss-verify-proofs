(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI0m YI0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YF0l YCej YCeh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Let HBgot := tl_got_shadow B TL.
Let HBcell := tl_shadow_cell B TL.
Lemma obj_at_kept : forall (m m' : word -> option byte) p lay vals sz,
obj_at tfibsegs m p lay vals -> lay_inside lay sz = true ->
(forall i, 0 <= i < sz -> mbyte tfibsegs m' (p + i) = mbyte tfibsegs m (p + i)) -> obj_at tfibsegs m' p lay vals.
Proof. intros m m' p lay vals sz H Hl Hk. exact (obj_at_transport_range tfibsegs m m' p lay vals sz H Hl Hk). Qed.
Definition blk_kept (H H' : word -> bool) (m m' : word -> option byte) (b n : Z) : Prop :=
forall i, 0 <= i < n -> aview tfibsegs H' m' (b + i) = aview tfibsegs H m (b + i).
Lemma obj_at_blk_kept : forall H H' m m' p lay vals sz,
obj_at tfibsegs (mrestrict H m) p lay vals -> lay_inside lay sz = true -> blk_kept H H' m m' p sz ->
obj_at tfibsegs (mrestrict H' m') p lay vals.
Proof.
intros H H' m m' p lay vals sz Ho Hl Hk. apply (obj_at_kept _ _ p lay vals sz Ho Hl).
intros i Hi. apply (mbyte_of_aview tfibsegs). apply Hk. exact Hi.
Qed.
End c.
End a.
