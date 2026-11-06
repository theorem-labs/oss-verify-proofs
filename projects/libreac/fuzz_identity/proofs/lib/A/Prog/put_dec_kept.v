(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the caller-journal shapes of projects/cgif/cgif_file_fuzzer/proofs/lib/YC20.v:311-365 (as fuzz_grant's lib/A/Prog/CtrlFinish.v states them: tcj_kept, twr_ok, tsrc_ok) over fuzz_identity's listing, the destination shape tdst_ok, and ajournal_sub_awr: lib/YCbq.v's ajournal_sub with the caller's write right awr_byte (its stack window and its own frames too) in place of ajournal_sub's heap-block-or-tmp-block premise. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/IdentCJ.v; 21 of its 54 lines of code are new or changed and 210 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym IdentSyms IdentList IdentPa.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentCJ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma pd_tcj_of_parts : forall STKc lyc Sc W memc W2 mem2 sp (E : Z -> Prop) F,
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STKc <= a < sp) -> ~ E a -> ~ (F <= a < F + 64) ->
 ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
 aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
(forall cid pos a, In (cid, pos) (frames Sc) ->
 (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
 ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STKc <= a < sp) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) ->
(forall a, sp - STKc <= a < sp -> apresent (w_H W2) mem2 a) ->
4096 <= F -> F + 64 <= alloc_ceiling -> in_app F 64 -> F mod 32 = 0 ->
(forall a, F <= a < F + 64 -> alloc_ceiling <= a -> False) ->
tcj_kept B STKc lyc Sc W memc W2 mem2 sp E.
Proof using LAWS.
intros STKc lyc Sc W memc W2 mem2 sp E F K1 K2 K3 K4 K5 K6 HF4096 HFceil HFapp HFq HFhi.
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as R.
split; [|split; [exact K2|split; [exact K3|split; [exact K4|split; [exact K5|exact K6]]]]].
intros a Ha Hw HE. apply K1; [exact Ha | exact Hw | exact HE | clear - Ha HFceil; lia |].
clear - Ha HFceil C1 D R. unfold SHADOW_OFF. lia.
Qed.
End e.
End d.
End b.
