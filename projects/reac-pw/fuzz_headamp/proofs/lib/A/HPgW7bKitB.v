(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated as w7_memcpy_at for image A's __asan_memcpy 0x510d4, with the wrapper's same_but_materialized kept in the post as same_io; the rest of the file is new. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47): two lemmas of the memory kit of the walk of
   LLVMFuzzerTestOneInput from 0x81a34 to 0x8237c that lib/A/HPgW7bKit.v lacks. Proves no function (kind: segment lemma).
   w7_ra_rd: range_addressable moves from one reader to another that agrees with it on the shadow hull.
   w7_strok_kept2: HPgW7bKit.w7_strok moves across a change of world as well as of memory (only the readers on
   w7_strz matter). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgMem HPgW7bBase HPgW7bKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma w7_ra_rd : forall (rd rd' : reader) x n,
range_addressable rd SHADOW_OFF x n -> 0 <= x -> (forall a, w7_hull x n a -> rd' a = rd a) -> range_addressable rd' SHADOW_OFF x n.
Proof.
intros rd rd' x n HR Hx HK y Hy. destruct (HR y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite HK; [exact Hs|]. unfold w7_hull, shadow_of_addr. unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)) as M1.
pose proof (Z.div_le_mono y (x + n - 1) 8 ltac:(lia) ltac:(lia)) as M2.
pose proof (Z.div_mod (0x7fff8000 + (x + n - 1) / 8) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (0x7fff8000 + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.div_le_mono (0x7fff8000 + x / 8) (0x7fff8000 + y / 8) 8 ltac:(lia) ltac:(lia)) as M3.
pose proof (Z.mul_div_le (0x7fff8000 + y / 8) 8 ltac:(lia)). nia.
Qed.
Lemma w7_strok_kept2 : forall (W W' : world rsegs) m m' R x s,
w7_strok W m R x s -> (forall a, w7_strz x s a -> aview rsegs (w_H W') m' a = aview rsegs (w_H W) m a) ->
w7_strok W' m' R x s.
Proof.
intros W W' m m' R x s (H0 & H1 & H2 & Hb & Hn & Ht & Hs & Ha & Hr & Hh) HK.
split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [intros j Hj; rewrite HK by (left; lia); exact (Hb j Hj)|].
split; [rewrite HK by (left; lia); exact Hn|].
split; [intros a Hx; rewrite HK; [exact (Ht a Hx)|]; left; pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8); lia|].
split; [exact Hs|]. split; [exact Ha|].
split; [apply (w7_ra_rd (aview rsegs (w_H W) m)); [exact Hr | lia | intros a Hx; apply HK; right; exact Hx]|].
intros a Hx. rewrite HK by (right; exact Hx). exact (Hh a Hx).
Qed.
End b.
Print Assumptions w7_ra_rd.
Print Assumptions w7_strok_kept2.
