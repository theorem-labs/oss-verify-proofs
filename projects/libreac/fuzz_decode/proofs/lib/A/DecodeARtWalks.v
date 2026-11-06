(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file. It applies the relocated core's malloc / free walks (lib/A/AF0w.v
   tfib_amalloc_realizes, lib/A/AF0q.v afree_realizes_closed, from cgif_file_fuzzer lib/A/AF0w.v:44 / AF0q.v:12 via
   fuzz_grant's Theorem Labs lane) at libreac/fuzz_decode's ASan image, in the form of lib/A/DecodeClose.v's H_RT_MALLOC (:227)
   and H_RT_FREE (:229). Rule 24: no function is proved here (no new walk); the walks are the core's. *)
(* Row D-A-rt-walks of a Theorem Labs lane's step 5b (the integrator, a Theorem Labs lane). Two forms per walk:
   - dec_A_rt_malloc / dec_A_rt_free: for every symbol record B that is GrantSyms with the image's depot hashes,
     the hypothesis' conclusion at B (for DecodeClose's free Variable B);
   - dec_A_rt_malloc_at / dec_A_rt_free_at: the same at the image's record lib/A/AD2l.v GrantB (premises discharged by
     GrantB_syms and eq_refl, as fuzz_boxreg's BoxClose.v:187-189 and fuzz_grant's GrantCloseAlloc.v:24-27 do).
   segs is decodesegs0 (lib/A/DecodeTFIB.v:19), the same term as the core's tfibsegs (lib/A/AB1v.v:13): both are
   images.Asan.M.loaded_segments. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK04 YA0n YG00 YG0f YG0n YG0d YA00 YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AF0w AF0q AD2l.

Lemma dec_A_segs : decodesegs0 = tfibsegs.
Proof. reflexivity. Qed.

(* H_RT_MALLOC (DecodeClose.v:227) at a GrantSyms record. *)
Lemma dec_A_rt_malloc : forall B, GrantSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc decodesegs0 B.
Proof.
  intros B TS HD rc fx. rewrite dec_A_segs. exact (@AF0w.tfib_amalloc_realizes fx rc B TS HD).
Qed.

(* H_RT_FREE (DecodeClose.v:229) at a GrantSyms record. *)
Lemma dec_A_rt_free : forall B, GrantSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc decodesegs0 B.
Proof.
  intros B TS HD rc fx. rewrite dec_A_segs. exact (@AF0q.afree_realizes_closed fx rc B TS HD).
Qed.

(* The same at the image's record GrantB. *)
Lemma dec_A_rt_malloc_at : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @amalloc_realizes fx rc decodesegs0 AD2l.GrantB.
Proof. exact (dec_A_rt_malloc AD2l.GrantB AD2l.GrantB_syms (fun t => eq_refl)). Qed.

Lemma dec_A_rt_free_at : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @afree_realizes fx rc decodesegs0 AD2l.GrantB.
Proof. exact (dec_A_rt_free AD2l.GrantB AD2l.GrantB_syms (fun t => eq_refl)). Qed.

Print Assumptions dec_A_rt_malloc_at.
Print Assumptions dec_A_rt_free_at.
