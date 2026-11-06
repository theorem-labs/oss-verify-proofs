(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: made here for libreac/fuzz_decode row D-B-rt-walks (a Theorem Labs lane's free list,
   the integrator, a Theorem Labs lane).  The two runtime walks lib/B/DecodeBClose.v takes as H_RT_MALLOC (:221) and H_RT_FREE
   (:223), proved at image B's segments from this unit's own relocated donors:
     lib/B/YF0w.v:44  tfib_amalloc_realizes
     lib/B/YF0q.v:10  afree_realizes_closed
   Names agreed with a Theorem Labs lane, which holds the image-A twin lib/A/DecodeARtWalks.v (dec_A_rt_malloc / _free and
   the _at forms at AD2l.GrantB): the B names are dec_B_rt_malloc / dec_B_rt_free, with _at at YD2l.TfibB.
   The row covers ONLY these two; H_LINK_MALLOC04 (:242) and H_LINK_FREE04 (:244) are a Theorem Labs lane's link lane. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK04 YA0n YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YA00 YB1v YF0m YFfs YD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YF0w YF0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* H_RT_MALLOC's conclusion, at this unit's own segments. *)
Lemma dec_B_rt_malloc :
  forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
  @amalloc_realizes fx rc decodesegsB0 B.
Proof. intros B TS HD. exact (tfib_amalloc_realizes B TS HD). Qed.

(* H_RT_FREE's conclusion, likewise. *)
Lemma dec_B_rt_free :
  forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
  @afree_realizes fx rc decodesegsB0 B.
Proof. intros B TS HD. exact (afree_realizes_closed B TS HD). Qed.

End a.

(* The concrete form the composition binds (a Theorem Labs lane, 15:22Z): image B's record is YD2l.TfibB. *)
Lemma dec_B_rt_malloc_at :
  (forall t, as_dhash TfibB t = tfib_dhash t) ->
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc decodesegsB0 TfibB.
Proof. intros HD rc fx. exact (dec_B_rt_malloc TfibB TfibB_syms HD). Qed.

Lemma dec_B_rt_free_at :
  (forall t, as_dhash TfibB t = tfib_dhash t) ->
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc decodesegsB0 TfibB.
Proof. intros HD rc fx. exact (dec_B_rt_free TfibB TfibB_syms HD). Qed.
