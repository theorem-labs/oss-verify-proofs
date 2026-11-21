(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/zlib/checksum_fuzzer/proofs/lib/Reusable/YK16.v at , lines 6-42, comments removed. *)

From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
Unset Lia Cache.

Import ListNotations.


Ltac norm_fd32 :=
  repeat match goal with
         | |- context [fd32 AT_FDCWD] =>
             change (fd32 AT_FDCWD) with AT_FDCWD32
         | H : context [fd32 AT_FDCWD] |- _ =>
             change (fd32 AT_FDCWD) with AT_FDCWD32 in H
         | |- context [fd32 ?x] => change (fd32 x) with x
         | H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
         end.

Ltac fd32_ok :=
  solve [ reflexivity
        | assumption
        | apply fd32_lt31; assumption
        | apply fd32_id; assumption
        | apply fd32_lt31; lia
        | apply fd32_id; lia ].

Lemma star_inv (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star segs c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
  apply IHHstar. eapply Hstep; eauto.
Qed.

Lemma inv_no_reaches_error (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> ~ reaches_error segs c.
Proof.
  intros c HInv (tr & c' & evs & Hstar & Hss).
  eapply Hnoerr; [| exact Hss].
  eapply star_inv; eauto.
Qed.




