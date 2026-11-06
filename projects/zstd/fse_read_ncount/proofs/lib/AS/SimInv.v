(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
Unset Lia Cache.
Import ListNotations.
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
