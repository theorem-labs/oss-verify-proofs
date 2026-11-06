(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import SimInv ShapeAlg DivergeSim SpinAlg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import RegsEqv0.
Local Instance srz_fx_as : OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS.PropExec.FPState := OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS.PropExec.fx0.
Local Instance srz_fx_lib : OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.PropExec.FPState := OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.PropExec.fx0.
Import ListNotations.
Section WithSegs.
Variable segs : list Segment.
#[using="Type"] Lemma sstep_next_eqv : forall c c' e c2,
cfg_eqv c c' -> sstep_cfg segs ACFG c e (SNext c2) -> exists c2', sstep_cfg segs ACFG c' e (SNext c2') /\ cfg_eqv c2 c2'.
Proof.
intros c c' e c2 Heqv Hss.
destruct (sstep_cfg_eqv0_scfg segs ACFG c c' e (SNext c2) Heqv Hss) as (X' & Hss' & HX).
destruct X' as [c2'| ]; cbn in HX; [|contradiction].
exists c2'. split; assumption.
Qed.
#[using="Type"] Theorem srealizes_eqv : forall c T, srealizes segs c T -> forall c', cfg_eqv c c' -> srealizes segs c' T.
Proof.
intros c T H.
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.
-
destruct Hnode as [Hfwd Hexact].
set (I' := { p : I * config | sstep_cfg segs ACFG c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
destruct (sstep_next_eqv c c' (evs i0) (nx i0) Heqv (Hfwd i0)) as (c20 & Hs0 & He0).
pose (q0 := (exist _ (i0, c20) (conj Hs0 He0) : I')).
apply (srz_conseq segs c' (t_alt (fun q : I' => t_emit (evs (fst (proj1_sig q))) (T (fst (proj1_sig q)))))).
+ apply (srz_node segs c' I' (fun q => evs (fst (proj1_sig q))) (fun q => snd (proj1_sig q))
(fun q => T (fst (proj1_sig q))) q0).
* split.
-- intros [[i c2] [Hs He]]. cbn. exact Hs.
-- intros e st Hss.
destruct (sstep_cfg_eqv0_scfg segs ACFG c' c e st (cfg_eqv_sym c c' Heqv) Hss) as (X & HssX & HX).
destruct (Hexact e X HssX) as (j & -> & ->).
destruct st as [c2|]; cbn in HX; [|contradiction].
exists (exist _ (j, c2) (conj Hss (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
* intros [[i c2] [Hs He]]. cbn. exact (IH i c2 He).
+
intros tr. split.
* intros [[[i c2] [Hs He]] Ht]. cbn in Ht. exists i. exact Ht.
* intros [i Ht].
destruct (sstep_next_eqv c c' (evs i) (nx i) Heqv (Hfwd i)) as (c2 & Hs & He).
exists (exist _ (i, c2) (conj Hs He)). cbn. exact Ht.
-
apply srz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
-
eapply srz_conseq; [apply IH; exact Heqv | exact Heq].
Qed.
End WithSegs.
