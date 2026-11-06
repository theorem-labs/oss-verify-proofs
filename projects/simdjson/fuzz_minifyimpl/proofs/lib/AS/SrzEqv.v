(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import SimInv ShapeAlg DivergeSim SpinAlg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import RegsEqv0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Instance srz_fx_as : OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS.PropExec.FPState := OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS.PropExec.fx0.
Local Instance srz_fx_lib : OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.PropExec.FPState := OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.PropExec.fx0.
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
Proof. intros [ms mo]. split; [apply ms_eqv_refl | reflexivity]. Qed.

Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
Proof.
  intros [? ?] [? ?] [? ?] [H1 H2] [G1 G2]; cbn in *. split; [eapply ms_eqv_trans; eassumption | etransitivity; eassumption].
Qed.

Lemma sstep_cfg_eqv_acfg : forall c c' e X,
  cfg_eqv c c' -> sstep_cfg segs ACFG c e X -> exists X', sstep_cfg segs ACFG c' e X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] e X [Hms Hmo] Hss; cbn in Hms, Hmo; subst mo'.
  exact (sstep_scfg_eqv segs ACFG ms ms' mo e X Hms Hss).
Qed.

(* [comment removed for export] *)
Lemma sstep_next_eqv : forall c c' e c2,
  cfg_eqv c c' -> sstep_cfg segs ACFG c e (SNext c2) -> exists c2', sstep_cfg segs ACFG c' e (SNext c2') /\ cfg_eqv c2 c2'.
Proof.
  intros c c' e c2 Heqv Hss.
  destruct (sstep_cfg_eqv_acfg c c' e (SNext c2) Heqv Hss) as (X' & Hss' & HX).
  destruct X' as [c2'| ]; cbn in HX; [|contradiction].
  exists c2'. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma silent_loop_eqv : forall P : config -> Prop,
  silent_loop segs P -> silent_loop segs (fun d => exists c, P c /\ cfg_eqv c d).
Proof.
  intros P HL d (c & HP & Heqv).
  destruct (HL c HP) as (Hh & Hsvc & ms1 & mo1 & Hacc & HP1).
  destruct c as [ms mo]; destruct d as [ms' mo']. destruct Heqv as [Hms Hmo]; cbn in *. subst mo'.
  pose proof Hms as (_ & _ & _ & Hsv & _ & _ & _ & _).
  split; [exact Hh|]. split; [congruence|].
  pose proof (mi_account_step_eqv segs ms ms' mo Hms) as K. rewrite Hacc in K.
  destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |]; try contradiction.
  destruct K as [Heq <-].
  exists ms1', mo1. split; [reflexivity|]. exists (mkCfg ms1 mo1). split; [exact HP1|]. split; [exact Heq | reflexivity].
Qed.

Theorem srealizes_eqv : forall c T, srealizes segs c T -> forall c', cfg_eqv c c' -> srealizes segs c' T.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
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
           destruct (sstep_cfg_eqv_acfg c' c e st (cfg_eqv_sym c c' Heqv) Hss) as (X & HssX & HX).
           destruct (Hexact e X HssX) as (j & -> & ->).
           destruct st as [c2|]; cbn in HX; [|contradiction].
           exists (exist _ (j, c2) (conj Hss (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
      * intros [[i c2] [Hs He]]. cbn. exact (IH i c2 He).
    + (* [comment removed for export] *)
      intros tr. split.
      * intros [[[i c2] [Hs He]] Ht]. cbn in Ht. exists i. exact Ht.
      * intros [i Ht].
        destruct (sstep_next_eqv c c' (evs i) (nx i) Heqv (Hfwd i)) as (c2 & Hs & He).
        exists (exist _ (i, c2) (conj Hs He)). cbn. exact Ht.
  - (* [comment removed for export] *)
    apply srz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
  - (* [comment removed for export] *)
    eapply srz_conseq; [apply IH; exact Heqv | exact Heq].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mkst_MS : forall R pc m ro,
  OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS.PropExec.mkst R pc m ro = MS R bvmap_empty pc (Z_to_bv 32 0) None m ro.
Proof. reflexivity. Qed.

Lemma cfg_eqv_regs : forall R R' F pc fc rv m ro mo,
  regs_eqv0 R R' -> cfg_eqv (mkCfg (MS R F pc fc rv m ro) mo) (mkCfg (MS R' F pc fc rv m ro) mo).
Proof.
  intros. split; [|reflexivity]. split; [assumption|]. split; [apply regs_eqv_refl|]. repeat split; reflexivity.
Qed.

End WithSegs.
