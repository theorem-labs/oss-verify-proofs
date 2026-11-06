(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Frame Regs6ss.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Theorem realizes0_eqv : forall c T, ShapeAlg.realizes0 segs c T ->
  forall c', cfg_eqv c c' -> ShapeAlg.realizes0 segs c' T.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.
  - destruct c as [ms mo], c' as [ms' mo']. destruct Heqv as [Hms Hmo]; cbn in Hms, Hmo. subst mo'.
    destruct Hnode as [Hn1 Hn2].
    apply (ShapeAlg.rz_node0 segs (mkCfg ms' mo) I evs (fun i => xport_cfg segs ms ms' (nx i)) T i0).
    + split.
      * intros i. exact (proj1 (sstep_xport segs ms ms' mo (evs i) (SNext (nx i)) Hms (Hn1 i))).
      * intros e st Hst'.
        destruct (sstep_xport segs ms' ms mo e st (ms_eqv_sym _ _ Hms) Hst') as [S _].
        destruct (Hn2 e (xport segs ms' ms st) S) as (i & -> & Hx).
        exists i. split; [reflexivity|].
        rewrite <- (xport_round_trip segs ms ms' mo (evs i) st Hms Hst'). rewrite Hx. reflexivity.
    + intros i. apply (IH i).
      exact (proj2 (sstep_xport segs ms ms' mo (evs i) (SNext (nx i)) Hms (Hn1 i))).
  - apply ShapeAlg.rz_halt0. destruct Heqv as [_ <-]. exact Hh.
  - eapply ShapeAlg.rz_conseq0; [apply IH; exact Heqv| exact Heq].
Qed.

(* [comment removed for export] *)
Lemma budget_refused_at_eqv : forall c c', cfg_eqv c c' ->
  budget_refused_at segs c -> budget_refused_at segs c'.
Proof.
  intros [ms mo] [ms' mo'] [Hms Hmo] [Hh H]; cbn [cfg_ms cfg_model] in *. subst mo'.
  pose proof Hms as (_ & _ & _ & Hsvc & _).
  split; [exact Hh|]. cbn [cfg_ms cfg_model].
  destruct H as [(Hn & report & Hstep & Hmat) | (x8 & Hx8 & H)].
  - left. split; [congruence|].
    pose proof (step_accesses_eqv segs ms ms' Hms) as Hrep. rewrite Hstep in Hrep.
    destruct (RiscvSemantics.step_accesses segs ms') as [report'| |] eqn:E; cbn in Hrep; try contradiction.
    destruct Hrep as [_ Hacc]. exists report'. split; [reflexivity|]. rewrite <- Hacc. exact Hmat.
  - right. exists x8. split; [congruence|]. rewrite <- (sys_input_eqv segs ms ms' x8 Hms). exact H.
Qed.

Lemma star_eqv : forall c tr c1, star_cfg segs ACFG c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star_cfg segs ACFG c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_cfg_refl | exact Heqv].
  - destruct c1 as [ms mo], c' as [ms' mo']. destruct Heqv as [Hms Hmo]; cbn in Hms, Hmo. subst mo'.
    destruct (sstep_xport segs ms ms' mo evs (SNext c2) Hms Hss) as [Hst Hto]. cbn [xport to_eqv] in Hst, Hto.
    destruct (IH _ Hto) as (c3' & Hstar' & Heqv'). exists c3'.
    split; [eapply star_cfg_step; [exact Hst | exact Hstar'] | exact Heqv'].
Qed.

Section World.
Context {BW : BWorld}.

Lemma never_excused_eqv : forall c c', cfg_eqv c c' ->
  never_excused segs c' -> never_excused segs c.
Proof.
  intros c c' Heqv Hne tr c1 Hstar Hex.
  destruct (star_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & Heqv1).
  apply (Hne tr c1' Hstar'). unfold bw_excuse in *.
  destruct bw_on; [exact (budget_refused_at_eqv c1 c1' Heqv1 Hex) | exact Hex].
Qed.

Theorem realizes_eqv : forall c T, ShapeAlg.realizes segs c T ->
  forall c', cfg_eqv c c' -> ShapeAlg.realizes segs c' T.
Proof.
  intros c T H c' Heqv. constructor. intros Hne'.
  apply (realizes0_eqv c T); [| exact Heqv].
  apply (ShapeAlg.rz_unwrap segs c T H). exact (never_excused_eqv c c' Heqv Hne').
Qed.

Corollary realizes_ms_eqv : forall ms ms' mo T,
  ms_eqv ms ms' -> ShapeAlg.realizes segs (mkCfg ms mo) T -> ShapeAlg.realizes segs (mkCfg ms' mo) T.
Proof.
  intros ms ms' mo T Heqv H. apply (realizes_eqv _ T H). split; [exact Heqv| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma getr_reg_get : forall R (r : reg), bv_eqb r 0 = false -> PropExec.getr R r = reg_get R r.
Proof. intros R r Hr. unfold PropExec.getr. rewrite Hr. reflexivity. Qed.

(* [comment removed for export] *)
Theorem realizes_of_mkR : forall (R : bvmap 5 word) pc m rom mo T
    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  PropExec.getr R 1 = x1 -> PropExec.getr R 2 = x2 -> PropExec.getr R 3 = x3 -> PropExec.getr R 4 = x4 ->
  PropExec.getr R 5 = x5 -> PropExec.getr R 6 = x6 -> PropExec.getr R 7 = x7 -> PropExec.getr R 8 = x8 ->
  PropExec.getr R 9 = x9 -> PropExec.getr R 10 = x10 -> PropExec.getr R 11 = x11 -> PropExec.getr R 12 = x12 ->
  PropExec.getr R 13 = x13 -> PropExec.getr R 14 = x14 -> PropExec.getr R 15 = x15 -> PropExec.getr R 16 = x16 ->
  PropExec.getr R 17 = x17 -> PropExec.getr R 18 = x18 -> PropExec.getr R 19 = x19 -> PropExec.getr R 20 = x20 ->
  PropExec.getr R 21 = x21 -> PropExec.getr R 22 = x22 -> PropExec.getr R 23 = x23 -> PropExec.getr R 24 = x24 ->
  PropExec.getr R 25 = x25 -> PropExec.getr R 26 = x26 -> PropExec.getr R 27 = x27 -> PropExec.getr R 28 = x28 ->
  PropExec.getr R 29 = x29 -> PropExec.getr R 30 = x30 -> PropExec.getr R 31 = x31 ->
  ShapeAlg.realizes segs (mkCfg (PropExec.mkst (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                                                    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) pc m rom) mo) T ->
  ShapeAlg.realizes segs (mkCfg (PropExec.mkst R pc m rom) mo) T.
Proof.
  intros. eapply realizes_ms_eqv; [| eassumption].
  split; [| repeat split].
  apply xregs_eqv_sym. apply mkR_eqv_of; rewrite <- getr_reg_get by reflexivity; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End World.
End WithSegs.
