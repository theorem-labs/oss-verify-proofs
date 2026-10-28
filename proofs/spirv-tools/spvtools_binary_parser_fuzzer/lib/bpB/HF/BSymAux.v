(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BFrame BSymExec BSymExec2 BSymExec2Sound BSymRun BRefMemcpyLib BAgentLib.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition sregion : Type := (saddr * Z)%type.

Definition rdenot (E : env) (r : sregion) : word * Z :=
  (Z_to_bv 64 (estart E (fst r)), snd r).

Fixpoint entry_covered (rs : list sregion) (a : saddr) (w : nat) : bool :=
  match rs with
  | [] => false
  | (SA rb rk, n) :: rest =>
      (expr_eqb (a_base a) rb && Z.leb rk (a_off a) && Z.leb (a_off a + Z.of_nat w) (rk + n))%bool
      || entry_covered rest a w
  end.

Fixpoint log_covered (rs : list sregion) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE a w _ :: rest => entry_covered rs a w && log_covered rs rest
  end.

Definition regions_flat (E : env) (rs : list sregion) : Prop :=
  forall r, In r rs -> flat E (fst r) (snd r).

Lemma entry_covered_in : forall E rs a w (x : word),
  entry_covered rs a w = true -> regions_flat E rs -> flat E a (Z.of_nat w) ->
  (estart E a <= bv_unsigned x < estart E a + Z.of_nat w)%Z ->
  ~ outside x (map (rdenot E) rs).
Proof.
  intros E rs a w x. induction rs as [|[[rb rk] n] rest IH]; cbn [entry_covered map outside]; intros Hc Hrf Hfa Hx.
  - discriminate.
  - apply orb_prop in Hc as [Hc|Hc].
    + apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
      apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
      intros [Hno _]. apply Hno. unfold in_rng, rdenot. cbn [fst snd].
      pose proof (Hrf _ (or_introl eq_refl)) as Hfr. cbn [fst snd] in Hfr.
      unfold flat, estart in *. cbn [a_base a_off] in *. rewrite <- H1 in *.
      rewrite u64_lit by lia. lia.
    + intros [_ Hout]. apply (IH Hc); [| exact Hfa | exact Hx | exact Hout].
      intros r Hr. apply Hrf. right. exact Hr.
Qed.

Lemma frame_layer : forall E rs m a w (v : word),
  entry_covered rs a w = true -> regions_flat E rs -> flat E a (Z.of_nat w) ->
  frame_mod m (wbytes m (adenot E a) (word_to_le_bytes w v)) (map (rdenot E) rs).
Proof.
  intros E rs m a w v Hc Hrf Hfa.
  pose proof (flat_u E a _ Hfa) as Hu.
  eapply frame_mod_weaken.
  2:{ apply frame_mod_wbytes. rewrite length_N_to_le_bytes, Hu. destruct Hfa as (?&?&?&?). lia. }
  intros x Hout. cbn [outside]. split; [|exact I].
  intros Hin. unfold in_rng in Hin. rewrite length_N_to_le_bytes, Hu in Hin.
  exact (entry_covered_in E rs a w x Hc Hrf Hfa Hin Hout).
Qed.

Theorem log_covered_frame : forall E base rs log,
  log_covered rs log = true -> regions_flat E rs -> log_flat E log ->
  frame_mod base (mem_denot E base log) (map (rdenot E) rs).
Proof.
  intros E base rs log. induction log as [|[a w v] rest IH]; cbn [log_covered mem_denot log_flat]; intros Hc Hrf Hlf.
  - apply frame_mod_refl.
  - apply andb_prop in Hc as [H1 H2]. destruct Hlf as (Hw & Hfa & Hlf').
    eapply frame_mod_trans_same; [apply IH; assumption|].
    apply frame_layer; assumption.
Qed.

Lemma regs_ok_same : forall E sr sr' R R' (r : reg),
  regs_ok E sr R -> regs_ok E sr' R' -> sr_get sr' r = sr_get sr r -> getr R' r = getr R r.
Proof. intros E sr sr' R R' r HR HR' Hs. rewrite (HR r), (HR' r), Hs. reflexivity. Qed.

Fixpoint same_regs (sr sr' : list expr) (rs : list reg) : bool :=
  match rs with
  | [] => true
  | r :: rest => expr_eqb (sr_get sr' r) (sr_get sr r) && same_regs sr sr' rest
  end.

Lemma same_regs_sound : forall E sr sr' R R' rs,
  same_regs sr sr' rs = true -> regs_ok E sr R -> regs_ok E sr' R' ->
  forall r, In r rs -> getr R' r = getr R r.
Proof.
  intros E sr sr' R R' rs. induction rs as [|r0 rest IH]; cbn [same_regs]; intros Hs HR HR' r Hin.
  - destruct Hin.
  - apply andb_prop in Hs as [H1 H2]. destruct Hin as [<-|Hin].
    + apply (regs_ok_same E sr sr' R R' r0 HR HR'). apply expr_eqb_eq. exact H1.
    + apply IH; assumption.
Qed.

Lemma keeps_cs_of_same : forall E sr sr' R R',
  same_regs sr sr' callee_saved = true -> regs_ok E sr R -> regs_ok E sr' R' -> keeps_cs R R'.
Proof. intros E sr sr' R R' Hs HR HR' r Hin. eapply same_regs_sound; eassumption. Qed.

Section FXP1. Context {fx : DFP}.

End FXP1.
