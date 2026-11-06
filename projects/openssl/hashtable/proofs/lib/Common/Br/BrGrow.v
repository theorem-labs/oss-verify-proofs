(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Grow.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma write_to_mem_def : forall bs m a x, m x <> None -> write_to_mem m a bs x <> None.
Proof.
  induction bs as [|b bs IH]; intros m a x Hx; [exact Hx|]. cbn [write_to_mem]. apply IH.
  destruct (bv_eqb x a); [discriminate | exact Hx].
Qed.

Lemma interp_grows : forall t m report,
  interp_eff_accesses segs t m = MachineOk report ->
  forall x, m x <> None -> snd (@access_value _ report) x <> None.
Proof.
  induction t as [c | c | c | c | c | c | n a k IH | n a v k IH];
    intros m report H x Hx; cbn [interp_eff_accesses] in H; try discriminate H.
  - inversion H; subst. exact Hx.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs |]; [| discriminate H].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m)
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [access_value]. exact (IH _ m r0 E x Hx).
  - destruct (store_ok segs m a (width_bytes n)); [| discriminate H].
    destruct (interp_eff_accesses segs k
                (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [access_value]. apply (IH _ r0 E x). apply write_to_mem_def. exact Hx.
Qed.

Lemma decode_exec_grows : forall st w report,
  decode_exec_accesses segs st w = MachineOk report ->
  forall x, ms_mem st x <> None -> ms_mem (@access_value _ report) x <> None.
Proof.
  intros st w report H x Hx. unfold decode_exec_accesses in H.
  destruct (is_ecall w).
  - inversion H; subst. exact Hx.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate H].
    match type of H with context [interp_eff_accesses segs ?t ?m] =>
      destruct (interp_eff_accesses segs t m) as [r0 | |] eqn:E; try discriminate H end.
    pose proof (interp_grows _ _ _ E x Hx) as Hg.
    destruct (@access_value _ r0) as [c m']. inversion H; subst. cbn [access_value ms_mem]. exact Hg.
Qed.

Theorem step_mem_grows : forall ms ms',
  step segs ms = MachineOk ms' -> forall x, ms_mem ms x <> None -> ms_mem ms' x <> None.
Proof.
  intros ms ms' Hs x Hx. unfold step in Hs.
  destruct (step_accesses segs ms) as [report | |] eqn:Hacc; try discriminate Hs.
  cbn [drop_access_report] in Hs. inversion Hs; subst ms'. clear Hs.
  unfold step_accesses in Hacc.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (decode_exec_grows _ _ _ Hacc x Hx)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (decode_exec_grows _ _ _ Hacc x Hx)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (decode_exec_grows _ _ _ Hacc x Hx)|].
  unfold fetch_failure in Hacc.
  repeat match type of Hacc with context [if ?c then _ else _] => destruct c end; discriminate Hacc.
Qed.

Theorem rsteps_mem_grows : forall n ms ms',
  rsteps segs n ms = MachineOk ms' -> forall x, ms_mem ms x <> None -> ms_mem ms' x <> None.
Proof.
  induction n as [|n IH]; intros ms ms' H x Hx; cbn [rsteps] in H.
  - inversion H; subst. exact Hx.
  - destruct (ms_svc_pending ms); [inversion H; subst; exact Hx|].
    destruct (step segs ms) as [ms1 | |] eqn:Hs; try discriminate H.
    exact (IH ms1 ms' H x (step_mem_grows ms ms1 Hs x Hx)).
Qed.
End Grow.
