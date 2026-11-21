(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require Import PropExec CatExec CatSim StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Section Grows.
Variable segs : list Segment.

Lemma interp_eff_accesses_grows : forall t m r,
  RiscvSemantics.interp_eff_accesses segs t m = MachineOk r ->
  mem_grows m (snd (access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r H; cbn [RiscvSemantics.interp_eff_accesses] in H.
  - injection H as <-. cbn. apply mem_grows_refl.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - (* port727: 's interp_eff_accesses answers a failed load by the
       vvar test (Unmodeled / Fault), as Lib/StepFast's interp_eff0 mirrors it: neither is MachineOk *)
    destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|];
      [|destruct (RiscvSemantics.range_meets_vvar segs a (width_bytes n)); discriminate].
    destruct (RiscvSemantics.interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:Hk;
      try discriminate.
    injection H as <-. cbn. exact (IH _ m rep Hk).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (RiscvSemantics.interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [rep| |] eqn:Hk; try discriminate.
    injection H as <-. cbn.
    eapply mem_grows_trans; [apply write_to_mem_grows | exact (IH _ rep Hk)].
Qed.

Lemma decode_exec_accesses_grows : forall st w r,
  RiscvSemantics.decode_exec_accesses segs st w = MachineOk r ->
  mem_grows (ms_mem st) (ms_mem (access_value _ r)).
Proof.
  intros st w r H. unfold RiscvSemantics.decode_exec_accesses in H.
  destruct (is_ecall w).
  - injection H as <-. cbn. apply mem_grows_refl.
  - destruct (decode_any w) as [[i isz]|].
    + destruct (RiscvSemantics.interp_eff_accesses segs _ (ms_mem st)) as [rep| |] eqn:Hi; try discriminate.
      pose proof (interp_eff_accesses_grows _ _ _ Hi) as G.
      destruct (access_value _ rep) as [c m'] eqn:Hv.
      injection H as <-. cbn. cbn in G. exact G.
    + destruct (is_defined_illegal w); discriminate.
Qed.

Lemma fetch_failure_not_ok : forall m a st', RiscvSemantics.fetch_failure segs m a <> MachineOk st'.
Proof.
  intros m a st'. unfold RiscvSemantics.fetch_failure.
  (* port727: fetch_failure has more tests at (a pc in the vDSO
     text is Unmodeled): split every test; no leaf is MachineOk (the form of the ported TopLevel) *)
  cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; discriminate.
Qed.

Lemma step_mem_grows : forall st st',
  RiscvSemantics.step segs st = MachineOk st' -> mem_grows (ms_mem st) (ms_mem st').
Proof.
  intros st st' H. unfold RiscvSemantics.step, RiscvSemantics.step_accesses, drop_access_report in H.
  destruct (RiscvSemantics.fetch_word segs (ms_pc st)) as [w|].
  { destruct (RiscvSemantics.decode_exec_accesses segs st w) as [r| |] eqn:Hd; try discriminate.
    injection H as <-. exact (decode_exec_accesses_grows _ _ _ Hd). }
  destruct (RiscvSemantics.fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|].
  { destruct (RiscvSemantics.decode_exec_accesses segs st w) as [r| |] eqn:Hd; try discriminate.
    injection H as <-. exact (decode_exec_accesses_grows _ _ _ Hd). }
  destruct (RiscvSemantics.fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|].
  { destruct (RiscvSemantics.decode_exec_accesses segs st w) as [r| |] eqn:Hd; try discriminate.
    injection H as <-. exact (decode_exec_accesses_grows _ _ _ Hd). }
  destruct (RiscvSemantics.fetch_failure segs (ms_mem st) (ms_pc st)) as [s| |] eqn:Hf; try discriminate.
  exfalso. exact (fetch_failure_not_ok _ _ _ Hf).
Qed.

Theorem msteps_mem_grows : forall ms ms',
  msteps segs ms ms' -> mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 Hsvc Hstep Hrest IH].
  - apply mem_grows_refl.
  - eapply mem_grows_trans; [exact (step_mem_grows _ _ Hstep) | exact IH].
Qed.

End Grows.
End FXG.
