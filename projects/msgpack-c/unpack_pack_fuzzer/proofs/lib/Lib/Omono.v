(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Exec.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Unset Lia Cache.

Section WithSegs.
Variable segs : list Segment.

Definition omono (m m' : word -> option byte) : Prop := forall x, m x <> None -> m' x <> None.

Lemma omono_refl : forall m, omono m m.
Proof. intros m x H. exact H. Qed.
Lemma omono_trans : forall m1 m2 m3, omono m1 m2 -> omono m2 m3 -> omono m1 m3.
Proof. intros m1 m2 m3 A B x H. exact (B x (A x H)). Qed.

Lemma write_to_mem_omono : forall m a bs, omono m (write_to_mem m a bs).
Proof.
  intros m a bs. revert m a. induction bs as [|b bs IH]; intros m a x H; cbn [write_to_mem]; [exact H|].
  apply IH. destruct (bv_eqb x a); [discriminate| exact H].
Qed.

Lemma interp_omono : forall t m r,
  interp_eff_accesses segs t m = MachineOk r -> omono m (snd (access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r H; cbn [interp_eff_accesses] in H; try discriminate H.
  - injection H as <-. cbn. apply omono_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:R; try discriminate.
    injection H as <-. cbn. exact (IH _ m rep R).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [rep| |] eqn:R; try discriminate.
    injection H as <-. cbn. eapply omono_trans; [apply write_to_mem_omono| exact (IH _ rep R)].
Qed.

Lemma decode_exec_omono : forall st w st',
  decode_exec segs st w = MachineOk st' -> omono (ms_mem st) (ms_mem st').
Proof.
  intros st w st' H. unfold decode_exec, decode_exec_accesses in H.
  destruct (is_ecall w).
  - cbn in H. injection H as <-. cbn. apply omono_refl.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate H].
    destruct (interp_eff_accesses segs _ (ms_mem st)) as [rep| |] eqn:R; try discriminate H.
    pose proof (interp_omono _ _ _ R) as OM.
    destruct (access_value _ rep) as [c m'] eqn:AV. cbn in H. injection H as <-. cbn. cbn in OM. exact OM.
Qed.

Lemma step_omono : forall st st', RiscvSemantics.step segs st = MachineOk st' -> omono (ms_mem st) (ms_mem st').
Proof.
  intros st st' H. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc st)) as [w|].
  { exact (decode_exec_omono st w st' H). }
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|].
  { exact (decode_exec_omono st w st' H). }
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|].
  { exact (decode_exec_omono st w st' H). }
  destruct (fetch_failure segs (ms_mem st) (ms_pc st)) as [st2| |] eqn:F; cbn in H; try discriminate H.
  unfold fetch_failure in F. destruct (negb _); [discriminate F|]. destruct (_ : bool) in F; discriminate F.
Qed.

Lemma msteps_omono : forall ms ms', msteps segs ms ms' -> omono (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 [_ S] _ IH]; [apply omono_refl|].
  eapply omono_trans; [exact (step_omono _ _ S)| exact IH].
Qed.

Lemma evt_omono : forall (Q : machine_state -> Prop) ms,
  evt segs Q ms -> evt segs (fun ms' => Q ms' /\ omono (ms_mem ms) (ms_mem ms')) ms.
Proof.
  intros Q ms (ms' & R & HQ). exists ms'. split; [exact R|]. split; [exact HQ|]. exact (msteps_omono _ _ R).
Qed.

End WithSegs.
