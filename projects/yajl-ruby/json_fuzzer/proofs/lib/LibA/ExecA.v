(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition acc := (word * nat)%type.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition resA (r : machine_result (access_report machine_state))
  : machine_result (machine_state * list acc) :=
  match r with
  | MachineOk rep => MachineOk (@access_value _ rep, @accessed_ranges _ rep)
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

Definition lift_resultA (ro : word -> option byte)
  (r : machine_result (access_report (core * (word -> option byte))))
  : machine_result (machine_state * list acc) :=
  match r with
  | MachineOk rep => let '(c, m') := @access_value _ rep in
                     MachineOk (MS_of_core c m' ro, @accessed_ranges _ rep)
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

(* [comment removed for export] *)
Lemma step_genA : forall segs R F pc fc rv m ro w i sz,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  resA (RiscvSemantics.step_accesses segs (MS R F pc fc rv m ro)) =
  lift_resultA ro (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m).
Proof.
  intros segs R F pc fc rv m ro w i sz Hf He Hd.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He, Hd.
  cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS].
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i _) m) as [[[c m'] rs]| |]; reflexivity.
Qed.

Lemma step_ecall_genA : forall segs R F pc fc rv m ro w,
  fetch_word segs pc = Some w ->
  is_ecall w = true ->
  resA (RiscvSemantics.step_accesses segs (MS R F pc fc rv m ro)) =
  MachineOk (MSsvc R F pc (if is_x0 17 then w0 else reg_get R 17) fc rv m ro, []).
Proof.
  intros segs R F pc fc rv m ro w Hf He.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma resA_drop : forall segs ms ms' rs,
  resA (RiscvSemantics.step_accesses segs ms) = MachineOk (ms', rs) ->
  RiscvSemantics.step segs ms = MachineOk ms'.
Proof.
  intros segs ms ms' rs H. unfold RiscvSemantics.step.
  destruct (RiscvSemantics.step_accesses segs ms) as [[v a]| |]; cbn in *; [|discriminate|discriminate].
  inversion H; subst. reflexivity.
Qed.

Lemma resA_report : forall segs ms ms' rs,
  resA (RiscvSemantics.step_accesses segs ms) = MachineOk (ms', rs) ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' rs).
Proof.
  intros segs ms ms' rs H.
  destruct (RiscvSemantics.step_accesses segs ms) as [[v a]| |]; cbn in *; [|discriminate|discriminate].
  inversion H; subst. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition mstepA (ms ms' : machine_state) (rs : list acc) : Prop :=
  ms_svc_pending ms = None /\ resA (RiscvSemantics.step_accesses segs ms) = MachineOk (ms', rs).

Lemma mstepA_mstep : forall ms ms' rs, mstepA ms ms' rs -> mstep segs ms ms'.
Proof. intros ms ms' rs [H1 H2]. split; [exact H1| eapply resA_drop; exact H2]. Qed.

Lemma mstepA_det : forall ms a b ra rb, mstepA ms a ra -> mstepA ms b rb -> a = b /\ ra = rb.
Proof. intros ms a b ra rb [_ Ha] [_ Hb]. rewrite Ha in Hb. inversion Hb. auto. Qed.

Section WithPolicy.
(* [comment removed for export] *)
Variable P : acc -> Prop.

Inductive mstepsA : machine_state -> machine_state -> Prop :=
| mstepsA_refl : forall ms, mstepsA ms ms
| mstepsA_cons : forall ms ms1 ms2 rs, mstepA ms ms1 rs -> Forall P rs -> mstepsA ms1 ms2 -> mstepsA ms ms2.

Lemma mstepsA_one : forall ms ms' rs, mstepA ms ms' rs -> Forall P rs -> mstepsA ms ms'.
Proof. intros. eapply mstepsA_cons; [eassumption|eassumption|apply mstepsA_refl]. Qed.

Lemma mstepsA_trans : forall a b c, mstepsA a b -> mstepsA b c -> mstepsA a c.
Proof. intros a b c H; induction H; intros; [assumption|]. eapply mstepsA_cons; eauto. Qed.

(* [comment removed for export] *)
Lemma mstepsA_msteps : forall a b, mstepsA a b -> msteps segs a b.
Proof.
  intros a b H; induction H; [apply msteps_refl|].
  eapply msteps_cons; [eapply mstepA_mstep; eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition evtA (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms', mstepsA ms ms' /\ Q ms'.

Lemma evtA_done : forall (Q : machine_state -> Prop) ms, Q ms -> evtA Q ms.
Proof. intros Q ms H. exists ms. split; [apply mstepsA_refl|exact H]. Qed.

Lemma evtA_step : forall Q ms ms1 rs, mstepA ms ms1 rs -> Forall P rs -> evtA Q ms1 -> evtA Q ms.
Proof. intros Q ms ms1 rs H HP (ms' & Hs & HQ). exists ms'. split; [eapply mstepsA_cons; eauto|exact HQ]. Qed.

Lemma evtA_cut : forall (P0 Q : machine_state -> Prop) ms,
  evtA P0 ms -> (forall ms', P0 ms' -> evtA Q ms') -> evtA Q ms.
Proof.
  intros P0 Q ms (ms1 & H1 & HP) K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
  exists ms2. split; [eapply mstepsA_trans; eauto| exact HQ].
Qed.

Lemma evtA_mono : forall (P0 Q : machine_state -> Prop) ms,
  evtA P0 ms -> (forall ms', P0 ms' -> Q ms') -> evtA Q ms.
Proof. intros P0 Q ms H K. eapply evtA_cut; [exact H|]. intros ms' HP. apply evtA_done, K, HP. Qed.

Lemma evtA_eq : forall Q ms ms', ms = ms' -> evtA Q ms' -> evtA Q ms.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma evtA_evt : forall Q ms, evtA Q ms -> evt segs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [apply mstepsA_msteps; exact H| exact HQ]. Qed.

End WithPolicy.

(* [comment removed for export] *)
Lemma mstepsA_weaken : forall (P P' : acc -> Prop) a b,
  (forall x, P x -> P' x) -> mstepsA P a b -> mstepsA P' a b.
Proof.
  intros P P' a b HPP H; induction H; [apply mstepsA_refl|].
  eapply mstepsA_cons; eauto. eapply Forall_impl; eauto.
Qed.

Lemma evtA_weaken : forall (P P' : acc -> Prop) Q ms,
  (forall x, P x -> P' x) -> evtA P Q ms -> evtA P' Q ms.
Proof. intros P P' Q ms HPP (ms' & H & HQ). exists ms'. split; [eapply mstepsA_weaken; eauto| exact HQ]. Qed.

(* [comment removed for export] *)

End WithSegs.

Arguments mstepA segs ms ms' rs /.
