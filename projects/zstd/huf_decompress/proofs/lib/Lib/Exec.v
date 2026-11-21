(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (msteps_one, msteps_trans, mstep_det and 6 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Exec () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib3Lib4Exec5mstepC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib4Exec6msteps01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib4Exec6msteps02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00i59OSSVerify5KrLib3Lib4Exec6msteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib4Exec:msteps_indC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib3Lib4Exec<msteps_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Definition mstep (ms ms' : machine_state) : Prop :=
  ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'.

Inductive msteps : machine_state -> machine_state -> Prop :=
| msteps_refl : forall ms, msteps ms ms
| msteps_cons : forall ms ms1 ms2, mstep ms ms1 -> msteps ms1 ms2 -> msteps ms ms2.

Lemma msteps_one : forall ms ms', mstep ms ms' -> msteps ms ms'.
Proof. intros. eapply msteps_cons; [eassumption|apply msteps_refl]. Qed.

Lemma msteps_trans : forall a b c, msteps a b -> msteps b c -> msteps a c.
Proof. intros a b c H; induction H; intros; [assumption|]. eapply msteps_cons; eauto. Qed.

(* [comment removed for export] *)
Lemma mstep_det : forall ms a b, mstep ms a -> mstep ms b -> a = b.
Proof. intros ms a b [_ Ha] [_ Hb]. congruence. Qed.

(* [comment removed for export] *)
Lemma mstep_not_svc : forall ms ms', mstep ms ms' -> ms_svc_pending ms = None.
Proof. intros ms ms' [H _]; exact H. Qed.

(* [comment removed for export] *)

Definition evt (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms', msteps ms ms' /\ Q ms'.

Lemma evt_done : forall (Q : machine_state -> Prop) ms, Q ms -> evt Q ms.
Proof. intros Q ms H. exists ms. split; [apply msteps_refl|exact H]. Qed.

Lemma evt_step : forall Q ms ms1, mstep ms ms1 -> evt Q ms1 -> evt Q ms.
Proof. intros Q ms ms1 H (ms' & Hs & HQ). exists ms'. split; [eapply msteps_cons; eauto|exact HQ]. Qed.

(* [comment removed for export] *)
Lemma evt_cut : forall (P Q : machine_state -> Prop) ms,
  evt P ms -> (forall ms', P ms' -> evt Q ms') -> evt Q ms.
Proof.
  intros P Q ms (ms1 & H1 & HP) K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
  exists ms2. split; [eapply msteps_trans; eauto| exact HQ].
Qed.

Lemma evt_mono : forall (P Q : machine_state -> Prop) ms,
  evt P ms -> (forall ms', P ms' -> Q ms') -> evt Q ms.
Proof. intros P Q ms H K. eapply evt_cut; [exact H|]. intros ms' HP. apply evt_done, K, HP. Qed.

(* [comment removed for export] *)
Lemma evt_eq : forall Q ms ms', ms = ms' -> evt Q ms' -> evt Q ms.
Proof. intros; subst; assumption. Qed.

End WithSegs.

Arguments mstep segs ms ms' /.
