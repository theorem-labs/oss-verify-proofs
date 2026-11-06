(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2 X1bn.
Import ListNotations.
Open Scope Z_scope.

Definition mem_quiet (mo : Model) : Prop := m_vm_lazy mo = [] /\ m_vm_materialized mo = [].

Definition step_live (B : Z) (mo' : Model) : Prop :=
live_bytes (vm_maps (m_vmmaps mo')) <= B /\ mem_quiet mo'.

Definition LBUDGET : Z := 2147483648.

Definition nroom (B : Z) (n : node) (mo : Model) : Prop :=
match n with
| NMmap addr len prot flags => addr = 0 -> flags = MAP_PRIVATE + MAP_ANONYMOUS ->
live_bytes (vm_maps (m_vmmaps mo)) + mmap_len len <= B /\ vm_gap_available (m_vmmaps mo) (mmap_len len) = true
| _ => True
end.

Lemma nroom_mono : forall B B' n mo, B <= B' -> nroom B n mo -> nroom B' n mo.
Proof.
intros B B' n mo HB H. destruct n; cbn in *; auto. intros E1 E2. destruct (H E1 E2) as [H1 H2]. split; [lia| exact H2].
Qed.

Fixpoint tlive {R} (B : Z) (t : itree node R) (mo : Model) : Prop :=
match t with
| Ret _ => True
| Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs ->
(nroom B n mo /\ step_live B mo') /\ tlive B (k rsp) mo'
end.

Lemma tlive_mono : forall {R} (t : itree node R) mo B B', B <= B' -> tlive B t mo -> tlive B' t mo.
Proof.
intros R t. induction t as [r|n k IH]; intros mo B B' HB H; cbn in *; [exact I|].
intros rsp mo' evs Hs. destruct (H rsp mo' evs Hs) as [[Hr [H1 Hq]] H2].
split; [split; [exact (nroom_mono B B' n mo HB Hr)| split; [lia| exact Hq]]| eapply IH; eauto].
Qed.

Definition nstep_live (B : Z) (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
nstep n mo rsp mo' evs /\ (nroom B n mo /\ live_bytes (vm_maps (m_vmmaps mo')) <= B).

Lemma texit_live_of_tlive : forall {R} (t : itree node R) mo tr B,
tlive B t mo -> texit nstep nexit t mo tr -> texit (nstep_live B) nexit t mo tr.
Proof.
intros R t. induction t as [r|n k IH]; intros mo tr B HL HX; cbn in *; [exact HX|].
destruct HX as [H|(rsp & mo' & evs & tr' & Hs & Hx & ->)]; [left; exact H| right].
destruct (HL rsp mo' evs Hs) as [[Hr [Hb _]] HL']. exists rsp, mo', evs, tr'. split; [split; [exact Hs| split; [exact Hr| exact Hb]]|]. split; [eapply IH; eauto| reflexivity].
Qed.

Lemma tpath_live_of_tlive : forall {R} (t : itree node R) mo tr r mo' B,
tlive B t mo -> tpath nstep t mo tr r mo' -> tpath (nstep_live B) t mo tr r mo'.
Proof.
intros R t. induction t as [r0|n k IH]; intros mo tr r mo' B HL HP; cbn in *; [exact HP|].
destruct HP as (rsp & mo1 & evs & tr' & Hs & Hp & ->).
destruct (HL rsp mo1 evs Hs) as [[Hr [Hb _]] HL']. exists rsp, mo1, evs, tr'. split; [split; [exact Hs| split; [exact Hr| exact Hb]]|]. split; [eapply IH; eauto| reflexivity].
Qed.
