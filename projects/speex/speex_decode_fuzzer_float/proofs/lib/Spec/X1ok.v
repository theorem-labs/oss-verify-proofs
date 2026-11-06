(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Export X1pe X1os X1oq X1oz X1oy X1op.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ra X1qu X1r3 X1r4 X1og X1r9 X1or X1p5 X1q7.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Definition raw_malloc_LQ := raw_malloc_L malloc_core_fq_proof.
Definition raw_free_LQ := raw_free_L.

Check (raw_malloc_LQ : forall X P n, 0 <= n ->
mspecL LBUDGET (fun s mo => QI X P s mo /\ ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET) (raw_malloc n)
(fun r s mo => match r with
| Some p => QI ((p, n) :: X) P s mo /\ n < 2 ^ 63
| None => QI X P s mo
end)).
Check (raw_free_LQ : forall X P p n, mspecL LBUDGET (QI ((p, n) :: X) P) (raw_free p) (fun _ => QI X P)).

Lemma QI_step_live X P s mo : QI X P s mo -> step_live LBUDGET mo.
Proof.
intros HQ. split; [exact (QI_live _ _ _ _ HQ)|].
destruct HQ as [(st & L & BL & LS & _ & _ & _ & _ & HK & HL & _) _].
apply mem_quiet_of; [exact (kl_minv _ _ _ HK)| exact (LI_nomat _ _ HL)].
Qed.

Lemma m_vm_with_fds v m : m_vm (with_fds v m) = m_vm m.
Proof. destruct m; reflexivity. Qed.
Lemma m_vm_with_tid v m : m_vm (with_tid v m) = m_vm m.
Proof. destruct m; reflexivity. Qed.

Theorem raw_free_opt_LQ X P (o : option bptr) n :
mspecL LBUDGET (QI (match o with Some p => (p, n) :: X | None => X end) P) (raw_free_opt o) (fun _ => QI X P).
Proof.
destruct o as [p|]; cbn [raw_free_opt]; [apply raw_free_LQ|]. apply mspecL_ret. intros s mo H. exact H.
Qed.

Theorem raw_calloc_LQ X P m n : 0 <= m -> 0 <= n ->
mspecL LBUDGET (fun s mo => QI X P s mo /\ ROOMX X P (n * m) /\ PHI P + R63X X + bigb (n * m) <= LBUDGET) (raw_calloc m n)
(fun r s mo => match r with
| Some p => QI ((p, n * m) :: X) P s mo /\ n * m < 2 ^ 63
| None => QI X P s mo
end).
Proof.
intros Hm Hn. unfold raw_calloc.
destruct (negb (n =? 0) && ((2 ^ 64 - 1) / n <? m)); [apply mspecL_ret; intros s mo [H _]; exact H|].
apply raw_malloc_LQ. nia.
Qed.

Theorem raw_realloc_LQ X P p k n : 0 <= n < MMAP_THRESHOLD ->
mspecL LBUDGET (fun s mo => QI ((p, k) :: X) P s mo /\ ROOMX ((p, k) :: X) P n) (raw_realloc p n)
(fun r s mo => match r with
| Some q => exists k', (k' = k \/ k' = n) /\ QI ((q, k') :: X) P s mo
| None => QI ((p, k) :: X) P s mo
end).
Proof.
intros Hn. unfold raw_realloc.
destruct (size_overflows n); [apply mspecL_ret; intros s mo [H _]; exact H|].
destruct (negb (ptop p)); [apply mspecL_munr|].
eapply mspecL_bind; [apply mspecL_get|]. intros s0.
apply mspecL_pointwise. intros s1 mo1 [-> [HQ HR]].
destruct (s_slots (ps_m s1) !! fst p) as [[g idx]|]; [| apply mspecL_munr].
destruct ((n <=? _) && (n <? MMAP_THRESHOLD) && (_ <=? size_to_class n + 1)).
{ apply mspecL_ret. intros s mo [-> ->]. exists k. split; [left; reflexivity| exact HQ]. }
destruct ((48 <=? _) && (MMAP_THRESHOLD <=? n)); [apply mspecL_munr|].
eapply mspecL_bind.
{ eapply mspecL_pre; [apply (raw_malloc_LQ ((p, k) :: X) P n); lia|].
intros s mo [-> ->]. split; [exact HQ|]. split; [exact HR|].
rewrite (bigb_small n) by lia. destruct HQ as [_ HB]. lia. }
intros [q|]; cbn beta iota.
- apply mspecL_pure. intros _. eapply mspecL_seq.
+ eapply mspecL_pre; [apply (raw_free_LQ ((q, n) :: X) P p k)|]. intros s mo H. eapply QI_perm; [apply perm_swap| exact H].
+ intros _. apply mspecL_ret. intros s mo H. exists n. split; [right; reflexivity| exact H].
- apply mspecL_ret. intros s mo H. exact H.
Qed.
