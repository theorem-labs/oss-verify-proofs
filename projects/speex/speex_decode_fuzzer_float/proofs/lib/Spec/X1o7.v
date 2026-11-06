(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ra X1qu X1ri X1r3 X1r4
X1nt X1rh X1re X1qz X1rg X1od X1rm X1o8 X1r6
X1r8 X1nu X1ob X1o3 X1o5 X1o4 X1o6 X1o0 X1ny X1nz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Definition Km_ok (Km : Model -> Prop) : Prop := forall mo mo', Km mo -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> Km mo'.

Definition Klib (Km : Model -> Prop) (so : stdout_st) : PState -> Model -> Prop := fun s mo => Km mo /\ ps_so s = so.

Lemma Klib_fstable2 : forall Km so, Km_ok Km -> fstable2 (Klib Km so).
Proof. intros Km so HKm s mo s' mo' [H1 H2] Hso Hfd Hfs. split; [eapply HKm; eauto| congruence]. Qed.

Lemma SoA_fstable : forall Km so tr0, Km_ok Km -> fstable (SoA ps_so Km so tr0).
Proof.
intros Km so tr0 HKm s mo tr s' mo' (H1 & H2 & H3) Hso Hfd Hfs. split; [eapply HKm; eauto|]. split; [congruence| exact H3].
Qed.

Section TargetE.
Variable sel : option bool.
Variable X : list event -> Prop.

Lemma size_ok : forall n, n < 2^62 -> size_overflows n = false.
Proof. intros n H. unfold size_overflows. apply Z.leb_gt. lia. Qed.

Lemma REL_fuzz_one : forall (K : PState -> Model -> Prop), fstable2 K ->
forall payload, REL sel X K erase (fuzz_one payload) (p_fuzz_one payload).
Proof.
intros K HK payload. unfold fuzz_one.
apply (REL_LLVMFuzzerTestOneInput sel X K).
- exact (REL_raw_malloc sel X K HK).
- exact (REL_raw_calloc sel X K HK).
- intros p [] n. exact (REL_raw_realloc sel X K HK p n).
- intros p []. exact (REL_raw_free sel X K HK p).
- exact (REL_s_notify sel X K).
- exact (REL_s_warning sel X K).
- apply REL_bits_unpack_unsigned_M.
- apply REL_bits_peek_M.
- apply REL_bits_advance_M.
- apply REL_bits_remaining_M.
Qed.

Lemma fuzz_one_E : forall Km so payload tr0, Km_ok Km ->
mspecE sel X (SoA ps_so Km so tr0) (fuzz_one payload)
(fun rc s mo tr => exists eb, canon_fuzz payload = (0, eb) /\ fuzz_defined payload /\ rc = 0
/\ SoA ps_so Km so (tr0 ++ evw 2 eb) s mo tr).
Proof.
intros Km so payload tr0 HKm.
eapply mspecE_conseq; [apply (REL_mspecE sel X (Klib Km so) (fun z : Z => z) (fuzz_one payload) (p_fuzz_one payload) tr0 p0);
apply REL_fuzz_one; apply Klib_fstable2; exact HKm| |].
- intros s mo tr (H1 & H2 & ->). split; [split; assumption|]. cbn [p_err p0]. rewrite evw_nil, app_nil_r. reflexivity.
- intros rc s mo tr (rc' & q' & Hp & -> & (H1 & H2) & ->). exists (p_err q').
split; [exact (canon_fuzz_of_prun _ _ _ Hp)|]. split; [unfold fuzz_defined; rewrite Hp; discriminate|].
split; [exact (p_fuzz_one_rc _ _ _ _ Hp)|]. split; [exact H1|]. split; [exact H2| reflexivity].
Qed.

Definition so_after (j : nat) : stdout_st :=
match j with O => stdout_init | S j' => mkStdout true (zeros_out j') false false end.
Lemma run_calls_E : forall Km payload eb n j tr0, Km_ok Km -> canon_fuzz payload = (0, eb) -> (j + n <= 500)%nat ->
mspecE sel X (SoA ps_so Km (so_after j) (tr0 ++ calls_events eb j)) (run_calls io_emit fuzz_one n payload 0)
(fun rc s mo tr => SoA ps_so Km (so_after (j + n)) (tr0 ++ calls_events eb (j + n)) s mo tr /\ rc = 0
/\ ((0 < n)%nat -> fuzz_defined payload)).
Proof.
intros Km payload eb n. induction n as [|n IH]; intros j tr0 HKm Hcf Hj; cbn [run_calls].
- apply mspecE_ret. intros s mo tr H. rewrite Nat.add_0_r. split; [exact H|]. split; [reflexivity| lia].
- eapply mspecE_bind; [apply fuzz_one_E; exact HKm|].
intros rc'. apply mspecE_exI. intros eb'. apply mspecE_pure_l; intros Hcf'. apply mspecE_pure_l; intros Hdef. apply mspecE_pure_l; intros ->.
assert (eb' = eb) by congruence. subst eb'.
eapply mspecE_seq with (R := SoA ps_so Km (so_after (S j)) (tr0 ++ calls_events eb (S j))).
+ unfold io_emit, s_emit. destruct j as [|j].
* eapply mspecE_conseq; [apply (stdout_emit_first ps_so set_so_ps sel X (fun _ _ => eq_refl) Km (tr0 ++ evw 2 eb))| |].
{ intros s mo tr H. cbn [so_after calls_events] in H. rewrite app_nil_r in H. exact H. }
intros a s mo tr H. rewrite calls_events_1, app_assoc. exact H.
* eapply mspecE_conseq; [apply (stdout_emit_next ps_so set_so_ps sel X (fun _ _ => eq_refl) Km (zeros_out j) ((tr0 ++ calls_events eb (S j)) ++ evw 2 eb));
rewrite zlength_zeros_out; unfold STDOUT_BUFSIZ; lia| |].
{ intros s mo tr H. exact H. }
intros a s mo tr H. cbv beta in H. rewrite zeros_out_app in H. rewrite calls_events_S, app_assoc. exact H.
+ intros _. replace (j + S n)%nat with (S j + n)%nat by lia.
eapply mspecE_post; [apply IH; [exact HKm| exact Hcf| lia]|].
intros rc s mo tr (H1 & H2 & _). split; [exact H1|]. split; [exact H2|]. intros _. exact Hdef.
Qed.

Lemma calls_pos : forall cfg, (1 <= Z.to_nat (1 + Z.land cfg 3) <= 4)%nat.
Proof.
intros cfg. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
pose proof (Z.mod_pos_bound cfg (2^2) ltac:(lia)) as H. change (2^2) with 4 in *. lia.
Qed.

Theorem target_run_E : forall Km cfg payload tr0, Km_ok Km -> zlength payload < 2^61 ->
mspecE sel X (SoA ps_so Km stdout_init tr0) (X1r6.run cfg payload)
(fun rc s mo tr => exists eb, canon_fuzz payload = (0, eb) /\ fuzz_defined payload /\ rc = 0 /\
SoA ps_so Km (so_after (Z.to_nat (1 + Z.land cfg 3))) (tr0 ++ calls_events eb (Z.to_nat (1 + Z.land cfg 3))) s mo tr).
Proof.
intros Km cfg payload tr0 HKm Hd. unfold X1r6.run, target_run. cbv zeta.
pose proof (SoA_fstable Km stdout_init tr0 HKm) as HK0.
eapply mspecE_bind with (Q1 := fun a s mo tr => SoA ps_so Km stdout_init tr0 s mo tr /\ a <> None).
- destruct (zlength payload =? 0).
+ apply mspecE_ret. intros s mo tr H. split; [exact H| discriminate].
+ eapply mspecE_bind; [apply raw_malloc_E; [exact HK0| apply size_ok; lia]|].
intros r. apply mspecE_pure. intros Hr. destruct r as [p|]; [|contradiction Hr; reflexivity].
apply mspecE_ret. intros s mo tr H. split; [exact H| discriminate].
- intros [owned|]; [|apply mspecE_pure; intros []; reflexivity].
apply mspecE_pure. intros _.
destruct (calls_pos cfg) as [Hc1 Hc2]. destruct (Z.to_nat (1 + Z.land cfg 3)) as [|n] eqn:En; [lia|].

eapply mspecE_bind with (Q1 := fun rc s mo tr => exists eb', canon_fuzz payload = (0, eb') /\ fuzz_defined payload /\ rc = 0 /\
SoA ps_so Km (so_after (S n)) (tr0 ++ calls_events eb' (S n)) s mo tr).
+ cbn [run_calls].
eapply mspecE_bind; [apply fuzz_one_E; exact HKm|].
intros rc'. apply mspecE_exI. intros eb'. apply mspecE_pure_l; intros Hcf'. apply mspecE_pure_l; intros Hdef. apply mspecE_pure_l; intros ->.
eapply mspecE_seq with (R := SoA ps_so Km (so_after 1) (tr0 ++ calls_events eb' 1)).
{ unfold io_emit, s_emit.
eapply mspecE_conseq; [apply (stdout_emit_first ps_so set_so_ps sel X (fun _ _ => eq_refl) Km (tr0 ++ evw 2 eb'))| |].
{ intros s mo tr H. exact H. }
intros a s mo tr H. rewrite calls_events_1, app_assoc. exact H. }
intros _. eapply mspecE_post; [apply (run_calls_E Km payload eb' n 1 tr0 HKm Hcf'); lia|].
intros rc s mo tr (H1 & H2 & _). exists eb'. splits; auto.
+ intros rc. apply mspecE_exI. intros eb'. apply mspecE_pure_l; intros Hcf'. apply mspecE_pure_l; intros Hdef. apply mspecE_pure_l; intros ->.
eapply mspecE_seq with (R := SoA ps_so Km (so_after (S n)) (tr0 ++ calls_events eb' (S n))).
* destruct owned as [q|]; [apply raw_free_E; apply SoA_fstable; exact HKm| apply mspecE_ret; auto].
* intros u. apply mspecE_ret. intros s mo tr H. exists eb'. splits; auto.
Qed.

End TargetE.
