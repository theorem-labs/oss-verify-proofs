(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad Stdio Prog Canon.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Malloc.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import SjModel DrtModel Target TargetSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import ProgDetIface ProgDetLogic ProgDetNodes ProgDetMalloc ProgDetStdio.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store cho Target.ops lib_free_opt].

Section TargetE.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.

Let ops : target_ops (Monad.M PState) bptr := Target.ops raw_malloc raw_free ps_so set_so_ps.

Lemma mspecE_ret_ops {A} (a : A) (P : assnE PState) (Q : A -> assnE PState) :
  (forall s mo tr, P s mo tr -> Q a s mo tr) -> mspecE sel X P (ret ops a) Q.
Proof. intros H. cbn. apply mspecE_ret. exact H. Qed.

Lemma mspecE_bind_ops {A B} (m : Monad.M PState A) (f : A -> Monad.M PState B) P Q1 Q :
  mspecE sel X P m Q1 -> (forall a, mspecE sel X (Q1 a) (f a) Q) -> mspecE sel X P (bind ops m f) Q.
Proof. intros. cbn. eapply mspecE_bind; eauto. Qed.

Lemma mspecE_chok_ops {B} (k : Z -> Monad.M PState B) P Q :
  (forall z, mspecE sel X P (k z) Q) -> mspecE sel X P (bind ops (cho ops) k) Q.
Proof. intros H. cbn. apply mspecE_chok. exact H. Qed.

Lemma size_ok : forall n, n < 2^62 -> Malloc.size_overflows n = false.
Proof. intros n H. unfold Malloc.size_overflows. apply Z.leb_gt. lia. Qed.

Section Harness.
Variable K : assnE PState.
Hypothesis HK : fstable K.
Variable d : list Z.
Hypothesis Hd : zlength d <= 2^32.

Lemma malloc_ops_E : forall n, n < 2^62 ->
  mspecE sel X K (lib_malloc ops n) (fun r s mo tr => K s mo tr /\ r <> None).
Proof. intros n Hn. red_ops. apply raw_malloc_E; [exact HK| apply size_ok; exact Hn]. Qed.

Lemma free_ops_E : forall p, mspecE sel X K (lib_free ops p) (fun _ => K).
Proof. intros [p|]; red_ops; [apply raw_free_E; exact HK| apply mspecE_ret; auto]. Qed.

Lemma newnt_E : forall n, n < 2^62 -> mspecE sel X K (newnt ops n) (fun _ => K).
Proof.
  intros n Hn. unfold newnt.
  eapply mspecE_bind_ops; [apply malloc_ops_E; exact Hn|].
  intros r. apply mspecE_pure. intros Hr. destruct r as [p|]; [| contradiction Hr; reflexivity].
  apply mspecE_ret_ops. auto.
Qed.

Lemma del_E : forall p, mspecE sel X K (del ops p) (fun _ => K).
Proof. intros p. unfold del. apply free_ops_E. Qed.

Lemma drt_free_nulls_E : mspecE sel X K (drt_free_nulls ops) (fun _ => K).
Proof.
  unfold drt_free_nulls.
  repeat (apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply free_ops_E| intros _]).
  apply free_ops_E.
Qed.

Lemma drt_print_E : mspecE sel X K (drt_print ops) (fun _ => K).
Proof.
  unfold drt_print. apply mspecE_chok_ops. intros ok.
  destruct (ok =? 0); [apply mspecE_ret_ops; auto| apply drt_free_nulls_E].
Qed.

Lemma drt_copy_phase_E : forall len rc, 0 <= len <= 2^32 -> rc_ok len rc ->
  mspecE sel X K (drt_copy_phase ops len rc) (fun _ => K).
Proof.
  intros len rc Hl Hrc. unfold drt_copy_phase.
  destruct (Z.leb_spec len SJ_PADMAX) as [Hle|Hgt]; [| apply mspecE_ret_ops; auto].
  pose proof (sj_sizes_small len Hl) as (_ & _ & _ & HC).
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply newnt_E; lia|]. intros cp.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)).
  { destruct rc as [c|]; [| apply mspecE_ret_ops; auto]. cbn in Hrc.
    apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply newnt_E; change (2^62) with 4611686018427387904; unfold SJ_PADMAX in Hle; lia|].
    intros r. apply del_E. }
  intros _.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply drt_print_E|]. intros _.
  apply del_E.
Qed.

Lemma fuzz_one_with_E : forall rc, rc_ok (zlength d) rc ->
  mspecE sel X K (fuzz_one_with ops d rc) (fun r s mo tr => K s mo tr /\ r = 0).
Proof.
  intros rc Hrc. unfold fuzz_one_with.
  assert (Hd0 : 0 <= zlength d) by (unfold zlength; lia).
  set (len := zlength d) in *.
  pose proof (sj_sizes_small len ltac:(lia)) as (HS & HT & HI & _).
  assert (HK62 : forall k, k <= 8192 -> k < 2^62) by (intros k Hk; change (2^62) with 4611686018427387904; lia).
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply newnt_E; lia|]. intros sb.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply newnt_E; lia|]. intros tp.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply newnt_E; apply HK62; unfold SJ_IMPL; lia|]. intros im.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply newnt_E; lia|]. intros ix.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply newnt_E; apply HK62; unfold SJ_OC; lia|]. intros oc.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply newnt_E; apply HK62; unfold SJ_IA; lia|]. intros ia.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply drt_copy_phase_E; [lia| exact Hrc]|]. intros _.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply del_E|]. intros _.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply del_E|]. intros _.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply del_E|]. intros _.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply del_E|]. intros _.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply del_E|]. intros _.
  apply (mspecE_bind_ops _ _ _ (fun _ => K)); [apply del_E|]. intros _.
  apply mspecE_ret_ops. auto.
Qed.

Lemma fuzz_one_E : mspecE sel X K (fuzz_one ops d) (fun rc s mo tr => K s mo tr /\ rc = 0).
Proof. unfold fuzz_one. apply fuzz_one_with_E. apply sj_root_copy_ok. Qed.

End Harness.

Definition so_after (j : nat) : stdout_st :=
  match j with O => stdout_init | S j' => mkStdout true (zeros_out j') false false end.
Definition out_after (j : nat) : list Z := match j with O => [] | S _ => [48; 10] end.

Definition Km_ok (Km : Model -> Prop) : Prop := forall mo mo', Km mo -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> Km mo'.

Lemma SoA_fstable : forall Km so tr0, Km_ok Km -> fstable (SoA ps_so Km so tr0).
Proof.
  intros Km so tr0 HKm s mo tr s' mo' (H1 & H2 & H3) Hso Hfd Hfs. split; [eapply HKm; eauto|]. split; [congruence| exact H3].
Qed.

Lemma zlength_zeros_out : forall j, zlength (zeros_out j) = 2 * Z.of_nat j.
Proof.
  induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S, zlen_app, IH. unfold zlength. cbn [length]. lia.
Qed.

Lemma zeros_out_app : forall j, zeros_out j ++ [48; 10] = zeros_out (S j).
Proof.
  induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S. rewrite <- app_assoc, IH. reflexivity.
Qed.

Lemma Zdecimal_0 : Zdecimal 0 ++ [10] = [48; 10].
Proof. reflexivity. Qed.

Lemma run_calls_E : forall Km d n j tr0, Km_ok Km -> zlength d <= 2^32 -> (j + n <= 500)%nat ->
  mspecE sel X (SoA ps_so Km (so_after j) (tr0 ++ evw 1 (out_after j))) (DrtModel.run_calls ops d n 0)
    (fun rc => fun s mo tr => SoA ps_so Km (so_after (j + n)) (tr0 ++ evw 1 (out_after (j + n))) s mo tr /\ rc = 0).
Proof.
  intros Km d n. induction n as [|n IH]; intros j tr0 HKm Hd Hj; cbn [DrtModel.run_calls].
  - apply mspecE_ret_ops. intros s mo tr H. rewrite Nat.add_0_r. auto.
  - apply (mspecE_bind_ops _ _ _ (fun rc' s mo tr => SoA ps_so Km (so_after j) (tr0 ++ evw 1 (out_after j)) s mo tr /\ rc' = 0)).
    { apply fuzz_one_E; [apply SoA_fstable; exact HKm| exact Hd]. }
    intros rc'. apply mspecE_pure. intros ->. red_ops. rewrite Zdecimal_0. cbn [pieces_emit_of].
    eapply mspecE_seq with (R := SoA ps_so Km (so_after (S j)) (tr0 ++ evw 1 (out_after (S j)))).
    + destruct j as [|j].
      * eapply mspecE_conseq; [apply (stdout_emit_first ps_so set_so_ps sel X (fun _ _ => eq_refl) Km tr0)| |].
        { intros s mo tr H. cbn [so_after out_after evw map] in H. rewrite app_nil_r in H. exact H. }
        intros a s mo tr H. exact H.
      * eapply mspecE_conseq; [apply (stdout_emit_next ps_so set_so_ps sel X (fun _ _ => eq_refl) Km (zeros_out j) (tr0 ++ evw 1 [48; 10]))| |].
        { rewrite zlength_zeros_out. unfold STDOUT_BUFSIZ. lia. }
        { intros s mo tr H. exact H. }
        intros a s mo tr H. cbv beta in H. rewrite zeros_out_app in H. exact H.
    + intros _. replace (j + S n)%nat with (S j + n)%nat by lia. apply IH; auto; lia.
Qed.

Lemma calls_pos : forall cfg, (1 <= Z.to_nat (Z.land cfg 3 + 1) <= 4)%nat.
Proof.
  intros cfg. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound cfg (2^2) ltac:(lia)) as H. change (2^2) with 4 in *. lia.
Qed.

Theorem target_run_E : forall Km cfg payload tr0, Km_ok Km -> zlength payload <= 2^32 ->
  mspecE sel X (SoA ps_so Km stdout_init tr0) (Prog.run cfg payload)
    (fun rc s mo tr => SoA ps_so Km (so_after (Z.to_nat (Z.land cfg 3 + 1))) (tr0 ++ evw 1 [48; 10]) s mo tr /\ rc = 0).
Proof.
  intros Km cfg payload tr0 HKm Hd. unfold Prog.run, Target.target_run, DrtModel.target_run.
  pose proof (SoA_fstable Km stdout_init tr0 HKm) as HK0.
  apply (mspecE_bind_ops _ _ _ (fun a s mo tr => SoA ps_so Km stdout_init tr0 s mo tr /\ a <> None)).
  - destruct (zlength payload =? 0).
    + apply mspecE_ret_ops. intros s mo tr H. split; [exact H| discriminate].
    + eapply mspecE_bind_ops; [apply malloc_ops_E; [exact HK0| change (2^32) with 4294967296 in Hd; change (2^62) with 4611686018427387904; lia]|].
      intros r. apply mspecE_pure. intros Hr. destruct r as [p|]; [|contradiction Hr; reflexivity].
      apply mspecE_ret_ops. intros s mo tr H. split; [exact H| discriminate].
  - intros [owned|]; [|apply mspecE_pure; intros []; reflexivity].
    apply mspecE_pure. intros _.
    destruct (calls_pos cfg) as [Hc1 Hc2]. destruct (Z.to_nat (Z.land cfg 3 + 1)) as [|n] eqn:En; [lia|].
    apply (mspecE_bind_ops _ _ _ (fun rc s mo tr => SoA ps_so Km (so_after (S n)) (tr0 ++ evw 1 [48; 10]) s mo tr /\ rc = 0)).
    + eapply mspecE_conseq; [apply (run_calls_E Km payload (S n) 0 tr0 HKm Hd); lia| |].
      * intros s mo tr H. cbn [so_after out_after evw map]. rewrite app_nil_r. exact H.
      * intros rc s mo tr [H ->]. split; [exact H| reflexivity].
    + intros rc. apply mspecE_pure. intros ->.
      apply (mspecE_bind_ops _ _ _ (fun _ => SoA ps_so Km (so_after (S n)) (tr0 ++ evw 1 [48; 10]))).
      * apply free_ops_E. apply SoA_fstable. exact HKm.
      * intros u. apply mspecE_ret_ops. intros s mo tr H. auto.
Qed.

End TargetE.
