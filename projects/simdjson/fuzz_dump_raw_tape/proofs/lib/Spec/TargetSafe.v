(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Monad MSafe MSafeN Stdio SjModel DrtModel Target.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store cho Target.ops lib_free_opt].

Lemma sj_sizes_small : forall len, 0 <= len <= 2^32 ->
  0 <= SJ_SBUF len < 2^62 /\ 0 <= SJ_TAPE len < 2^62 /\ 0 <= SJ_IDX len < 2^62 /\ 0 <= SJ_COPY len < 2^62.
Proof.
  intros len H. unfold SJ_SBUF, SJ_TAPE, SJ_IDX, SJ_COPY, sj_cap.
  pose proof (roundup64_ge (5 * (Z.max len 32 / 3) + 64)). pose proof (roundup64_lt (5 * (Z.max len 32 / 3) + 64)).
  pose proof (roundup64_ge (Z.max len 32 + 3)). pose proof (roundup64_lt (Z.max len 32 + 3)).
  pose proof (roundup64_ge (Z.max len 32)). pose proof (roundup64_lt (Z.max len 32)).
  assert (0 <= Z.max len 32 / 3 <= 2^32) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  change (2^32) with 4294967296 in *. change (2^62) with 4611686018427387904. lia.
Qed.

Section TargetSafe.
Context {St ptr : Type}.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.
Variable own : list ptr -> assn St.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspecN (own X) (raw_malloc n)
         (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).

Hypothesis HdmS : forall X n, 0 <= n < 2^62 ->
  mspecN (own X) (raw_malloc n) (fun r s mo => exists p, r = Some p /\ own (p :: X) s mo).
Hypothesis Hdf : forall X p, mspecN (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hout : forall X, mspecN (own X) (stdout_vprintf get_so set_so pieces_emit_0) (fun _ => own X).

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.

Lemma mspecN_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecN P (ret ops a) Q.
Proof. intros H. cbn. apply mspecN_ret. exact H. Qed.

Lemma mspecN_bind_ops {A B} (m : Monad.M St A) (f : A -> Monad.M St B) P Q1 Q :
  mspecN P m Q1 -> (forall a, mspecN (Q1 a) (f a) Q) -> mspecN P (bind ops m f) Q.
Proof. intros H1 H2. cbn. eapply mspecN_bind; eauto. Qed.

Lemma zlength_nonneg {A} (l : list A) : 0 <= zlength l.
Proof. unfold zlength. lia. Qed.

Lemma mspecN_chok_ops {B} (k : Z -> Monad.M St B) P Q :
  (forall z, mspecN P (k z) Q) -> mspecN P (bind ops (cho ops) k) Q.
Proof. intros H. cbn. apply mspecN_chok. exact H. Qed.

Lemma newnt_mspecN : forall X n, 0 <= n < 2^62 ->
  mspecN (own X) (newnt ops n) (fun p s mo => own (p :: X) s mo).
Proof.
  intros X n Hn. unfold newnt.
  apply (mspecN_bind_ops _ _ _ (fun r s mo => exists p, r = Some p /\ own (p :: X) s mo)).
  { red_ops. apply HdmS. exact Hn. }
  intros [p|].
  - apply mspecN_ret_ops. intros s mo (q & E & H). inversion E; subst q. exact H.
  - red_ops. eapply mspecN_pre; [apply mspecN_munr|]. intros s mo (q & E & _). discriminate E.
Qed.

Lemma del_mspecN : forall X Y p, Permutation Y (p :: X) -> mspecN (own Y) (del ops p) (fun _ => own X).
Proof.
  intros X Y p HP. unfold del. red_ops. eapply mspecN_pre; [apply Hdf|].
  intros s mo H. exact (Hperm _ _ s mo HP H).
Qed.

Lemma drt_free_nulls_N : forall X, mspecN (own X) (drt_free_nulls ops) (fun _ => own X).
Proof.
  intros X. unfold drt_free_nulls.
  repeat (apply (mspecN_bind_ops _ _ _ (fun _ => own X)); [red_ops; apply mspecN_ret; auto| intros _]).
  red_ops. apply mspecN_ret. auto.
Qed.

Lemma drt_print_N : forall X, mspecN (own X) (drt_print ops) (fun _ => own X).
Proof.
  intros X. unfold drt_print. apply mspecN_chok_ops. intros ok.
  destruct (ok =? 0); [apply mspecN_ret_ops; auto| apply drt_free_nulls_N].
Qed.

Lemma drt_copy_phase_N : forall len rc X, 0 <= len <= 2^32 -> rc_ok len rc ->
  mspecN (own X) (drt_copy_phase ops len rc) (fun _ => own X).
Proof.
  intros len rc X Hl Hrc. unfold drt_copy_phase.
  destruct (Z.leb_spec len SJ_PADMAX) as [Hle|Hgt]; [| apply mspecN_ret_ops; auto].
  pose proof (sj_sizes_small len Hl) as (_ & _ & _ & HC).
  apply (mspecN_bind_ops _ _ _ (fun cp s mo => own (cp :: X) s mo)); [apply newnt_mspecN; exact HC|]. intros cp.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (cp :: X) s mo)).
  { destruct rc as [c|]; [| apply mspecN_ret_ops; auto]. cbn in Hrc.
    apply (mspecN_bind_ops _ _ _ (fun r s mo => own (r :: cp :: X) s mo)).
    + apply newnt_mspecN. change (2^62) with 4611686018427387904. unfold SJ_PADMAX in Hle. lia.
    + intros r. apply del_mspecN. apply Permutation_refl. }
  intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (cp :: X) s mo)); [apply drt_print_N|]. intros _.
  apply del_mspecN. apply Permutation_refl.
Qed.

Lemma fuzz_one_with_mspecN : forall d X rc, zlength d <= 2^32 -> rc_ok (zlength d) rc ->
  mspecN (own X) (fuzz_one_with ops d rc) (fun r s mo => own X s mo /\ r = 0).
Proof.
  intros d X rc Hd Hrc. unfold fuzz_one_with. pose proof (zlength_nonneg d) as H0.
  set (len := zlength d) in *.
  pose proof (sj_sizes_small len ltac:(lia)) as (HS & HT & HI & _).
  assert (HK : forall k, 0 <= k <= 8192 -> 0 <= k < 2^62) by (intros k Hk; change (2^62) with 4611686018427387904; lia).
  apply (mspecN_bind_ops _ _ _ (fun sb s mo => own (sb :: X) s mo)); [apply newnt_mspecN; exact HS|]. intros sb.
  apply (mspecN_bind_ops _ _ _ (fun tp s mo => own (tp :: sb :: X) s mo)); [apply newnt_mspecN; exact HT|]. intros tp.
  apply (mspecN_bind_ops _ _ _ (fun im s mo => own (im :: tp :: sb :: X) s mo)); [apply newnt_mspecN; apply HK; unfold SJ_IMPL; lia|]. intros im.
  apply (mspecN_bind_ops _ _ _ (fun ix s mo => own (ix :: im :: tp :: sb :: X) s mo)); [apply newnt_mspecN; exact HI|]. intros ix.
  apply (mspecN_bind_ops _ _ _ (fun oc s mo => own (oc :: ix :: im :: tp :: sb :: X) s mo)); [apply newnt_mspecN; apply HK; unfold SJ_OC; lia|]. intros oc.
  apply (mspecN_bind_ops _ _ _ (fun ia s mo => own (ia :: oc :: ix :: im :: tp :: sb :: X) s mo)); [apply newnt_mspecN; apply HK; unfold SJ_IA; lia|]. intros ia.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (ia :: oc :: ix :: im :: tp :: sb :: X) s mo)); [apply drt_copy_phase_N; [lia| exact Hrc]|]. intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (ia :: oc :: ix :: im :: tp :: X) s mo)).
  { apply del_mspecN. apply Permutation_sym. exact (Permutation_middle [ia; oc; ix; im; tp] X sb). } intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (ia :: oc :: ix :: im :: X) s mo)).
  { apply del_mspecN. apply Permutation_sym. exact (Permutation_middle [ia; oc; ix; im] X tp). } intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (oc :: ix :: im :: X) s mo)); [apply del_mspecN; apply Permutation_refl|]. intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (ix :: im :: X) s mo)); [apply del_mspecN; apply Permutation_refl|]. intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (im :: X) s mo)); [apply del_mspecN; apply Permutation_refl|]. intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own X s mo)); [apply del_mspecN; apply Permutation_refl|]. intros _.
  apply mspecN_ret_ops. intros s mo H. split; [exact H| reflexivity].
Qed.

Lemma fuzz_one_mspecN : forall d X, zlength d <= 2^32 ->
  mspecN (own X) (fuzz_one ops d) (fun r s mo => own X s mo /\ r = 0).
Proof. intros d X Hd. unfold fuzz_one. apply fuzz_one_with_mspecN; [exact Hd| apply sj_root_copy_ok]. Qed.

Lemma run_calls_mspecN : forall d X n rc, zlength d <= 2^32 -> rc = 0 ->
  mspecN (own X) (run_calls ops d n rc) (fun rc' s mo => own X s mo /\ rc' = 0).
Proof.
  intros d X n. induction n as [|n IH]; intros rc Hd Hrc; cbn [run_calls].
  - apply mspecN_ret_ops. intros s mo H. auto.
  - apply (mspecN_bind_ops _ _ _ (fun rc' s mo => own X s mo /\ rc' = 0)); [apply fuzz_one_mspecN; exact Hd|].
    intros rc'. apply mspecN_pure. intros ->.
    apply (mspecN_bind_ops _ _ _ (fun _ => own X)).
    + red_ops. change (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0. apply Hout.
    + intros _. apply IH; [exact Hd| reflexivity].
Qed.

Theorem target_run_mspecN : forall X cfg payload, zlength payload <= 2^32 ->
  mspecN (own X) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ => own X).
Proof.
  intros X cfg payload Hpl. unfold Target.target_run, DrtModel.target_run. fold ops.
  apply (mspecN_bind_ops _ _ _
           (fun a s mo => match a with
                          | None => own X s mo
                          | Some None => own X s mo
                          | Some (Some p) => own (p :: X) s mo
                          end)).
  - destruct (zlength payload =? 0).
    + apply mspecN_ret_ops. auto.
    + apply (mspecN_bind_ops _ _ _
               (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end)).
      * red_ops. eapply mspecN_post; [apply Hdm; apply zlength_nonneg|].
        intros [p|] s mo H; [exact (proj1 H)| exact H].
      * intros [p|]; apply mspecN_ret_ops; auto.
  - intros [[p|]|]; [| |apply mspecN_ret_ops; auto].
    + apply (mspecN_bind_ops _ _ _ (fun rc s mo => own (p :: X) s mo /\ rc = 0)); [apply run_calls_mspecN; [exact Hpl| reflexivity]|].
      intros rc. apply (mspecN_bind_ops _ _ _ (fun _ => own X)).
      * red_ops. eapply mspecN_pre; [apply Hdf|]. intros s mo H. exact (proj1 H).
      * intros _. apply mspecN_ret_ops. auto.
    + apply (mspecN_bind_ops _ _ _ (fun rc s mo => own X s mo /\ rc = 0)); [apply run_calls_mspecN; [exact Hpl| reflexivity]|].
      intros rc. apply (mspecN_bind_ops _ _ _ (fun _ => own X)).
      * red_ops. apply mspecN_ret. intros s mo H. exact (proj1 H).
      * intros _. apply mspecN_ret_ops. auto.
Qed.

End TargetSafe.
