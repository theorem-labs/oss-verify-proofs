(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad MSafe MSafeN Stdio SjModel PjModel ImpModel Target.
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

Definition oblk (b : option ptr) : list ptr := match b with Some p => [p] | None => [] end.

Lemma del_opt_N : forall X b, mspecN (own (oblk b ++ X)) (del_opt ops b) (fun _ => own X).
Proof.
  intros X [p|]; unfold del_opt; cbn [oblk app].
  - apply del_mspecN. apply Permutation_refl.
  - apply mspecN_ret_ops. intros s mo H. exact H.
Qed.

Lemma pj_chain_N : forall fuel len cap b X, 0 <= len <= SJ_PADMAX -> 0 <= cap ->
  mspecN (own (oblk b ++ X)) (pj_chain ops fuel len cap b) (fun b' s mo => own (oblk b' ++ X) s mo).
Proof.
  induction fuel as [|f IH]; intros len cap b X Hl Hc; cbn [pj_chain].
  - apply mspecN_ret_ops. intros s mo H. exact H.
  - apply mspecN_chok_ops. intros z. destruct (chain_ok len cap z) eqn:E.
    + apply chain_ok_spec in E. pose proof (PJ_CAPMAX_bound len Hl) as HB.
      apply (mspecN_bind_ops _ _ _ (fun p s mo => own (p :: oblk b ++ X) s mo)).
      { apply newnt_mspecN. change (2^62) with 4611686018427387904. lia. }
      intros p. apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (p :: X) s mo)).
      * destruct b as [b0|]; unfold del_opt; cbn [oblk app].
        -- apply del_mspecN. apply perm_swap.
        -- apply mspecN_ret_ops. intros s mo H. exact H.
      * intros _. apply (IH len z (Some p) X Hl). lia.
    + apply mspecN_ret_ops. intros s mo H. exact H.
Qed.

Lemma pj_free_nulls_N : forall X, mspecN (own X) (pj_free_nulls ops) (fun _ => own X).
Proof.
  intros X. unfold pj_free_nulls.
  repeat (apply (mspecN_bind_ops _ _ _ (fun _ => own X)); [red_ops; apply mspecN_ret; auto| intros _]).
  red_ops. apply mspecN_ret. auto.
Qed.

Lemma pj_print_N : forall len X, 0 <= len <= SJ_PADMAX ->
  mspecN (own X) (pj_print ops len) (fun _ => own X).
Proof.
  intros len X Hl. unfold pj_print. apply mspecN_chok_ops. intros ok.
  destruct (ok =? 0); [apply mspecN_ret_ops; auto|].
  apply (mspecN_bind_ops _ _ _ (fun b s mo => own (oblk b ++ X) s mo)).
  { apply (pj_chain_N PJ_FUEL len PJ_INLINE None X Hl). unfold PJ_INLINE. lia. }
  intros b. apply (mspecN_bind_ops _ _ _ (fun _ => own X)); [apply del_opt_N|].
  intros _. apply pj_free_nulls_N.
Qed.

Definition olist (o : option ptr) : list ptr := match o with Some p => [p] | None => [] end.

Lemma imp_static_N : forall X v,
  mspecN (own (olist v ++ X)) (imp_static ops v) (fun v' s mo => exists p, v' = Some p /\ own (p :: X) s mo).
Proof.
  intros X [p|]; unfold imp_static; cbn [olist app].
  - apply mspecN_ret_ops. intros s mo H. exists p. split; [reflexivity| exact H].
  - apply (mspecN_bind_ops _ _ _ (fun p s mo => own (p :: X) s mo)).
    + apply newnt_mspecN. unfold IMP_VEC. change (2^62) with 4611686018427387904. lia.
    + intros p. apply mspecN_ret_ops. intros s mo H. exists p. split; [reflexivity| exact H].
Qed.

Lemma imp_copy_N : forall len X, 0 <= len <= SJ_PADMAX ->
  mspecN (own X) (imp_copy ops len) (fun c s mo => own (olist c ++ X) s mo).
Proof.
  intros len X Hl. unfold imp_copy. apply mspecN_chok_ops. intros S. destruct (copy_ok len S) eqn:E.
  - apply copy_ok_spec in E. pose proof (PJ_CAPMAX_bound len Hl) as HB.
    apply (mspecN_bind_ops _ _ _ (fun b s mo => own (b :: X) s mo)).
    + apply newnt_mspecN. change (2^62) with 4611686018427387904. lia.
    + intros b. apply mspecN_ret_ops. intros s mo H. exact H.
  - apply mspecN_ret_ops. intros s mo H. exact H.
Qed.

Lemma imp_print_N : forall len X, 0 <= len <= SJ_PADMAX ->
  mspecN (own X) (imp_print ops len) (fun _ => own X).
Proof.
  intros len X Hl. unfold imp_print. apply mspecN_chok_ops. intros ok.
  destruct (ok =? 0); [apply mspecN_ret_ops; auto|].
  apply (mspecN_bind_ops _ _ _ (fun b s mo => own (oblk b ++ X) s mo)).
  { apply (pj_chain_N PJ_FUEL len PJ_INLINE None X Hl). unfold PJ_INLINE. lia. }
  intros b.
  apply (mspecN_bind_ops _ _ _ (fun sb s mo => own (oblk sb ++ (oblk b ++ X)) s mo)).
  { apply (pj_chain_N PJ_FUEL len IMP_SCAP0 None (oblk b ++ X) Hl). unfold IMP_SCAP0. lia. }
  intros sb.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (oblk sb ++ X) s mo)).
  { destruct b as [bp|]; unfold del_opt; cbn [oblk app].
    - apply del_mspecN. destruct sb as [sp'|]; cbn [oblk app]; [apply perm_swap| apply Permutation_refl].
    - apply mspecN_ret_ops. intros s mo H. exact H. }
  intros _.
  apply (mspecN_bind_ops _ _ _ (fun c s mo => own (olist c ++ (oblk sb ++ X)) s mo)); [apply imp_copy_N; exact Hl|]. intros c.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (olist c ++ X) s mo)).
  { destruct sb as [sp'|]; unfold del_opt; cbn [oblk app].
    - apply del_mspecN. destruct c as [cp'|]; cbn [olist app]; [apply perm_swap| apply Permutation_refl].
    - rewrite app_nil_r || idtac. apply mspecN_ret_ops. intros s mo H. exact H. }
  intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (olist c ++ X) s mo)); [apply pj_free_nulls_N|]. intros _.
  destruct c as [cp'|]; unfold del_opt; cbn [olist app].
  - apply del_mspecN. apply Permutation_refl.
  - apply mspecN_ret_ops. intros s mo H. exact H.
Qed.

Lemma imp_copy_phase_N : forall len rc X, 0 <= len <= 2^32 -> rc_ok len rc ->
  mspecN (own X) (imp_copy_phase ops len rc) (fun _ => own X).
Proof.
  intros len rc X Hl Hrc. unfold imp_copy_phase.
  destruct (Z.leb_spec len SJ_PADMAX) as [Hle|Hgt]; [| apply mspecN_ret_ops; auto].
  pose proof (sj_sizes_small len Hl) as (_ & _ & _ & HC).
  apply (mspecN_bind_ops _ _ _ (fun cp s mo => own (cp :: X) s mo)); [apply newnt_mspecN; exact HC|]. intros cp.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (cp :: X) s mo)).
  { destruct rc as [c|]; [| apply mspecN_ret_ops; auto]. cbn in Hrc.
    apply (mspecN_bind_ops _ _ _ (fun r s mo => own (r :: cp :: X) s mo)).
    + apply newnt_mspecN. change (2^62) with 4611686018427387904. unfold SJ_PADMAX in Hle. lia.
    + intros r. apply del_mspecN. apply Permutation_refl. }
  intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (cp :: X) s mo)); [apply imp_print_N; lia|]. intros _.
  apply del_mspecN. apply Permutation_refl.
Qed.

Lemma fuzz_one_with_mspecN : forall d X rc v, zlength d <= 2^32 -> rc_ok (zlength d) rc ->
  mspecN (own (olist v ++ X)) (fuzz_one_with ops d rc v)
         (fun r s mo => exists p, snd r = Some p /\ fst r = 0 /\ own (p :: X) s mo).
Proof.
  intros d X rc v Hd Hrc. unfold fuzz_one_with. pose proof (zlength_nonneg d) as H0.
  set (len := zlength d) in *.
  pose proof (sj_sizes_small len ltac:(lia)) as (HS & HT & HI & _).
  assert (HK : forall k, 0 <= k <= 8192 -> 0 <= k < 2^62) by (intros k Hk; change (2^62) with 4611686018427387904; lia).
  apply (mspecN_bind_ops _ _ _ (fun v' s mo => exists p, v' = Some p /\ own (p :: X) s mo)); [apply imp_static_N|]. intros v'.
  apply mspecN_exI. intros p. apply mspecN_pure_l. intros ->.
  set (Y := p :: X).
  apply (mspecN_bind_ops _ _ _ (fun sb s mo => own (sb :: Y) s mo)); [apply newnt_mspecN; exact HS|]. intros sb.
  apply (mspecN_bind_ops _ _ _ (fun tp s mo => own (tp :: sb :: Y) s mo)); [apply newnt_mspecN; exact HT|]. intros tp.
  apply (mspecN_bind_ops _ _ _ (fun im s mo => own (im :: tp :: sb :: Y) s mo)); [apply newnt_mspecN; apply HK; unfold SJ_IMPL; lia|]. intros im.
  apply (mspecN_bind_ops _ _ _ (fun ix s mo => own (ix :: im :: tp :: sb :: Y) s mo)); [apply newnt_mspecN; exact HI|]. intros ix.
  apply (mspecN_bind_ops _ _ _ (fun oc s mo => own (oc :: ix :: im :: tp :: sb :: Y) s mo)); [apply newnt_mspecN; apply HK; unfold SJ_OC; lia|]. intros oc.
  apply (mspecN_bind_ops _ _ _ (fun ia s mo => own (ia :: oc :: ix :: im :: tp :: sb :: Y) s mo)); [apply newnt_mspecN; apply HK; unfold SJ_IA; lia|]. intros ia.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (ia :: oc :: ix :: im :: tp :: sb :: Y) s mo)); [apply imp_copy_phase_N; [lia| exact Hrc]|]. intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (ia :: oc :: ix :: im :: tp :: Y) s mo)).
  { apply del_mspecN. apply Permutation_sym. exact (Permutation_middle [ia; oc; ix; im; tp] Y sb). } intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (ia :: oc :: ix :: im :: Y) s mo)).
  { apply del_mspecN. apply Permutation_sym. exact (Permutation_middle [ia; oc; ix; im] Y tp). } intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (oc :: ix :: im :: Y) s mo)); [apply del_mspecN; apply Permutation_refl|]. intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (ix :: im :: Y) s mo)); [apply del_mspecN; apply Permutation_refl|]. intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (im :: Y) s mo)); [apply del_mspecN; apply Permutation_refl|]. intros _.
  apply (mspecN_bind_ops _ _ _ (fun _ s mo => own Y s mo)); [apply del_mspecN; apply Permutation_refl|]. intros _.
  apply mspecN_ret_ops. intros s mo H. exists p. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity| exact H].
Qed.

Lemma fuzz_one_mspecN : forall d X v, zlength d <= 2^32 ->
  mspecN (own (olist v ++ X)) (fuzz_one ops d v) (fun r s mo => exists p, snd r = Some p /\ fst r = 0 /\ own (p :: X) s mo).
Proof. intros d X v Hd. unfold fuzz_one. apply fuzz_one_with_mspecN; [exact Hd| apply sj_root_copy_ok]. Qed.

Lemma run_calls_mspecN : forall d X n rc v, zlength d <= 2^32 -> rc = 0 ->
  mspecN (own (olist v ++ X)) (run_calls ops d n rc v)
         (fun r s mo => own (olist (snd r) ++ X) s mo /\ fst r = 0).
Proof.
  intros d X n. induction n as [|n IH]; intros rc v Hd Hrc; cbn [run_calls].
  - apply mspecN_ret_ops. intros s mo H. cbn [fst snd]. split; [exact H| exact Hrc].
  - apply (mspecN_bind_ops _ _ _ (fun r s mo => exists p, snd r = Some p /\ fst r = 0 /\ own (p :: X) s mo)); [apply fuzz_one_mspecN; exact Hd|].
    intros r. apply mspecN_exI. intros p. apply mspecN_pure_l. intros Hr. apply mspecN_pure_l. intros Hz.
    apply (mspecN_bind_ops _ _ _ (fun _ => own (p :: X))).
    + red_ops. rewrite Hz. change (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0. apply Hout.
    + intros _. rewrite Hr. apply (IH (fst r) (Some p)); [exact Hd| exact Hz].
Qed.

Theorem target_run_mspecN : forall X cfg payload, zlength payload <= 2^32 ->
  mspecN (own X) (Target.target_run raw_malloc raw_free get_so set_so cfg payload)
         (fun r s mo => own (olist (snd r) ++ X) s mo /\ fst r = 0).
Proof.
  intros X cfg payload Hpl. unfold Target.target_run, ImpModel.target_run. fold ops.
  apply (mspecN_bind_ops _ _ _
           (fun a s mo => match a with
                          | None => False
                          | Some None => own X s mo
                          | Some (Some p) => own (p :: X) s mo
                          end)).
  - destruct (zlength payload =? 0).
    + apply mspecN_ret_ops. auto.
    + apply (mspecN_bind_ops _ _ _ (fun r s mo => exists p, r = Some p /\ own (p :: X) s mo)).
      * red_ops. apply HdmS. split; [apply zlength_nonneg|]. change (2^62) with 4611686018427387904. lia.
      * intros [p|]; apply mspecN_ret_ops; [intros s mo (q & E & H); inversion E; subst; exact H| intros s mo (q & E & _); discriminate E].
  - intros [[p|]|]; [| | red_ops; eapply mspecN_pre; [apply mspecN_munr|]; intros s mo F; destruct F].
    + apply (mspecN_bind_ops _ _ _ (fun r s mo => own (olist (snd r) ++ (p :: X)) s mo /\ fst r = 0));
        [apply (run_calls_mspecN payload (p :: X) _ 0 None); [exact Hpl| reflexivity]|].
      intros r. apply mspecN_pure. intros Hz.
      apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (olist (snd r) ++ X) s mo)).
      * red_ops. eapply mspecN_pre; [apply Hdf|]. intros s mo H. eapply Hperm; [| exact H]. apply Permutation_sym. apply Permutation_middle.
      * intros _. apply mspecN_ret_ops. intros s mo H. cbn [fst snd]. rewrite Hz. cbn. split; [exact H| reflexivity].
    + apply (mspecN_bind_ops _ _ _ (fun r s mo => own (olist (snd r) ++ X) s mo /\ fst r = 0));
        [apply (run_calls_mspecN payload X _ 0 None); [exact Hpl| reflexivity]|].
      intros r. apply mspecN_pure. intros Hz.
      apply (mspecN_bind_ops _ _ _ (fun _ s mo => own (olist (snd r) ++ X) s mo)).
      * red_ops. apply mspecN_ret. intros s mo H. exact H.
      * intros _. apply mspecN_ret_ops. intros s mo H. cbn [fst snd]. rewrite Hz. cbn. split; [exact H| reflexivity].
Qed.

End TargetSafe.
