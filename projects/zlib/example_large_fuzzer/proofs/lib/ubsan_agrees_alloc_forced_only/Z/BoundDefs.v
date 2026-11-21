(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees CompressModel DeflateOverlay RefDeflSafeZ RefDeflSafeFBT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition symlen (s : deflate_state) (j : Z) : Z := if sym_isdist s j then sym_lc s (3 * j) + 3 else 1.
Definition cov (s : deflate_state) : Z := zsum (symlen s) 0 (Z.to_nat (nsym s)).
Definition near3 (s : deflate_state) (j : Z) : Prop :=
  sym_isdist s j = true -> sym_lc s (3 * j) = 0 -> sym_dist s (3 * j) <= 4096.

Record COV (s : deflate_state) : Prop := {
  cv_cov : cov s = ds_strstart s - ds_block_start s - ds_match_available s;
  cv_near : forall j, 0 <= j < nsym s -> near3 s j;
  cv_nb : ds_block_start s < 0 -> ds_w_size s - MIN_LOOKAHEAD <= ds_strstart s;
  cv_pm : ds_match_length s = 3 -> wrap32 (ds_strstart s - ds_match_start s) <= 4097;
  cv_ma : 3 <= ds_match_length s -> ds_match_available s = 1 }.

(* [comment removed for export] *)
Lemma symlen_same : forall s s' j,
  sym_dist s' (3 * j) = sym_dist s (3 * j) -> sym_lc s' (3 * j) = sym_lc s (3 * j) -> symlen s' j = symlen s j.
Proof. intros s s' j Ed El. unfold symlen, sym_isdist. rewrite Ed, El. reflexivity. Qed.

Lemma near3_same : forall s s' j,
  sym_dist s' (3 * j) = sym_dist s (3 * j) -> sym_lc s' (3 * j) = sym_lc s (3 * j) -> near3 s j -> near3 s' j.
Proof. intros s s' j Ed El H. unfold near3, sym_isdist in *. rewrite Ed, El. exact H. Qed.

Lemma cov_ext : forall s s', nsym s' = nsym s ->
  (forall j, 0 <= j < nsym s -> sym_dist s' (3 * j) = sym_dist s (3 * j) /\ sym_lc s' (3 * j) = sym_lc s (3 * j)) ->
  cov s' = cov s.
Proof.
  intros s s' EN H. unfold cov. rewrite EN. apply zsum_ext. intros j Hj.
  destruct (H j ltac:(lia)) as [Ed El]. apply symlen_same; assumption.
Qed.

(* [comment removed for export] *)
Lemma sym_view_same : forall s s', ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  forall k, sym_dist s' k = sym_dist s k /\ sym_lc s' k = sym_lc s k.
Proof.
  intros s s' EP EL k. unfold sym_dist, sym_d0, sym_d1, sym_lc, sym_buf_get. rewrite EP, EL. split; reflexivity.
Qed.

Lemma cov_same : forall s s', ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  ds_sym_next s' = ds_sym_next s -> cov s' = cov s.
Proof.
  intros s s' EP EL EN. apply cov_ext; [unfold nsym; rewrite EN; reflexivity|].
  intros j _. apply sym_view_same; assumption.
Qed.

Lemma near_same : forall s s', ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  ds_sym_next s' = ds_sym_next s ->
  (forall j, 0 <= j < nsym s -> near3 s j) -> forall j, 0 <= j < nsym s' -> near3 s' j.
Proof.
  intros s s' EP EL EN H j Hj. assert (EN' : nsym s' = nsym s) by (unfold nsym; rewrite EN; reflexivity).
  destruct (sym_view_same s s' EP EL (3 * j)) as [Ed Ec]. apply (near3_same s s' j Ed Ec). apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma cov_snoc : forall s r, 0 <= nsym s -> nsym r = nsym s + 1 ->
  (forall j, 0 <= j < nsym s -> sym_dist r (3 * j) = sym_dist s (3 * j) /\ sym_lc r (3 * j) = sym_lc s (3 * j)) ->
  cov r = cov s + symlen r (nsym s).
Proof.
  intros s r N0 EN OLD. unfold cov. rewrite EN. replace (Z.to_nat (nsym s + 1)) with (S (Z.to_nat (nsym s))) by lia.
  rewrite zsum_snoc. rewrite Z.add_0_l, Z2Nat.id by lia. f_equal.
  apply zsum_ext. intros j Hj. destruct (OLD j ltac:(lia)) as [Ed El]. apply symlen_same; assumption.
Qed.

Lemma near_snoc : forall s r, 0 <= nsym s -> nsym r = nsym s + 1 ->
  (forall j, 0 <= j < nsym s -> sym_dist r (3 * j) = sym_dist s (3 * j) /\ sym_lc r (3 * j) = sym_lc s (3 * j)) ->
  (forall j, 0 <= j < nsym s -> near3 s j) -> near3 r (nsym s) ->
  forall j, 0 <= j < nsym r -> near3 r j.
Proof.
  intros s r N0 EN OLD H NEW j Hj. destruct (Z.eq_dec j (nsym s)) as [->|Nj]; [exact NEW|].
  destruct (OLD j ltac:(lia)) as [Ed El]. apply (near3_same s r j Ed El). apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma symlen_lit : forall r j, sym_dist r (3 * j) = 0 -> symlen r j = 1.
Proof. intros r j E. unfold symlen, sym_isdist. rewrite E. reflexivity. Qed.
Lemma symlen_match : forall r j, sym_dist r (3 * j) <> 0 -> symlen r j = sym_lc r (3 * j) + 3.
Proof. intros r j E. unfold symlen, sym_isdist. destruct (Z.eqb_spec (sym_dist r (3 * j)) 0); [contradiction | reflexivity]. Qed.
Lemma near3_lit : forall r j, sym_dist r (3 * j) = 0 -> near3 r j.
Proof. intros r j E. unfold near3, sym_isdist. rewrite E. cbn. intros H; discriminate H. Qed.
