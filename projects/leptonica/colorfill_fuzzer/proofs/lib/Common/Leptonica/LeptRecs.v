(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec CatExec StepTac StoreOk MemSplit RefMemcpyLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptStructs.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.

#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition fld : Type := (nat * Z)%type.

Fixpoint flds_bytes (fs : list fld) : list byte :=
  match fs with [] => [] | (k, v) :: t => Z_to_le_bytes k v ++ flds_bytes t end.
Fixpoint flds_len (fs : list fld) : nat :=
  match fs with [] => 0%nat | (k, _) :: t => (k + flds_len t)%nat end.
Fixpoint flds_wf (fs : list fld) : Prop :=
  match fs with [] => True | (k, v) :: t => (0 <= v < 2 ^ (8 * Z.of_nat k) /\ (k <= 8)%nat) /\ flds_wf t end.
Fixpoint fld_off (fs : list fld) (i : nat) : nat :=
  match fs, i with
  | (k, _) :: t, S i' => (k + fld_off t i')%nat
  | _, _ => 0%nat
  end.
Fixpoint fld_get (fs : list fld) (i : nat) : fld :=
  match fs, i with
  | f :: _, O => f
  | _ :: t, S i' => fld_get t i'
  | [], _ => (0%nat, 0%Z)
  end.
Fixpoint fld_set (fs : list fld) (i : nat) (z : Z) : list fld :=
  match fs, i with
  | (k, _) :: t, O => (k, z) :: t
  | f :: t, S i' => f :: fld_set t i' z
  | [], _ => []
  end.
(* [comment removed for export] *)
Fixpoint zflds (ks : list nat) : list fld :=
  match ks with [] => [] | k :: t => (k, 0) :: zflds t end.

Lemma flds_bytes_len : forall fs, length (flds_bytes fs) = flds_len fs.
Proof. induction fs as [|[k v] t IH]; [reflexivity|]. cbn [flds_bytes flds_len]. rewrite length_app, length_Z_to_le_bytes, IH. reflexivity. Qed.

Definition RECat (m : word -> option byte) (p : Z) (fs : list fld) : Prop :=
  0 <= p /\ p + Z.of_nat (flds_len fs) < 2 ^ 64 /\ flds_wf fs /\ bytes_at m p (flds_bytes fs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fld_off_get_len : forall fs i, (i < length fs)%nat ->
  (fld_off fs i + fst (fld_get fs i) <= flds_len fs)%nat.
Proof.
  induction fs as [|[k v] t IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i']; cbn [fld_off fld_get fst flds_len]; [lia|].
  cbn in Hi. specialize (IH i' ltac:(lia)). lia.
Qed.

Lemma flds_bytes_split : forall fs i, (i < length fs)%nat ->
  firstn (fst (fld_get fs i)) (skipn (fld_off fs i) (flds_bytes fs)) = Z_to_le_bytes (fst (fld_get fs i)) (snd (fld_get fs i)).
Proof.
  induction fs as [|[k v] t IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i']; cbn [fld_off fld_get fst snd flds_bytes].
  - rewrite skipn_O. rewrite firstn_app, length_Z_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite <- (length_Z_to_le_bytes k v) at 1. rewrite firstn_all. reflexivity.
  - cbn in Hi. rewrite skipn_app, length_Z_to_le_bytes.
    replace (k + fld_off t i' - k)%nat with (fld_off t i') by lia.
    rewrite (skipn_all2 (Z_to_le_bytes k v)) by (rewrite length_Z_to_le_bytes; lia). cbn [app].
    exact (IH i' ltac:(lia)).
Qed.

Lemma fld_set_bytes : forall fs i z, (i < length fs)%nat ->
  flds_bytes (fld_set fs i z) =
  firstn (fld_off fs i) (flds_bytes fs) ++ Z_to_le_bytes (fst (fld_get fs i)) z ++
  skipn (fld_off fs i + fst (fld_get fs i)) (flds_bytes fs).
Proof.
  induction fs as [|[k v] t IH]; intros i z Hi; [cbn in Hi; lia|].
  destruct i as [|i']; cbn [fld_set fld_off fld_get fst flds_bytes].
  - rewrite firstn_O. cbn [app]. rewrite skipn_app, length_Z_to_le_bytes, Nat.sub_diag, skipn_O.
    rewrite skipn_all2 by (rewrite length_Z_to_le_bytes; lia). reflexivity.
  - cbn in Hi. rewrite (IH i' z ltac:(lia)).
    rewrite firstn_app, length_Z_to_le_bytes. replace (k + fld_off t i' - k)%nat with (fld_off t i') by lia.
    rewrite (firstn_all2 (Z_to_le_bytes k v)) by (rewrite length_Z_to_le_bytes; lia).
    rewrite skipn_app, length_Z_to_le_bytes.
    replace (k + fld_off t i' + fst (fld_get t i') - k)%nat with (fld_off t i' + fst (fld_get t i'))%nat by lia.
    rewrite (skipn_all2 (Z_to_le_bytes k v)) by (rewrite length_Z_to_le_bytes; lia).
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma fld_set_len : forall fs i z, flds_len (fld_set fs i z) = flds_len fs.
Proof. induction fs as [|[k v] t IH]; intros i z; [destruct i; reflexivity|]. destruct i; cbn [fld_set flds_len]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma fld_set_length : forall fs i z, length (fld_set fs i z) = length fs.
Proof. induction fs as [|[k v] t IH]; intros i z; [destruct i; reflexivity|]. destruct i; cbn [fld_set length]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma fld_set_wf : forall fs i z, flds_wf fs -> (i < length fs)%nat -> 0 <= z < 2 ^ (8 * Z.of_nat (fst (fld_get fs i))) ->
  flds_wf (fld_set fs i z).
Proof.
  induction fs as [|[k v] t IH]; intros i z WF Hi Hz; [cbn in Hi; lia|].
  destruct i as [|i']; cbn [fld_set flds_wf fld_get fst length] in *.
  - destruct WF as [[_ Hk] WFt]. split; [split; [exact Hz | exact Hk] | exact WFt].
  - destruct WF as [H1 WFt]. split; [exact H1|]. apply IH; [exact WFt | lia | exact Hz].
Qed.

Lemma fld_get_wf : forall fs i, flds_wf fs -> (i < length fs)%nat ->
  0 <= snd (fld_get fs i) < 2 ^ (8 * Z.of_nat (fst (fld_get fs i))) /\ (fst (fld_get fs i) <= 8)%nat.
Proof.
  induction fs as [|[k v] t IH]; intros i WF Hi; [cbn in Hi; lia|].
  destruct i as [|i']; cbn [flds_wf fld_get fst snd length] in *; [exact (proj1 WF)|].
  apply IH; [exact (proj2 WF) | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RECat_frame : forall m m' p fs, RECat m p fs ->
  (forall x : word, p <= u x < p + Z.of_nat (flds_len fs) -> m' x = m x) -> RECat m' p fs.
Proof.
  intros m m' p fs (Hp & Hn & WF & HB) HF. split; [lia|]. split; [lia|]. split; [exact WF|].
  apply (bytes_at_frame m); [exact HB | rewrite flds_bytes_len; exact HF | lia | rewrite flds_bytes_len; lia].
Qed.

Lemma RECat_out : forall m p fs (wa : word) ws, RECat m p fs -> u wa + Z.of_nat (length ws) <= 2 ^ 64 ->
  (p + Z.of_nat (flds_len fs) <= u wa \/ u wa + Z.of_nat (length ws) <= p) -> RECat (wbytes m wa ws) p fs.
Proof.
  intros m p fs wa ws HP Hw Hd. apply (RECat_frame m); [exact HP|]. intros x Hx. apply wbytes_outside; lia.
Qed.

Lemma RECat_defined : forall m p fs (x : word), RECat m p fs -> p <= u x < p + Z.of_nat (flds_len fs) -> m x <> None.
Proof.
  intros m p fs x (Hp & Hn & _ & HB) Hx.
  pose proof (HB (u x - p) ltac:(rewrite flds_bytes_len; lia)) as E.
  replace (Z_to_bv 64 (p + (u x - p))) with x in E by (apply bv_eq; rewrite u_Z2bv by lia; lia). rewrite E. discriminate.
Qed.

Lemma RECat_range : forall m p fs, RECat m p fs -> 0 <= p /\ p + Z.of_nat (flds_len fs) < 2 ^ 64.
Proof. intros m p fs (Hp & Hn & _). lia. Qed.

Lemma Z_to_le_bytes_0 : forall k, Z_to_le_bytes k 0 = repeat (Z_to_bv 8 0) k.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [Z_to_le_bytes repeat]. rewrite Z.shiftr_0_l, IH. reflexivity. Qed.

Lemma zflds_bytes : forall ks, flds_bytes (zflds ks) = repeat (Z_to_bv 8 0) (flds_len (zflds ks)).
Proof. induction ks as [|k t IH]; [reflexivity|]. cbn [zflds flds_bytes flds_len]. rewrite IH, repeat_app, Z_to_le_bytes_0. reflexivity. Qed.

Lemma zflds_wf : forall ks, Forall (fun k => (k <= 8)%nat) ks -> flds_wf (zflds ks).
Proof.
  induction ks as [|k t IH]; intros H; [exact I|]. inversion H; subst. cbn [zflds flds_wf]. split; [| apply IH; assumption].
  split; [| assumption]. split; [lia|]. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma RECat_zero : forall m p (ks : list nat), 0 <= p -> p + Z.of_nat (flds_len (zflds ks)) < 2 ^ 64 ->
  Forall (fun k => (k <= 8)%nat) ks ->
  (forall i, 0 <= i < Z.of_nat (flds_len (zflds ks)) -> m (Z_to_bv 64 (p + i)) = Some (Z_to_bv 8 0)) ->
  RECat m p (zflds ks).
Proof.
  intros m p ks Hp Hn Hks HZ. split; [lia|]. split; [lia|]. split; [exact (zflds_wf ks Hks)|].
  rewrite zflds_bytes. apply bytes_at_zeros. exact HZ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma REC_rd : forall m p fs (i : nat), RECat m p fs -> (i < length fs)%nat ->
  rdn segs m (Z_to_bv 64 (p + Z.of_nat (fld_off fs i))) (fst (fld_get fs i)) =
  Some (Z_to_le_bytes (fst (fld_get fs i)) (snd (fld_get fs i))).
Proof.
  intros m p fs i (Hp & Hn & WF & HB) Hi. pose proof (fld_off_get_len fs i Hi) as L.
  rewrite <- (flds_bytes_split fs i Hi).
  apply (bytes_at_field segs m p (flds_bytes fs) (fld_off fs i) (fst (fld_get fs i))); rewrite ?flds_bytes_len; try lia. exact HB.
Qed.

(* [comment removed for export] *)
Lemma REC_rd_val : forall fs i, flds_wf fs -> (i < length fs)%nat ->
  bytes_le_to_Z (Z_to_le_bytes (fst (fld_get fs i)) (snd (fld_get fs i))) = snd (fld_get fs i).
Proof.
  intros fs i WF Hi. destruct (fld_get_wf fs i WF Hi) as [R K].
  rewrite bytes_le_to_Z_of_le_bytes by lia. apply Z.mod_small. exact R.
Qed.

Lemma REC_wr : forall m p fs (i : nat) z, RECat m p fs -> (i < length fs)%nat ->
  0 <= z < 2 ^ (8 * Z.of_nat (fst (fld_get fs i))) ->
  RECat (wbytes m (Z_to_bv 64 (p + Z.of_nat (fld_off fs i))) (word_to_le_bytes (fst (fld_get fs i)) (Z_to_bv 64 z))) p (fld_set fs i z).
Proof.
  intros m p fs i z (Hp & Hn & WF & HB) Hi Hz. pose proof (fld_off_get_len fs i Hi) as L. destruct (fld_get_wf fs i WF Hi) as [_ K].
  assert (Hz64 : 0 <= z < 2 ^ 64).
  { split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hz)|]. apply Z.pow_le_mono_r; lia. }
  split; [lia|]. split; [rewrite fld_set_len; lia|]. split; [apply fld_set_wf; assumption|].
  rewrite (fld_set_bytes fs i z Hi). rewrite w2b_Z by exact Hz64.
  pose proof (bytes_at_wbytes_in m p (flds_bytes fs) (fld_off fs i) (Z_to_le_bytes (fst (fld_get fs i)) z) HB ltac:(lia)
                ltac:(rewrite flds_bytes_len; lia) ltac:(rewrite flds_bytes_len, length_Z_to_le_bytes; lia)) as H.
  rewrite length_Z_to_le_bytes in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma REC_wr' : forall m p fs fs' (i k : nat) (a : word) z, RECat m p fs -> (i < length fs)%nat ->
  0 <= z < 2 ^ (8 * Z.of_nat k) ->
  k = fst (fld_get fs i) -> a = Z_to_bv 64 (p + Z.of_nat (fld_off fs i)) -> fs' = fld_set fs i z ->
  RECat (wbytes m a (word_to_le_bytes k (Z_to_bv 64 z))) p fs'.
Proof. intros m p fs fs' i k a z HR Hi Hz -> -> ->. apply REC_wr; assumption. Qed.

(* [comment removed for export] *)
Lemma REC_rd' : forall m p fs (i k : nat) (a : word) v, RECat m p fs -> (i < length fs)%nat ->
  k = fst (fld_get fs i) -> a = Z_to_bv 64 (p + Z.of_nat (fld_off fs i)) -> v = snd (fld_get fs i) ->
  rdn segs m a k = Some (Z_to_le_bytes k v).
Proof. intros m p fs i k a v HR Hi -> -> ->. apply REC_rd; assumption. Qed.

(* [comment removed for export] *)
Lemma RECat_set_rdn : forall m m' p fs (i : nat) z, RECat m p fs -> (i < length fs)%nat ->
  0 <= z < 2 ^ (8 * Z.of_nat (fst (fld_get fs i))) ->
  (forall x : word, p <= u x < p + Z.of_nat (flds_len fs) ->
     ~ (p + Z.of_nat (fld_off fs i) <= u x < p + Z.of_nat (fld_off fs i) + Z.of_nat (fst (fld_get fs i))) -> m' x = m x) ->
  (forall x : word, p <= u x < p + Z.of_nat (flds_len fs) -> m' x <> None) ->
  rdn segs m' (Z_to_bv 64 (p + Z.of_nat (fld_off fs i))) (fst (fld_get fs i)) = Some (Z_to_le_bytes (fst (fld_get fs i)) z) ->
  RECat m' p (fld_set fs i z).
Proof.
  intros m m' p fs i z (Hp & Hn & WF & HB) Hi Hz FR DEF R.
  pose proof (fld_off_get_len fs i Hi) as L. destruct (fld_get_wf fs i WF Hi) as [_ K].
  split; [lia|]. split; [rewrite fld_set_len; lia|]. split; [apply fld_set_wf; assumption|].
  rewrite (fld_set_bytes fs i z Hi).
  set (off := fld_off fs i) in *. set (k := fst (fld_get fs i)) in *.
  pose proof HB as HB1. rewrite <- (firstn_skipn off (flds_bytes fs)) in HB1. apply bytes_at_app in HB1 as [H1 H23].
  rewrite <- (firstn_skipn k (skipn off (flds_bytes fs))) in H23. apply bytes_at_app in H23 as [_ H3].
  assert (E1 : length (firstn off (flds_bytes fs)) = off) by (rewrite length_firstn, flds_bytes_len; lia).
  assert (E2 : length (firstn k (skipn off (flds_bytes fs))) = k) by (rewrite length_firstn, length_skipn, flds_bytes_len; lia).
  rewrite E1, E2 in H3. rewrite skipn_skipn in H3. replace (k + off)%nat with (off + k)%nat in H3 by lia.
  apply bytes_at_app; split; [| apply bytes_at_app; split].
  - eapply bytes_at_frame; [exact H1 | rewrite E1 | lia | rewrite E1; lia]. intros x Hx. apply FR; lia.
  - rewrite E1.
    apply (rdn_bytes_at segs m' _ (Z_to_le_bytes k z)); rewrite ?length_Z_to_le_bytes; [lia | lia | | exact R].
    intros j Hj. apply DEF. rewrite u_Z2bv by lia. lia.
  - rewrite E1, length_Z_to_le_bytes.
    eapply bytes_at_frame; [exact H3 | | lia | rewrite length_skipn, flds_bytes_len; lia].
    rewrite length_skipn, flds_bytes_len. intros x Hx. apply FR; lia.
Qed.

End WithSegs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
