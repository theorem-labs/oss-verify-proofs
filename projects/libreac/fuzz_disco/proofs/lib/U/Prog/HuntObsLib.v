From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcParse CtrlParsed disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_frame_clean_len_c reac_disco_table_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import hunt_c reac_hunt_observe_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sub_split : forall (l : list byte) k n1 n2, 0 <= k ->
  sub l k (n1 + n2) = sub l k n1 ++ sub l (k + Z.of_nat n1) n2.
Proof.
  intros l k n1 n2 Hk. unfold sub. replace (Z.to_nat (k + Z.of_nat n1)) with (n1 + Z.to_nat k)%nat by lia.
  rewrite <- skipn_skipn. generalize (skipn (Z.to_nat k) l) as l'. clear l k Hk.
  induction n1 as [|n1 IH]; intros l'; [reflexivity|]. destruct l' as [|x l']; cbn.
  - destruct n2; reflexivity.
  - f_equal. apply IH.
Qed.

Lemma sub_all : forall (l : list byte) k n, 0 <= k -> (Z.to_nat k + n)%nat = length l -> sub l k n = skipn (Z.to_nat k) l.
Proof. intros l k n Hk Hn. unfold sub. apply firstn_all2. rewrite length_skipn. lia. Qed.

Lemma sub_app_l : forall (A B : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length A) ->
  sub (A ++ B) k n = sub A k n.
Proof.
  intros A B k n Hk Hn. unfold sub. rewrite skipn_app. replace (Z.to_nat k - length A)%nat with O by lia.
  cbn [skipn]. rewrite firstn_app. rewrite length_skipn. replace (n - (length A - Z.to_nat k))%nat with O by lia.
  cbn [firstn]. apply app_nil_r.
Qed.

Lemma sub_app_r : forall (A B : list byte) k n, Z.of_nat (length A) <= k ->
  sub (A ++ B) k n = sub B (k - Z.of_nat (length A)) n.
Proof.
  intros A B k n Hk. unfold sub. rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  f_equal. f_equal. lia.
Qed.

Lemma sub_skipn : forall (H : list byte) k j n, 0 <= j -> sub (skipn k H) j n = sub H (Z.of_nat k + j) n.
Proof. intros H k j n Hj. unfold sub. rewrite skipn_skipn. f_equal. f_equal. lia. Qed.

Lemma sub_sub : forall (l : list byte) k n j n', 0 <= k -> 0 <= j -> j + Z.of_nat n' <= Z.of_nat n ->
  sub (sub l k n) j n' = sub l (k + j) n'.
Proof.
  intros l k n j n' Hk Hj Hn. unfold sub. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n' (n - Z.to_nat j)) with n' by lia. f_equal. f_equal. lia.
Qed.

Lemma sub_whole : forall (l : list byte) n, length l = n -> sub l 0 n = l.
Proof. intros l n H. unfold sub. cbn [Z.to_nat skipn]. apply firstn_all2. lia. Qed.

Lemma len_sub : forall (l : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length l) -> length (sub l k n) = n.
Proof. intros l k n Hk H. unfold sub. rewrite length_firstn, length_skipn. lia. Qed.

Lemma ble1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof.
  intros b. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

Lemma ble_le4 : forall z, 0 <= z < 2^32 -> bytes_le_to_Z (le4 (Z_to_bv 64 z)) = z.
Proof.
  intros z Hz. unfold le4. rewrite bytes_le_to_Z_to_le_bytes by (apply bv_unsigned_in_range).
  rewrite unsigned_lit by lia. apply Z.mod_small. cbn. lia.
Qed.

Lemma dkind_len : forall F len, dkind F len <> 0 -> 50 <= len.
Proof.
  intros F len. unfold dkind, ctrlparse. destruct (cp_hdr len F) eqn:E.
  - intros _. apply cp_hdr_spec in E. tauto.
  - cbn [fst]. intros X. exfalso. apply X. reflexivity.
Qed.

Lemma dkind1 : forall F len, dkind F len = 1 -> fb F 16 = 0 /\ fb F 17 = 0.
Proof.
  intros F len H. unfold dkind in H. apply ctrlparse_filler in H. destruct H as (_ & H16 & H17).
  split; [exact H16 | exact H17].
Qed.

Lemma cm_ret_cases : forall F len U L, cm_ret F len U L = 0 \/ cm_ret F len U L = -1.
Proof.
  intros F len U L. unfold cm_ret, classify_model. cbv beta zeta.
  destruct L as [Lb|]; cbv beta iota;
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end); cbn; auto.
Qed.

Lemma cm_ret0_len : forall F len U L, cm_ret F len U L = 0 -> 50 <= len.
Proof.
  intros F len U L. unfold cm_ret, classify_model. cbv beta zeta.
  destruct (dkind F len =? 0) eqn:K; [cbn; discriminate|]. intros _. apply (dkind_len F). apply Z.eqb_neq. exact K.
Qed.

Lemma cm_ret0_facts : forall F len U L, cm_ret F len U L = 0 ->
  bytes_eqb (src F) U = false /\ (dkind F len = 1 \/ fsum F = 0).
Proof.
  intros F len U L. unfold cm_ret, classify_model. cbv beta zeta.
  destruct (dkind F len =? 0); [cbn; discriminate|].
  destruct (bytes_eqb (src F) U); [cbn; discriminate|].
  destruct (negb (dkind F len =? 1) && negb (fsum F =? 0)) eqn:S; [cbn; discriminate|].
  intros _. split; [reflexivity|].
  apply andb_false_iff in S. destruct S as [S|S]; apply negb_false_iff in S; apply Z.eqb_eq in S; auto.
Qed.

Lemma cm_out_ok : forall F len U Lb OB, cm_ret F len U (Some Lb) = 0 -> cm_out F len U (Some Lb) OB = sight F len.
Proof.
  intros F len U Lb OB. unfold cm_ret, cm_out, classify_model. cbv beta zeta iota.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end); cbn; intros X; first [discriminate X | reflexivity].
Qed.

Lemma cm_lock_some : forall F len U Lb, exists Lb', cm_lock F len U (Some Lb) = Some Lb'.
Proof.
  intros F len U Lb. unfold cm_lock, classify_model. cbv beta zeta iota.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end); cbn; eexists; reflexivity.
Qed.

Lemma cm_lock_fail : forall F len U Lb, cm_ret F len U (Some Lb) <> 0 -> cm_lock F len U (Some Lb) = Some Lb.
Proof.
  intros F len U Lb. unfold cm_ret, cm_lock, classify_model. cbv beta zeta iota.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end); cbn; intros X;
    first [reflexivity | exfalso; apply X; reflexivity].
Qed.

Lemma len_src : forall F, length F = 50%nat -> length (src F) = 6%nat.
Proof. intros F H. unfold src, fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma latch_ok : forall F Lb, length F = 50%nat -> length Lb = 12%nat -> lock_ok (latch F Lb).
Proof.
  intros F Lb HF HL. pose proof (len_src F HF) as LS.
  assert (L2 : length (fld Lb 6 2) = 2%nat) by (unfold fld; rewrite length_firstn, length_skipn; lia).
  unfold lock_ok, latch. set (A := src F) in *. set (B := fld Lb 6 2) in *. split.
  - rewrite !length_app, LS, L2, length_le4. reflexivity.
  - right. unfold fu. unfold fld at 1. rewrite skipn_app, LS. cbn [Nat.sub]. rewrite skipn_all2 by lia. cbn [app].
    rewrite skipn_app, L2. cbn [Nat.sub skipn]. rewrite skipn_all2 by lia. cbn [app]. vm_compute. reflexivity.
Qed.

Lemma cm_lock_ok : forall F len U Lb Lb', (50 <= len -> length F = 50%nat) -> lock_ok Lb ->
  cm_lock F len U (Some Lb) = Some Lb' -> lock_ok Lb'.
Proof.
  intros F len U Lb Lb' HF LOK E. unfold cm_lock, classify_model in E. cbv beta zeta iota in E.
  destruct (dkind F len =? 0) eqn:K0; [cbn [snd] in E; injection E as <-; exact LOK|].
  destruct (bytes_eqb (src F) U); [cbn [snd] in E; injection E as <-; exact LOK|].
  destruct (negb (dkind F len =? 1) && negb (fsum F =? 0)); [cbn [snd] in E; injection E as <-; exact LOK|].
  destruct ((dkind F len =? 1) && negb (lv Lb =? 0) && negb (bytes_eqb (lm Lb) (src F)));
    [cbn [snd] in E; injection E as <-; exact LOK|].
  cbn [snd] in E. injection E as <-. destruct (negb (dkind F len =? 1) && (lv Lb =? 0)); [|exact LOK].
  apply latch_ok; [apply HF; apply (dkind_len F); apply Z.eqb_neq; exact K0 | destruct LOK as [X _]; exact X].
Qed.

Lemma rwc_flat : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs [[Hwf Hb] Hw]. split; [split|].
  - cbn. split; [apply cells_bytes_length; exact Hwf | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.






