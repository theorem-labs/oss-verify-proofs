(** e's 104 bytes as the turn's stores and copies leave them: [upd_bytes] on runs of zeros, for the walks of the
    kinds that write a text body (ent_text). Byte-list facts only. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import EntFacts.
Import ListNotations.
Open Scope Z_scope.

Lemma zeros_add : forall a b, zeros (a + b) = zeros a ++ zeros b.
Proof. intros a b. unfold zeros. apply repeat_app. Qed.

Lemma skipn_zeros : forall k n, skipn k (zeros n) = zeros (n - k).
Proof.
  induction k as [|k IH]; intros n; [cbn [skipn]; rewrite Nat.sub_0_r; reflexivity|].
  destruct n as [|n]; [reflexivity|]. cbn [skipn zeros repeat]. apply IH.
Qed.

Lemma firstn_zeros : forall k n, firstn k (zeros n) = zeros (Nat.min k n).
Proof.
  induction k as [|k IH]; intros n; [reflexivity|].
  destruct n as [|n]; [reflexivity|]. cbn [firstn zeros repeat Nat.min]. f_equal. apply IH.
Qed.

(** A write inside the first part of a run, or inside the second. *)
Lemma upd_bytes_app_l : forall (h t bs : list byte) k, (k + length bs <= length h)%nat ->
  upd_bytes (h ++ t) k bs = upd_bytes h k bs ++ t.
Proof.
  intros h t bs k H. unfold upd_bytes. rewrite firstn_app, skipn_app.
  replace (k - length h)%nat with 0%nat by lia. replace (k + length bs - length h)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma upd_bytes_app_r : forall (h t bs : list byte) k, (length h <= k)%nat ->
  upd_bytes (h ++ t) k bs = h ++ upd_bytes t (k - length h) bs.
Proof.
  intros h t bs k H. unfold upd_bytes. rewrite firstn_app, skipn_app.
  rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. cbn [app].
  replace (k + length bs - length h)%nat with (k - length h + length bs)%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

(** A run of zeros written at its start. *)
Lemma upd_bytes_zeros0 : forall bs n, (length bs <= n)%nat -> upd_bytes (zeros n) 0 bs = bs ++ zeros (n - length bs).
Proof. intros bs n H. unfold upd_bytes. cbn [firstn app]. rewrite skipn_zeros. reflexivity. Qed.

(** A NUL written inside a run of zeros changes nothing. *)
Lemma upd_bytes_zeros_nul : forall n k, (k < n)%nat -> upd_bytes (zeros n) k [NUL] = zeros n.
Proof.
  intros n k H. unfold upd_bytes. rewrite firstn_zeros, skipn_zeros. cbn [length].
  replace (zeros n) with (zeros (Nat.min k n + (1 + (n - (k + 1))))) by (f_equal; lia).
  rewrite !zeros_add. reflexivity.
Qed.

(** e's bytes as 8 head bytes, the body, zeros to 96. *)
Definition ebytes (h b : list byte) : list byte := h ++ b ++ zeros (96 - length b).

Lemma ebytes_zero : ebytes (zeros 8) [] = zeros 104.
Proof. reflexivity. Qed.

(** A run copied at the end of the body (offset 8 + |b|). *)
Lemma ebytes_put : forall h b bs, length h = 8%nat -> (length b + length bs <= 96)%nat ->
  upd_bytes (ebytes h b) (8 + length b) bs = ebytes h (b ++ bs).
Proof.
  intros h b bs Hh Hb. unfold ebytes. rewrite upd_bytes_app_r by lia. rewrite Hh.
  replace (8 + length b - 8)%nat with (length b + 0)%nat by lia.
  rewrite upd_bytes_app_r by lia. replace (length b + 0 - length b)%nat with 0%nat by lia.
  rewrite upd_bytes_zeros0 by lia. rewrite length_app, <- !app_assoc.
  replace (96 - length b - length bs)%nat with (96 - (length b + length bs))%nat by lia. reflexivity.
Qed.

(** A NUL written past the body's end, into its zeros. *)
Lemma ebytes_nul : forall h b k, length h = 8%nat -> (8 + length b <= k < 104)%nat ->
  upd_bytes (ebytes h b) k [NUL] = ebytes h b.
Proof.
  intros h b k Hh Hk. unfold ebytes. rewrite upd_bytes_app_r by lia. rewrite upd_bytes_app_r by lia.
  rewrite upd_bytes_zeros_nul by lia. reflexivity.
Qed.

(** A write into the 8 head bytes (type at 0, size at 4). *)
Lemma ebytes_head : forall h b k bs, (k + length bs <= length h)%nat ->
  upd_bytes (ebytes h b) k bs = ebytes (upd_bytes h k bs) b.
Proof. intros h b k bs H. unfold ebytes. apply upd_bytes_app_l. exact H. Qed.

(** The head with the type and size put. *)
Lemma ebytes_ent : forall h t z b, length h = 8%nat ->
  ebytes (upd_bytes (upd_bytes h 0 (le32 t)) 4 (le32 z)) b = le32 t ++ le32 z ++ b ++ zeros (96 - length b).
Proof.
  intros h t z b Hh. unfold ebytes, upd_bytes.
  destruct h as [|h0 [|h1 [|h2 [|h3 [|h4 [|h5 [|h6 [|h7 [|]]]]]]]]]; cbn in Hh; try lia. reflexivity.
Qed.

Lemma ebytes_ent_mem : forall h e, length h = 8%nat ->
  ebytes (upd_bytes (upd_bytes h 0 (le32 (e_type e))) 4 (le32 (e_size e))) (e_body e) = ent_mem e.
Proof. intros h e Hh. rewrite ebytes_ent by exact Hh. reflexivity. Qed.

Lemma length_upd_head : forall h k bs, (k + length bs <= length h)%nat -> length (upd_bytes h k bs) = length h.
Proof. intros. apply upd_bytes_length. exact H. Qed.

Lemma ebytes_put' : forall h b bs k, length h = 8%nat -> k = (8 + length b)%nat -> (length b + length bs <= 96)%nat ->
  upd_bytes (ebytes h b) k bs = ebytes h (b ++ bs).
Proof. intros h b bs k Hh -> Hb. apply ebytes_put; assumption. Qed.

Lemma ebytes_head' : forall h b k bs, (k + length bs <= length h)%nat ->
  upd_bytes (ebytes h b) k bs = ebytes (upd_bytes h k bs) b.
Proof. exact ebytes_head. Qed.

(** ent_text's 104 bytes as kinds 0 and 1 make them: s copied at 8, a NUL after it, type at 0, size at 4. *)
Lemma text_head : forall s nb k1 k2, nb = [NUL] -> k1 = 8%nat -> k2 = (8 + length s)%nat -> (length s <= 95)%nat ->
  upd_bytes (upd_bytes (zeros 104) k1 s) k2 nb = ebytes (zeros 8) (s ++ [NUL]).
Proof.
  intros s nb k1 k2 -> -> -> Hs.
  change (zeros 104) with (ebytes (zeros 8) []).
  rewrite (ebytes_put' (zeros 8) [] s 8) by (cbn; lia). cbn [app].
  rewrite (ebytes_put' (zeros 8) s [NUL] (8 + length s)) by (cbn; lia). reflexivity.
Qed.

Lemma text_chain : forall s nb t z k1 k2 k3 k4, nb = [NUL] -> k1 = 8%nat -> k2 = (8 + length s)%nat -> k3 = 0%nat ->
  k4 = 4%nat -> (length s <= 95)%nat ->
  upd_bytes (upd_bytes (upd_bytes (upd_bytes (zeros 104) k1 s) k2 nb) k3 (le4 (Z_to_bv 64 t))) k4 (le4 (Z_to_bv 64 z))
  = ent_mem (Ent t z (s ++ [NUL])).
Proof.
  intros s nb t z k1 k2 k3 k4 E1 E2 E3 -> -> Hs. rewrite (text_head s nb k1 k2 E1 E2 E3 Hs).
  rewrite ebytes_head' by (cbn; lia). rewrite ebytes_head' by (unfold upd_bytes; cbn; lia).
  rewrite !le4_any. rewrite ebytes_ent by reflexivity. reflexivity.
Qed.

(** Kind 1 with kind's bit 7: then a NUL at 8 + |s| + 2, 'x' at 8 + |s| + 1, the size again. *)
Lemma text_chain_x : forall s nb nb2 nx t z z' k1 k2 k3 k4 k5 k6 k7,
  nb = [NUL] -> nb2 = [NUL] -> nx = [Z_to_bv 8 120] -> k1 = 8%nat -> k2 = (8 + length s)%nat -> k3 = 0%nat ->
  k4 = 4%nat -> k5 = (8 + length s + 2)%nat -> k6 = (8 + length s + 1)%nat -> k7 = 4%nat -> (length s <= 93)%nat ->
  upd_bytes (upd_bytes (upd_bytes (upd_bytes (upd_bytes (upd_bytes (upd_bytes (zeros 104) k1 s) k2 nb) k3
    (le4 (Z_to_bv 64 t))) k4 (le4 (Z_to_bv 64 z))) k5 nb2) k6 nx) k7 (le4 (Z_to_bv 64 z'))
  = ent_mem (Ent t z' ((s ++ [NUL]) ++ [Z_to_bv 8 120; NUL])).
Proof.
  intros s nb nb2 nx t z z' k1 k2 k3 k4 k5 k6 k7 E1 -> -> E2 E3 -> -> -> -> -> Hs.
  rewrite (text_head s nb k1 k2 E1 E2 E3 ltac:(lia)).
  rewrite ebytes_head' by (cbn; lia). rewrite ebytes_head' by (unfold upd_bytes; cbn; lia).
  rewrite ebytes_nul by (rewrite ?length_app; cbn [length]; unfold upd_bytes; cbn; lia).
  rewrite ebytes_put' by (rewrite ?length_app; cbn [length]; unfold upd_bytes; cbn; lia).
  rewrite ebytes_head' by (unfold upd_bytes; cbn; lia).
  rewrite !le4_any. unfold ebytes, ent_mem. cbn [e_type e_size e_body].
  rewrite !length_app. cbn [length].
  replace (96 - (length s + 1 + 1))%nat with (1 + (96 - (length s + 1 + 2)))%nat by lia.
  rewrite zeros_add. rewrite <- !app_assoc. cbn [app]. unfold upd_bytes, le32. cbn. reflexivity.
Qed.
