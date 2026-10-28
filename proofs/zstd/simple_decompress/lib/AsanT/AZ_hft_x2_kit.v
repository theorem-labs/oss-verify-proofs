(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuildThm.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition c2ok (T : Z) (dt : list Z) (u : Z) : Prop := 0 <= Znth (4 * u + 6) dt <= T /\ 1 <= Znth (4 * u + 7) dt <= 2.
Definition x2pref (T cur : Z) (dt : list Z) : Prop := forall u, 0 <= u < cur -> c2ok T dt u.
Definition x2prf (T c : Z) (ks : list Z) (dt : list Z) : Prop := x2pref T c dt /\ forall k, In k ks -> 0 <= k /\ c2ok T dt (c + k).

Lemma x2pref_0 : forall T dt, x2pref T 0 dt.
Proof. intros T dt u Hu. lia. Qed.
Lemma x2prf_open : forall T c dt, x2pref T c dt -> x2prf T c [] dt.
Proof. intros T c dt P. split; [exact P|]. intros k []. Qed.

Lemma c2ok_upd_other : forall T dt u j v, c2ok T dt u -> 0 <= u -> 0 <= j -> (j < 4 * u + 6 \/ 4 * u + 8 <= j) -> c2ok T (Zupd j v dt) u.
Proof. intros T dt u j v [A B] Hu Hj0 Hj. split; rewrite Znth_Zupd_other by lia; assumption. Qed.

(* [comment removed for export] *)
Lemma prf2_st_sq : forall T c ks dt k i a b, x2prf T c ks dt -> 0 <= c -> 0 <= k -> i = 4 + 4 * (c + k) ->
  x2prf T c ks (Zupd (i + 1) b (Zupd i a dt)).
Proof.
  intros T c ks dt k i a b [P K] Hc Hk ->. split.
  - intros u Hu. apply c2ok_upd_other; [apply c2ok_upd_other; [apply P; lia| lia| lia| lia] | lia| lia| lia].
  - intros k' IN. destruct (K k' IN) as [K0 KV]. split; [exact K0|].
    apply c2ok_upd_other; [apply c2ok_upd_other; [exact KV| lia| lia| lia] | lia| lia| lia].
Qed.
(* [comment removed for export] *)
Lemma prf2_st_sq1 : forall T c ks dt k i a, x2prf T c ks dt -> 0 <= c -> 0 <= k -> (i = 4 + 4 * (c + k) \/ i = 4 + 4 * (c + k) + 1) ->
  x2prf T c ks (Zupd i a dt).
Proof.
  intros T c ks dt k i a [P K] Hc Hk Hi. split.
  - intros u Hu. apply c2ok_upd_other; [apply P; lia| lia| lia| lia].
  - intros k' IN. destruct (K k' IN) as [K0 KV]. split; [exact K0|]. apply c2ok_upd_other; [exact KV| lia| lia| lia].
Qed.
(* [comment removed for export] *)
Lemma prf2_st_nl : forall T c ks dt k i nb ln, x2prf T c ks dt -> 0 <= c -> 0 <= k -> i = 4 + 4 * (c + k) + 2 -> i + 1 < Z.of_nat (length dt) ->
  0 <= nb <= T -> 1 <= ln <= 2 ->
  x2prf T c (k :: ks) (Zupd (i + 1) ln (Zupd i nb dt)).
Proof.
  intros T c ks dt k i nb ln [P K] Hc Hk -> HL Hnb Hln. unfold FseNCount.Zlength in *. split.
  - intros u Hu. apply c2ok_upd_other; [apply c2ok_upd_other; [apply P; lia| lia| lia| lia] | lia| lia| lia].
  - intros k' [<-|IN].
    + split; [lia|]. split.
      * replace (4 * (c + k) + 6) with (4 + 4 * (c + k) + 2) by lia. rewrite Znth_Zupd_other by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). exact Hnb.
      * replace (4 * (c + k) + 7) with (4 + 4 * (c + k) + 2 + 1) by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite Zupd_length; lia). exact Hln.
    + destruct (K k' IN) as [K0 KV]. split; [exact K0|].
      destruct (Z.eq_dec k' k) as [->|NE].
      * split.
        -- replace (4 * (c + k) + 6) with (4 + 4 * (c + k) + 2) by lia. rewrite Znth_Zupd_other by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). exact Hnb.
        -- replace (4 * (c + k) + 7) with (4 + 4 * (c + k) + 2 + 1) by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite Zupd_length; lia). exact Hln.
      * apply c2ok_upd_other; [apply c2ok_upd_other; [exact KV| lia| lia| lia] | lia| lia| lia].
Qed.
(* [comment removed for export] *)
Lemma prf2_close : forall T c ks dt L, x2prf T c ks dt -> 0 <= c -> (forall k, 0 <= k < L -> In k ks) -> x2pref T (c + L) dt.
Proof.
  intros T c ks dt L [P K] Hc COV u Hu. destruct (Z.lt_ge_cases u c) as [LT|GE]; [apply P; lia|].
  replace u with (c + (u - c)) by lia. apply (fun IN => proj2 (K _ IN)). apply COV. lia.
Qed.
Lemma prf2_close_c : forall T c ks dt (L : nat), x2prf T c ks dt -> 0 <= c -> cover L ks = true -> x2pref T (c + Z.of_nat L) dt.
Proof. intros T c ks dt L P Hc C. apply (prf2_close T c ks dt); [exact P | exact Hc | apply cover_ok; exact C]. Qed.
(* [comment removed for export] *)
Lemma x2pref_upd_hi : forall T cur dt j v, x2pref T cur dt -> 4 + 4 * cur <= j -> x2pref T cur (Zupd j v dt).
Proof. intros T cur dt j v P Hj u Hu. apply c2ok_upd_other; [apply P; lia| lia| lia| lia]. Qed.
Lemma x2pref_mono : forall T a b dt, x2pref T b dt -> a <= b -> x2pref T a dt.
Proof. intros T a b dt P H u Hu. apply P. lia. Qed.
(* [comment removed for export] *)
Lemma x2pref_upd_hdr : forall T cur dt j v, x2pref T cur dt -> 0 <= j < 4 -> x2pref T cur (Zupd j v dt).
Proof. intros T cur dt j v P Hj u Hu. apply c2ok_upd_other; [apply P; lia| lia| lia| lia]. Qed.
(* [comment removed for export] *)
Lemma x2pref_T_le : forall T T' cur dt, x2pref T cur dt -> T <= T' -> x2pref T' cur dt.
Proof. intros T T' cur dt P H u Hu. destruct (P u Hu) as [A B]. split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition d1_chk : bool :=
  forallb (fun nb => forallb (fun s =>
    let X := Z.lor (65536 * nb + 16777216) s in
    (X mod 256 =? s) && ((X / 256) mod 256 =? 0) && ((X / 65536) mod 256 =? nb) && ((X / 65536 / 256) mod 256 =? 1) && (X / 65536 =? nb + 256) && (X =? 65536 * nb + 16777216 + s))
    (zseq 256 0)) (zseq 13 0).
Lemma d1_chk_ok : d1_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma d1_bytes : forall nb s, 0 <= nb <= 12 -> 0 <= s < 256 ->
  Z.lor (65536 * nb + 16777216) s mod 256 = s /\ (Z.lor (65536 * nb + 16777216) s / 256) mod 256 = 0
  /\ (Z.lor (65536 * nb + 16777216) s / 65536) mod 256 = nb /\ (Z.lor (65536 * nb + 16777216) s / 65536 / 256) mod 256 = 1
  /\ Z.lor (65536 * nb + 16777216) s / 65536 = nb + 256 /\ Z.lor (65536 * nb + 16777216) s = 65536 * nb + 16777216 + s.
Proof.
  intros nb s Hnb Hs. pose proof d1_chk_ok as C. unfold d1_chk in C. rewrite forallb_forall in C.
  specialize (C nb ltac:(apply zseq_In_iff; lia)). rewrite forallb_forall in C. specialize (C s ltac:(apply zseq_In_iff; lia)).
  cbv beta in C. repeat (apply andb_prop in C; destruct C as [C ?C1]).
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end. repeat split; assumption.
Qed.
