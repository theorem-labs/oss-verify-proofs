(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanF.v at 225c2086379 for reac-pw/fuzz_rate:
   the Pod model's Role answers become Rate's (Rate.rate_of_pairs, Rate.expect_value, Rate.expect_model,
   Rate.harness_parse), the cut file is lib/A/RtPgSeg.v; the role-specific answer cases and the role cell are
   dropped, the answer's shape is Rate.answer_ok. *)
(* reac-pw/fuzz_rate, the image-A walk of LLVMFuzzerTestOneInput: THE MODEL FACTS the checking segment's scan
   lemmas use. Proves no function (kind: model fact): every lemma here is a fact of the shared Pod model (lib/Pod)
   and of lib/A/RtPgSeg.v's scan invariant rs_scan_inv; no binary, no image and no address occurs.

   WHAT THE SCAN COMPUTES. The inlined expect_rate (fuzz_rate.c:63-87) walks the record's entries with
   pod_next_pair (pod.h:124-145): an entry that is not a String key is skipped and the key slot stays open, a String
   key takes the slot, and the entry after a key is its value, whatever it is. That is exactly
   Accessors.pairs_by Accessors.key_of over the entries, and the answer is Rate.rate_of_pairs Rate.expect_value of
   those pairs, which lib/A/RtPgSeg.v names rs_E0 and keeps as the invariant rs_scan_inv rec j ("the answer is the
   answer of the pairs of the entries from j on, with no key pending").

   The lemmas below are the four moves the two loops make, and the three ends they can take:
     rk_inv_skip   the entry at m is not a key: the invariant moves to m + 1
     rk_inv_run    a run of entries that are not keys: the invariant moves across it
     rk_inv_key    the entry at m is a key and the entry at m + 1 is its value: the pairs are that pair, then the
                   pairs from m + 2 on, which is what the cut at the key match carries
     rk_inv_end    no entry is left: the answer is (None, 0), the absent check's
     rk_inv_last   the entry at m is the last one, so it starts no pair: the answer is (None, 0) again
   and, for the set-up and the head: the answer of a record that is not an Object of Props is (None, -1), of one
   whose params property is not a Struct is (None, 0), the answer of the parse on an uncorrupted record is the same
   as the scan's (Rate.parse_model_encode), the answer with the NULL flag is (None, -1), and both answers have
   Rate.answer_ok's shape. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa Nearest.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Definition rk_d : ent := Ent 0 0 [].

(* ========================= lists ========================= *)
Lemma rk_skipn_cons : forall {A : Type} (l : list A) (j : nat) (d : A), (j < length l)%nat ->
skipn j l = nth j l d :: skipn (S j) l.
Proof.
intros A l. induction l as [|x l IH]; intros j d Hj; cbn [length] in Hj; [lia|].
destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in Hj. lia.
Qed.

(* ========================= the pairs of the record's entries ========================= *)
Lemma rk_pairs_skip : forall (es : list ent) (m : nat), (m < length es)%nat ->
key_of (nth m es rk_d) = None ->
pairs_by key_of (skipn m es) None = pairs_by key_of (skipn (S m) es) None.
Proof.
intros es m Hm Hk. rewrite (rk_skipn_cons es m rk_d Hm). cbn [pairs_by]. rewrite Hk. reflexivity.
Qed.

Lemma rk_pairs_run : forall (es : list ent) (a m : nat), (a <= m)%nat -> (m <= length es)%nat ->
(forall q, (a <= q < m)%nat -> key_of (nth q es rk_d) = None) ->
pairs_by key_of (skipn a es) None = pairs_by key_of (skipn m es) None.
Proof.
intros es a m. remember (m - a)%nat as n eqn:Hn. revert a m Hn.
induction n as [|n IH]; intros a m Hn Ham Hml Hq.
- assert (a = m) as -> by lia. reflexivity.
- rewrite (rk_pairs_skip es a ltac:(lia) (Hq a ltac:(lia))).
  apply (IH (S a) m); [lia | lia | lia |]. intros q Hqq. apply Hq. lia.
Qed.

Lemma rk_pairs_key : forall (es : list ent) (m : nat) (kb : list byte), (S m < length es)%nat ->
key_of (nth m es rk_d) = Some kb ->
pairs_by key_of (skipn m es) None = (kb, nth (S m) es rk_d) :: pairs_by key_of (skipn (S (S m)) es) None.
Proof.
intros es m kb Hm Hk.
rewrite (rk_skipn_cons es m rk_d ltac:(lia)). cbn [pairs_by]. rewrite Hk.
rewrite (rk_skipn_cons es (S m) rk_d Hm). cbn [pairs_by]. reflexivity.
Qed.

Lemma rk_pairs_end : forall (es : list ent) (m : nat), (length es <= m)%nat ->
pairs_by key_of (skipn m es) None = [].
Proof. intros es m H. rewrite skipn_all2 by exact H. reflexivity. Qed.

Lemma rk_pairs_last : forall (es : list ent) (m : nat), (m < length es)%nat -> (length es <= S m)%nat ->
pairs_by key_of (skipn m es) None = [].
Proof.
intros es m H1 H2. rewrite (rk_skipn_cons es m rk_d H1). cbn [pairs_by].
rewrite skipn_all2 by exact H2. destruct (key_of (nth m es rk_d)); reflexivity.
Qed.

Lemma rk_rop_nil : forall (vf : ent -> option Z * Z), Rate.rate_of_pairs vf [] = (None, 0).
Proof. intros vf. reflexivity. Qed.

(* ========================= the scan's invariant (RtPgSeg.rs_scan_inv) ========================= *)
Lemma rk_inv_skip : forall (rec : pod_rec) (m : nat), rs_scan_inv rec m ->
(m < length (ents rec))%nat -> key_of (nth m (ents rec) rk_d) = None -> rs_scan_inv rec (S m).
Proof.
intros rec m (Hle & He) Hm Hk. split; [lia|].
rewrite He. rewrite (rk_pairs_skip (ents rec) m Hm Hk). reflexivity.
Qed.

Lemma rk_inv_run : forall (rec : pod_rec) (a m : nat), rs_scan_inv rec a ->
(a <= m)%nat -> (m <= length (ents rec))%nat ->
(forall q, (a <= q < m)%nat -> key_of (nth q (ents rec) rk_d) = None) ->
rs_scan_inv rec m.
Proof.
intros rec a m (Hle & He) Ham Hml Hq. split; [lia|].
rewrite He. rewrite (rk_pairs_run (ents rec) a m Ham Hml Hq). reflexivity.
Qed.

Lemma rk_inv_end : forall (rec : pod_rec) (m : nat), rs_scan_inv rec m ->
(length (ents rec) <= m)%nat -> rs_E0 rec = (None, 0).
Proof.
intros rec m (Hle & He) Hm. rewrite He, (rk_pairs_end (ents rec) m Hm). reflexivity.
Qed.

(* the entry at m is the last one, so it starts no pair however it reads *)
Lemma rk_inv_last : forall (rec : pod_rec) (a m : nat), rs_scan_inv rec a -> (a <= m)%nat ->
(m < length (ents rec))%nat -> (length (ents rec) <= S m)%nat ->
(forall q, (a <= q < m)%nat -> key_of (nth q (ents rec) rk_d) = None) ->
rs_E0 rec = (None, 0).
Proof.
intros rec a m Hinv Ham Hm Hs Hq.
pose proof (rk_inv_run rec a m Hinv Ham ltac:(lia) Hq) as (_ & He).
rewrite He, (rk_pairs_last (ents rec) m Hm Hs). reflexivity.
Qed.

(* the entry at m is a key and the entry at m + 1 is its value: the form the key-match cut carries *)
Lemma rk_inv_key : forall (rec : pod_rec) (a m : nat) (kb : list byte), rs_scan_inv rec a ->
(a <= m)%nat -> (S m < length (ents rec))%nat ->
(forall q, (a <= q < m)%nat -> key_of (nth q (ents rec) rk_d) = None) ->
key_of (nth m (ents rec) rk_d) = Some kb ->
rs_E0 rec = Rate.rate_of_pairs Rate.expect_value
 ((kb, nth (S m) (ents rec) rk_d) :: pairs_by key_of (skipn (S (S m)) (ents rec)) None).
Proof.
intros rec a m kb Hinv Ham Hm Hq Hk.
pose proof (rk_inv_run rec a m Hinv Ham ltac:(lia) Hq) as (_ & He).
rewrite He, (rk_pairs_key (ents rec) m kb Hm Hk). reflexivity.
Qed.

(* the invariant at the scan's start *)
Lemma rk_inv_start : forall (rec : pod_rec), is_props rec = true -> params_struct rec = true ->
rs_scan_inv rec 0.
Proof.
intros rec Hi Hp. split; [lia|].
unfold rs_E0, Rate.expect_model, pairs. rewrite Hi, Hp. cbn [orb negb skipn]. reflexivity.
Qed.

(* ========================= the two early answers the set-up's tests give ========================= *)
Lemma rk_expect_not_props : forall (rec : pod_rec), is_props rec = false -> rs_E0 rec = (None, -1).
Proof. intros rec H. unfold rs_E0, Rate.expect_model. rewrite H. reflexivity. Qed.

Lemma rk_expect_no_struct : forall (rec : pod_rec), is_props rec = true -> params_struct rec = false ->
rs_E0 rec = (None, 0).
Proof. intros rec Hi Hp. unfold rs_E0, Rate.expect_model. rewrite Hi, Hp. reflexivity. Qed.

(* ========================= the parse's answer ========================= *)
(* with the NULL flag *)
Lemma rk_parse_null : forall (bs : list byte), Rate.harness_parse true bs = (None, -1).
Proof. intros bs. reflexivity. Qed.
(* on an uncorrupted record, without it: the scan's answer *)
Lemma rk_parse_expect : forall (rec : pod_rec), pod_rec_wf rec -> corrupt rec = false ->
Rate.harness_parse false (buf rec) = rs_E0 rec.
Proof.
intros rec Hw Hc. unfold Rate.harness_parse, rs_E0. cbv beta iota.
unfold buf, corrupt in *. destruct (p_corr rec); [discriminate Hc|].
apply Rate.parse_model_encode. exact Hw.
Qed.
(* both answers have the shape of Rate.answer_ok: a write exactly on rc 1, else rc 0 or -1 *)
Lemma rk_parse_shape : forall (null : bool) (bs : list byte), Rate.answer_ok (Rate.harness_parse null bs).
Proof.
intros null bs. unfold Rate.harness_parse. destruct null; [exact (or_intror eq_refl)|].
apply Rate.parse_model_shape.
Qed.
Lemma rk_expect_shape : forall (rec : pod_rec), Rate.answer_ok (rs_E0 rec).
Proof. intros rec. apply Rate.expect_model_shape. Qed.

(* ========================= the record the build left ========================= *)
Lemma rk_wf : forall (inp : list byte), pod_rec_wf (fst (pod_build inp)).
Proof.
intros inp. destruct (pod_build inp) as [r rest] eqn:E. cbn [fst].
exact (pod_build_wf inp r rest E).
Qed.
Lemma rk_nent_le : forall (rec : pod_rec), pod_rec_wf rec -> (length (ents rec) <= 32)%nat.
Proof. intros rec H. exact (proj1 (ents_wf rec H)). Qed.
Lemma rk_ents_wf : forall (rec : pod_rec), pod_rec_wf rec -> Forall ent_wf (ents rec).
Proof. intros rec H. exact (proj2 (ents_wf rec H)). Qed.
Lemma rk_ent_wf_nth : forall (rec : pod_rec) (m : nat), pod_rec_wf rec -> (m < length (ents rec))%nat ->
ent_wf (nth m (ents rec) rk_d).
Proof.
intros rec m Hw Hm. pose proof (rk_ents_wf rec Hw) as HF.
rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hm.
Qed.

Print Assumptions rk_inv_key.
Print Assumptions rk_parse_expect.
Print Assumptions rk_parse_shape.
