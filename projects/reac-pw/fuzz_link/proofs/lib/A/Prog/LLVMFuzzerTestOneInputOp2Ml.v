(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   the byte-list algebra of the inlined `remember` (+0x1178 .. +0x11f0) over the model block: the
   model after `sw n + 1, MD_N_MARK` and snprintf of the name t into slot n (o2l_mbs2), its count, requests, marks
   and well-formedness; the slots the loop's strcmp reads; link_spec.v's `remember` on the model's marks.
   Ported from the plain walk's lib/Prog/Slot/LC2RemLib.v sections 2, 5 and 6, which are pure list
   lemmas over link_spec; the plain file is not importable on image A.
   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
Import ListNotations.
Local Open Scope Z_scope.

Ltac o2l_lia :=
  unfold MD_N_MARK, MD_MARK, MARK_LEN, MD_SIZE, MD_N_REQ, MD_REQ, MD_REQ_LEN, NL_SENT_LEN, NL_SENT_MAX,
         MD_NEXT, MD_SOCKET_ERRNO, MD_SEND_ERRNO, MARKS_MAX in *; lia.

Lemma o2l_nth_firstn : forall {A} (l : list A) n i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros A l. induction l as [|x l IH]; intros n i H.
  - destruct n, i; reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma o2l_nth_skipn : forall {A} (l : list A) k i, nth_error (skipn k l) i = nth_error l (k + i).
Proof.
  intros A l. induction l as [|x l IH]; intros k i.
  - destruct k, i; reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn. apply IH.
Qed.

Lemma o2l_ext : forall {A} (l1 l2 : list A), (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros [|b l2] H.
  - reflexivity.
  - specialize (H O). cbn in H. discriminate H.
  - specialize (H O). cbn in H. discriminate H.
  - pose proof (H O) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

Lemma o2l_firstn_S : forall {A} (l : list A) p d, (p < length l)%nat -> firstn (S p) l = firstn p l ++ [nth p l d].
Proof.
  intros A l. induction l as [|x l IH]; intros p d H; cbn [length] in H; [lia|].
  destruct p as [|p]; [reflexivity|]. cbn [firstn nth]. rewrite (IH p d) by lia. reflexivity.
Qed.

Lemma o2l_nth_upd : forall (cs T : list byte) k i, (k + length T <= length cs)%nat ->
  nth_error (upd_bytes cs k T) i =
    if (Nat.leb k i && Nat.ltb i (k + length T))%bool then nth_error T (i - k) else nth_error cs i.
Proof.
  intros cs T k i H. destruct (Nat.ltb_spec i (length cs)) as [Hi|Hi].
  - apply upd_bytes_nth; assumption.
  - rewrite (proj2 (nth_error_None (upd_bytes cs k T) i)) by (rewrite upd_bytes_length; lia).
    destruct (Nat.leb_spec k i); destruct (Nat.ltb_spec i (k + length T)); cbn [andb]; try (exfalso; lia).
    all: symmetry; apply nth_error_None; lia.
Qed.

Lemma o2l_nth_slice : forall (c : list byte) off n i,
  nth_error (slice c off n) i = if Nat.ltb i (Z.to_nat n) then nth_error c (Z.to_nat off + i) else None.
Proof.
  intros c off n i. unfold slice. destruct (Nat.ltb_spec i (Z.to_nat n)) as [H|H].
  - rewrite o2l_nth_firstn by exact H. apply o2l_nth_skipn.
  - apply nth_error_None. rewrite length_firstn. lia.
Qed.

Lemma o2l_slice_out : forall (cs T : list byte) X off len,
  0 <= X -> 0 <= off -> 0 <= len -> (Z.to_nat X + length T <= length cs)%nat ->
  off + len <= X \/ X + Z.of_nat (length T) <= off ->
  slice (upd_bytes cs (Z.to_nat X) T) off len = slice cs off len.
Proof.
  intros cs T X off len HX Ho Hl HL Hd. apply o2l_ext. intros i. rewrite !o2l_nth_slice.
  destruct (Nat.ltb_spec i (Z.to_nat len)) as [Hi|Hi]; [|reflexivity].
  rewrite o2l_nth_upd by exact HL.
  destruct (Nat.leb_spec (Z.to_nat X) (Z.to_nat off + i));
    destruct (Nat.ltb_spec (Z.to_nat off + i) (Z.to_nat X + length T)); cbn [andb]; try reflexivity.
  exfalso. lia.
Qed.

Lemma o2l_slice_in : forall (cs T : list byte) X len, 0 <= X -> Z.of_nat (length T) = len ->
  (Z.to_nat X + length T <= length cs)%nat -> slice (upd_bytes cs (Z.to_nat X) T) X len = T.
Proof.
  intros cs T X len HX HT HL. apply o2l_ext. intros i. rewrite o2l_nth_slice.
  replace (Z.to_nat len) with (length T) by lia.
  destruct (Nat.ltb_spec i (length T)) as [Hi|Hi].
  - rewrite o2l_nth_upd by exact HL.
    destruct (Nat.leb_spec (Z.to_nat X) (Z.to_nat X + i));
      destruct (Nat.ltb_spec (Z.to_nat X + i) (Z.to_nat X + length T)); cbn [andb]; try (exfalso; lia).
    f_equal. lia.
  - symmetry. apply nth_error_None. lia.
Qed.

Lemma o2l_slice_pre : forall (cs T : list byte) X len j, 0 <= X -> (Z.to_nat X + length T <= length cs)%nat ->
  (j < length T)%nat -> (j < Z.to_nat len)%nat ->
  nth_error (slice (upd_bytes cs (Z.to_nat X) T) X len) j = nth_error T j.
Proof.
  intros cs T X len j HX HL Hj Hjl. rewrite o2l_nth_slice.
  destruct (Nat.ltb_spec j (Z.to_nat len)); [|exfalso; lia].
  rewrite o2l_nth_upd by exact HL.
  destruct (Nat.leb_spec (Z.to_nat X) (Z.to_nat X + j));
    destruct (Nat.ltb_spec (Z.to_nat X + j) (Z.to_nat X + length T)); cbn [andb]; try (exfalso; lia).
  f_equal. lia.
Qed.

Lemma o2l_firstn_slice : forall (l : list byte) off len k, (k <= Z.to_nat len)%nat ->
  firstn k (skipn (Z.to_nat off) l) = firstn k (slice l off len).
Proof. intros l off len k H. unfold slice. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma o2l_zb0 : forall b : byte, bz b = 0 -> b = zb 0.
Proof. intros b H. apply bv_eq. unfold bz in H. rewrite H. reflexivity. Qed.

Lemma o2l_nul_nth : forall (l : list byte) d, (nul_at l < length l)%nat -> bz (nth (nul_at l) l d) = 0.
Proof.
  induction l as [|x l IH]; intros d H; cbn [length] in H; [cbn [nul_at] in H; lia|].
  revert H. cbn [nul_at]. destruct (bz x =? 0) eqn:E; intros H; cbn [nth].
  - apply Z.eqb_eq. exact E.
  - apply IH. lia.
Qed.

Lemma o2l_nul_at_eq : forall (l : list byte) p,
  (forall j, (j < p)%nat -> exists b, nth_error l j = Some b /\ bz b <> 0) ->
  (exists b, nth_error l p = Some b /\ bz b = 0) -> nul_at l = p.
Proof.
  induction l as [|x l IH]; intros p H1 (b & Hb & Hb0).
  - destruct p; cbn in Hb; discriminate Hb.
  - destruct p as [|p].
    + cbn [nth_error] in Hb. injection Hb as ->. cbn [nul_at]. rewrite (proj2 (Z.eqb_eq _ _) Hb0). reflexivity.
    + destruct (H1 O ltac:(lia)) as (b0 & Hx & Hx0). cbn [nth_error] in Hx. injection Hx as ->.
      cbn [nul_at]. rewrite (proj2 (Z.eqb_neq _ _) Hx0). f_equal. apply IH.
      * intros j Hj. exact (H1 (S j) ltac:(lia)).
      * exists b. split; [exact Hb | exact Hb0].
Qed.

Lemma o2l_cstr_eq : forall (l t : list byte), (forall j, (j < length t)%nat -> nth_error l j = nth_error t j) ->
  (forall b, In b t -> bz b <> 0) -> (exists b, nth_error l (length t) = Some b /\ bz b = 0) ->
  nul_at l = length t /\ cstr l = t.
Proof.
  intros l t H1 H2 H3.
  assert (Hn : nul_at l = length t).
  { apply o2l_nul_at_eq; [|exact H3].
    intros j Hj. rewrite H1 by exact Hj. destruct (nth_error t j) as [b|] eqn:E.
    - exists b. split; [reflexivity|]. apply H2. exact (nth_error_In t j E).
    - exfalso. apply nth_error_None in E. lia. }
  split; [exact Hn|]. unfold cstr. rewrite Hn. apply o2l_ext. intros j.
  destruct (Nat.ltb_spec j (length t)) as [Hj|Hj].
  - rewrite o2l_nth_firstn by exact Hj. apply H1. exact Hj.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite length_firstn; lia). symmetry. apply nth_error_None. lia.
Qed.

Definition o2l_D (n : Z) : Z := MD_MARK + MARK_LEN * n.
Definition o2l_mbs1 (mbs : list byte) (n : Z) : list byte :=
  upd_bytes mbs (Z.to_nat MD_N_MARK) (le4 (Z_to_bv 64 (n + 1))).
Definition o2l_mbs2 (mbs : list byte) (n : Z) (t : list byte) : list byte :=
  upd_bytes (o2l_mbs1 mbs n) (Z.to_nat (o2l_D n)) (t ++ [zb 0]).

(* the count word the append stores *)
Definition o2l_cnt (n : Z) : list byte := le4 (Z_to_bv 64 (n + 1)).
Lemma o2l_cnt_len : forall n, length (o2l_cnt n) = 4%nat.
Proof. intros n. apply length_le4. Qed.
Lemma o2l_mbs1_cnt : forall mbs n, o2l_mbs1 mbs n = upd_bytes mbs (Z.to_nat MD_N_MARK) (o2l_cnt n).
Proof. reflexivity. Qed.

Lemma o2l_len1 : forall mbs n, Z.of_nat (length mbs) = MD_SIZE -> length (o2l_mbs1 mbs n) = length mbs.
Proof. intros mbs n HL. unfold o2l_mbs1. apply upd_bytes_length. rewrite length_le4. o2l_lia. Qed.

Lemma o2l_lenT : forall t : list byte, length (t ++ [zb 0]) = S (length t).
Proof. intros t. rewrite length_app. cbn [length]. lia. Qed.

Lemma o2l_len2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  length (o2l_mbs2 mbs n t) = length mbs.
Proof.
  intros mbs n t HL Hn Ht. unfold o2l_mbs2. rewrite upd_bytes_length; [apply o2l_len1; exact HL|].
  rewrite o2l_len1 by exact HL. rewrite o2l_lenT. unfold o2l_D. o2l_lia.
Qed.

Lemma o2l_slice2 : forall mbs n t off len, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  0 <= off -> 0 <= len -> off + len <= MD_N_MARK ->
  (off + len <= o2l_D n \/ o2l_D n + Z.of_nat (length t) + 1 <= off) ->
  slice (o2l_mbs2 mbs n t) off len = slice mbs off len.
Proof.
  intros mbs n t off len HL Hn Ht Ho Hl H1 H2. unfold o2l_mbs2.
  pose proof (o2l_len1 mbs n HL) as L1. pose proof (o2l_lenT t) as LT.
  rewrite o2l_slice_out by (rewrite ?L1, ?LT; unfold o2l_D in *; o2l_lia).
  unfold o2l_mbs1. apply o2l_slice_out; [o2l_lia | exact Ho | exact Hl | rewrite length_le4; o2l_lia | left; exact H1].
Qed.

Lemma o2l_fld32 : forall mbs n t off, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  0 <= off -> off + 4 <= MD_MARK -> fld_u32 (o2l_mbs2 mbs n t) off = fld_u32 mbs off.
Proof.
  intros mbs n t off HL Hn Ht Ho H. unfold fld_u32, link_spec.rdn.
  rewrite o2l_slice2 by (first [assumption | unfold o2l_D; o2l_lia]). reflexivity.
Qed.

Lemma o2l_nmark2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  md_n_mark (o2l_mbs2 mbs n t) = n + 1.
Proof.
  intros mbs n t HL Hn Ht. unfold md_n_mark, fld_u32, link_spec.rdn, o2l_mbs2.
  pose proof (o2l_len1 mbs n HL) as L1. pose proof (o2l_lenT t) as LT.
  rewrite (o2l_slice_out (o2l_mbs1 mbs n) (t ++ [zb 0]) (o2l_D n) MD_N_MARK 4)
    by (rewrite ?L1, ?LT; unfold o2l_D in *; o2l_lia).
  unfold o2l_mbs1.
  rewrite (o2l_slice_in mbs (le4 (Z_to_bv 64 (n + 1))) MD_N_MARK 4)
    by (first [rewrite length_le4; reflexivity | rewrite length_le4; o2l_lia | o2l_lia]).
  rewrite bytes_le_to_Z_le4, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (n + 1) (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma o2l_reqs2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  model_wf mbs -> md_reqs (o2l_mbs2 mbs n t) = md_reqs mbs.
Proof.
  intros mbs n t HL Hn Ht (Hr & _ & _ & _ & Hrl & _).
  assert (En : md_n_req (o2l_mbs2 mbs n t) = md_n_req mbs)
    by (unfold md_n_req; apply o2l_fld32; first [assumption | o2l_lia]).
  unfold md_reqs. rewrite En. apply map_ext_in. intros i Hi. apply in_seq in Hi. cbv beta.
  assert (Hi' : 0 <= Z.of_nat i < md_n_req mbs) by lia.
  pose proof (Hrl (Z.of_nat i) Hi') as Hli.
  unfold md_req_one.
  assert (El : fld_u64 (o2l_mbs2 mbs n t) (MD_REQ_LEN + 8 * Z.of_nat i) = fld_u64 mbs (MD_REQ_LEN + 8 * Z.of_nat i)).
  { unfold fld_u64, link_spec.rdn. rewrite o2l_slice2 by (first [assumption | unfold o2l_D; o2l_lia]). reflexivity. }
  rewrite El. apply o2l_slice2; first [assumption | unfold o2l_D; o2l_lia].
Qed.

Lemma o2l_slotk2 : forall mbs n t j, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  0 <= j < n -> slice (o2l_mbs2 mbs n t) (MD_MARK + MARK_LEN * j) MARK_LEN = slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN.
Proof. intros mbs n t j HL Hn Ht Hj. apply o2l_slice2; first [assumption | unfold o2l_D; o2l_lia]. Qed.

Lemma o2l_slotn2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  ~ In (zb 0) t ->
  nul_at (slice (o2l_mbs2 mbs n t) (o2l_D n) MARK_LEN) = length t /\
  cstr (slice (o2l_mbs2 mbs n t) (o2l_D n) MARK_LEN) = t.
Proof.
  intros mbs n t HL Hn Ht H0.
  pose proof (o2l_len1 mbs n HL) as L1. pose proof (o2l_lenT t) as LT.
  apply o2l_cstr_eq.
  - intros j Hj. unfold o2l_mbs2.
    rewrite o2l_slice_pre; [ | unfold o2l_D; o2l_lia | rewrite L1, LT; unfold o2l_D; o2l_lia
                             | rewrite LT; lia | unfold MARK_LEN; lia].
    rewrite nth_error_app1 by exact Hj. reflexivity.
  - intros b Hb Hb0. apply H0. replace (zb 0) with b; [exact Hb|]. apply o2l_zb0. exact Hb0.
  - exists (zb 0). split; [|reflexivity]. unfold o2l_mbs2.
    rewrite o2l_slice_pre; [ | unfold o2l_D; o2l_lia | rewrite L1, LT; unfold o2l_D; o2l_lia
                             | rewrite LT; lia | unfold MARK_LEN; lia].
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma o2l_marks2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> n = md_n_mark mbs -> 0 <= n < 32 ->
  (length t <= 11)%nat -> ~ In (zb 0) t -> md_marks (o2l_mbs2 mbs n t) = md_marks mbs ++ [t].
Proof.
  intros mbs n t HL En Hn Ht H0. unfold md_marks.
  rewrite (o2l_nmark2 mbs n t HL Hn Ht). rewrite <- En.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia. rewrite seq_S, map_app. cbn [map]. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi. cbv beta. f_equal.
    apply o2l_slotk2; try assumption. lia.
  - f_equal.
    lazymatch goal with |- cstr (slice _ ?o _) = _ =>
      replace o with (o2l_D n) by (unfold o2l_D, MD_MARK, MARK_LEN; lia) end.
    exact (proj2 (o2l_slotn2 mbs n t HL Hn Ht H0)).
Qed.

Lemma o2l_wf2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> n = md_n_mark mbs -> 0 <= n < 32 ->
  (length t <= 11)%nat -> ~ In (zb 0) t -> model_wf mbs -> model_wf (o2l_mbs2 mbs n t).
Proof.
  intros mbs n t HL En Hn Ht H0 (Hr & Hx & Hs1 & Hs2 & Hrl & (Hm & Hst)).
  assert (F : forall off, 0 <= off -> off + 4 <= MD_MARK -> fld_u32 (o2l_mbs2 mbs n t) off = fld_u32 mbs off)
    by (intros off Ho Hof; apply o2l_fld32; assumption).
  assert (Er : md_n_req (o2l_mbs2 mbs n t) = md_n_req mbs) by (unfold md_n_req; apply F; o2l_lia).
  split; [rewrite Er; exact Hr|].
  split; [unfold md_next; rewrite F by o2l_lia; exact Hx|].
  split; [unfold md_socket_errno; rewrite F by o2l_lia; exact Hs1|].
  split; [unfold md_send_errno; rewrite F by o2l_lia; exact Hs2|].
  split.
  - intros i Hi. rewrite Er in Hi.
    unfold fld_u64, link_spec.rdn. rewrite o2l_slice2 by (first [assumption | unfold o2l_D; o2l_lia]).
    exact (Hrl i Hi).
  - unfold model_marks_wf. rewrite (o2l_nmark2 mbs n t HL Hn Ht). split; [unfold MARKS_MAX; lia|].
    intros i Hi. destruct (Z.eq_dec i n) as [->|Hne].
    + fold (o2l_D n). rewrite (proj1 (o2l_slotn2 mbs n t HL Hn Ht H0)). unfold MARK_LEN. lia.
    + rewrite o2l_slotk2 by (first [assumption | lia]). apply Hst. lia.
Qed.



Definition o2l_slot (mbs : list byte) (j : Z) : list byte := cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN).



Lemma o2l_marks_map : forall mbs, md_marks mbs = map (fun i => o2l_slot mbs (Z.of_nat i)) (seq 0 (Z.to_nat (md_n_mark mbs))).
Proof. reflexivity. Qed.

Lemma o2l_rem_in : forall mbs t, 0 <= md_n_mark mbs -> (exists j, 0 <= j < md_n_mark mbs /\ o2l_slot mbs j = t) ->
  remember (md_marks mbs) t = md_marks mbs.
Proof.
  intros mbs t H0 (j & Hj & Ej). unfold remember.
  replace (existsb (fun x => bl_eqb x t) (md_marks mbs)) with true; [reflexivity|].
  symmetry. apply existsb_exists. exists (o2l_slot mbs j). split.
  - rewrite o2l_marks_map. apply in_map_iff. exists (Z.to_nat j). rewrite Z2Nat.id by lia. split; [reflexivity|].
    apply in_seq. lia.
  - apply bl_eqb_iff. exact Ej.
Qed.

Lemma o2l_rem_full : forall mbs t, md_n_mark mbs = 32 -> remember (md_marks mbs) t = md_marks mbs.
Proof.
  intros mbs t H. unfold remember. destruct (existsb (fun x => bl_eqb x t) (md_marks mbs)); [reflexivity|].
  rewrite o2l_marks_map, length_map, length_seq, H. reflexivity.
Qed.

Lemma o2l_rem_new : forall mbs t, 0 <= md_n_mark mbs < 32 -> (length t <= 15)%nat ->
  (forall j, 0 <= j < md_n_mark mbs -> o2l_slot mbs j <> t) ->
  remember (md_marks mbs) t = md_marks mbs ++ [t].
Proof.
  intros mbs t Hn Ht NF. unfold remember.
  replace (existsb (fun x => bl_eqb x t) (md_marks mbs)) with false.
  - rewrite o2l_marks_map, length_map, length_seq.
    replace (Z.of_nat (Z.to_nat (md_n_mark mbs)) <? MARKS_MAX) with true by (symmetry; apply Z.ltb_lt; unfold MARKS_MAX; lia).
    rewrite firstn_all2 by exact Ht. reflexivity.
  - symmetry. apply Bool.not_true_iff_false. intro H. apply existsb_exists in H. destruct H as (x & Hin & Hx).
    rewrite o2l_marks_map in Hin. apply in_map_iff in Hin. destruct Hin as (i & <- & Hi). apply in_seq in Hi.
    apply bl_eqb_iff in Hx. apply (NF (Z.of_nat i)); [lia | exact Hx].
Qed.

