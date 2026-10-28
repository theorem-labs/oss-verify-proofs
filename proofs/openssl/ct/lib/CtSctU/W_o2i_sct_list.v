(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_get_object_walk W_c2i_ibuf W_c2i_int W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import W_crypto_realloc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_free W_sct_list_free SctRep W_sct_new W_sct_leaves W_memdup W_sct_set1_signature W_sk_leaves W_sk_new W_realloc_array W_sk_push SctStmt W_o2i_sig W_o2i_sct O2iKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.


(* [comment removed for export] *)
Ltac post_call_esp2 ESP m :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; rewrite ?ESP in PO; unfold STACK_SIZE in PO; revert ms' PO; post_call ctusegs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma perm_by_members : forall (L L' : list block),
  List.NoDup (map blk_id L) -> List.NoDup (map blk_id L') -> (forall b, In b L <-> In b L') -> Permutation L L'.
Proof. intros L L' N1 N2 H. apply Permutation.NoDup_Permutation; [eapply List.NoDup_map_inv; exact N1| eapply List.NoDup_map_inv; exact N2| exact H]. Qed.

Lemma NoDup_remove_sct : forall x L, List.NoDup (map blk_id L) -> List.NoDup (map blk_id (remove_sct x L)).
Proof. intros x L ND. unfold remove_sct. apply (NoDup_lremove (Some (sc_blk x, 0))). do 4 apply NoDup_lremove. exact ND. Qed.
Lemma NoDup_remove_scts : forall l L, List.NoDup (map blk_id L) -> List.NoDup (map blk_id (remove_scts l L)).
Proof. induction l as [|x t IH]; intros L ND; cbn [remove_scts]; [exact ND|]. apply IH. apply NoDup_remove_sct. exact ND. Qed.

(* [comment removed for export] *)
Lemma remove_sct_out : forall adr x L b, List.NoDup (map blk_id L) -> In b (remove_sct x L) -> ~ In (blk_id b) (map blk_id (sct_blocks adr x)).
Proof.
  intros adr x L b ND H Hin. unfold remove_sct in H. unfold sct_blocks in Hin. rewrite !map_app, !in_app_iff in Hin. cbn [map oblk blk_id fst snd app] in Hin.
  assert (R1 : forall q L0, In b (lb_remove q L0) -> blk_id b <> q /\ In b L0).
  { intros q L0 Hq. apply lb_remove_In in Hq. destruct Hq as [H1 H2]. split; [exact H2| exact H1]. }
  assert (R2 : forall od L0, In b (lremove od L0) -> (match od with Some (q, _) => blk_id b <> q | None => True end) /\ In b L0).
  { intros [[q n]|] L0 Hq; cbn [lremove] in Hq; [apply R1 in Hq; exact Hq| split; [exact I| exact Hq]]. }
  apply R1 in H. destruct H as [N5 H]. apply R2 in H. destruct H as [N4 H]. apply R2 in H. destruct H as [N3 H]. apply R2 in H. destruct H as [N2 H]. apply R2 in H. destruct H as [N1 H].
  destruct Hin as [Hin|[Hin|[Hin|[Hin|Hin]]]].
  - destruct (sc_logid x) as [l|]; cbn in Hin, N1; [| exact Hin]. destruct Hin as [E0|[]]. exact (N1 (eq_sym E0)).
  - destruct (sc_ext x) as [[e en]|]; cbn in Hin, N2; [| exact Hin]. destruct Hin as [E0|[]]. exact (N2 (eq_sym E0)).
  - destruct (sc_sig x) as [[g gn]|]; cbn in Hin, N3; [| exact Hin]. destruct Hin as [E0|[]]. exact (N3 (eq_sym E0)).
  - destruct (sc_blob x) as [[bb bn]|]; cbn in Hin, N4; [| exact Hin]. destruct Hin as [E0|[]]. exact (N4 (eq_sym E0)).
  - cbn in Hin. destruct Hin as [E0|[]]. exact (N5 (eq_sym E0)).
Qed.

Lemma remove_scts_out : forall adr l L b, List.NoDup (map blk_id L) -> In b (remove_scts l L) -> ~ In (blk_id b) (map blk_id (scts_blocks adr l)).
Proof.
  induction l as [|x t IH]; intros L b ND H; [intros []|]. cbn [scts_blocks]. rewrite map_app, in_app_iff.
  change (In b (remove_scts t (remove_sct x L))) in H. intros [Hin|Hin].
  - apply remove_scts_incl in H. exact (remove_sct_out adr x L b ND H Hin).
  - exact (IH (remove_sct x L) b (NoDup_remove_sct x L ND) H Hin).
Qed.

Lemma scts_blocks_in : forall adr l x b, In x l -> In b (sct_blocks adr x) -> In b (scts_blocks adr l).
Proof.
  intros adr l x b Hx Hb. induction l as [|y t IH]; [destruct Hx|]. cbn. rewrite in_app_iff. destruct Hx as [->|Hx]; [left; exact Hb| right; exact (IH Hx)].
Qed.

(* [comment removed for export] *)
Lemma remove_sk_perm : forall adr (k : skr bptr) (OWX NEW LB : list block),
  Permutation NEW (sk_blocks adr k) -> List.NoDup (map blk_id (OWX ++ NEW ++ LB)) ->
  Permutation (lb_remove (sk_blk k) (lremove (sk_data k) (remove_scts (sk_items k) (OWX ++ NEW ++ LB)))) (OWX ++ LB).
Proof.
  intros adr k OWX NEW LB PM ND.
  assert (NDR : List.NoDup (map blk_id (lb_remove (sk_blk k) (lremove (sk_data k) (remove_scts (sk_items k) (OWX ++ NEW ++ LB)))))).
  { apply (NoDup_lremove (Some (sk_blk k, 0))). apply NoDup_lremove. apply NoDup_remove_scts. exact ND. }
  assert (NDO : List.NoDup (map blk_id (OWX ++ LB))).
  { rewrite (map_app blk_id OWX), (map_app blk_id NEW LB) in ND. rewrite map_app. exact (NoDup_app_remove_l _ _ _ ND). }
  apply perm_by_members; [exact NDR| exact NDO|].
  pose proof ND as ND0. rewrite (map_app blk_id OWX), (map_app blk_id NEW LB) in ND0.
  pose proof (NoDup_app_split _ _ ND0) as (N23 & D1 & N1). pose proof (NoDup_app_split _ _ N23) as (N3 & D2 & N2).
  assert (IDS : forall b, In b (sk_blocks adr k) -> In (blk_id b) (map blk_id NEW)).
  { intros b Hb. apply in_map. eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]. }
  intros b. split.
  - intros H. pose proof H as H0. apply lb_remove_In in H. destruct H as [H Nb]. 
    assert (Nd : match sk_data k with Some (q, _) => blk_id b <> q | None => True end /\ In b (remove_scts (sk_items k) (OWX ++ NEW ++ LB))).
    { destruct (sk_data k) as [[q n]|]; cbn [lremove] in H; [apply lb_remove_In in H; destruct H as [H Hq]; split; [exact Hq| exact H]| split; [exact I| exact H]]. }
    destruct Nd as [Nd H1].
    pose proof (remove_scts_out adr (sk_items k) _ b ND H1) as Ns. apply remove_scts_incl in H1.
    rewrite !in_app_iff in H1. destruct H1 as [H1|[H1|H1]]; [apply in_app_iff; left; exact H1| | apply in_app_iff; right; exact H1].
    exfalso. pose proof (Permutation_in _ PM H1) as Hs. unfold sk_blocks in Hs. rewrite !in_app_iff in Hs. destruct Hs as [Hs|[Hs|Hs]].
    + apply Ns. apply in_map. exact Hs.
    + destruct (sk_data k) as [[q n]|]; cbn in Hs; [| exact Hs]. destruct Hs as [E0|[]]. apply Nd. rewrite <- E0. reflexivity.
    + destruct Hs as [E0|[]]. apply Nb. rewrite <- E0. reflexivity.
  - intros H. rewrite in_app_iff in H.
    assert (NIN : ~ In (blk_id b) (map blk_id (sk_blocks adr k))).
    { intros Hin. apply in_map_iff in Hin. destruct Hin as (b' & Eb & Hb'). pose proof (IDS b' Hb') as Hn. rewrite Eb in Hn.
      destruct H as [H|H]; [apply (D1 _ (in_map _ _ _ H)); apply in_app_iff; left; exact Hn| exact (D2 _ Hn (in_map _ _ _ H))]. }
    unfold sk_blocks in NIN. rewrite !map_app, !in_app_iff in NIN. cbn [map blk_id fst snd] in NIN.
    apply in_lb_remove_other; [| intros E0; apply NIN; right; right; left; symmetry; exact E0].
    apply in_lremove_other; [| destruct (sk_data k) as [[q n]|]; [intros E0; apply NIN; right; left; cbn; left; symmetry; exact E0| exact I]].
    apply (in_remove_scts_keep adr); [| intros Hin; apply NIN; left; exact Hin].
    rewrite !in_app_iff. destruct H as [H|H]; [left; exact H| right; right; exact H].
Qed.

Lemma lb_remove_perm : forall q (L L' : list block), Permutation L L' -> Permutation (lb_remove q L) (lb_remove q L').
Proof.
  intros q L L' HP. induction HP as [|b L L' HP IH|b b' L|L L' L'' H1 IH1 H2 IH2].
  - apply Permutation_refl.
  - rewrite !lb_remove_cons. destruct (bptr_eqb (blk_id b) q); [exact IH| apply perm_skip; exact IH].
  - rewrite !lb_remove_cons. destruct (bptr_eqb (blk_id b) q), (bptr_eqb (blk_id b') q); try apply Permutation_refl. apply perm_swap.
  - eapply Permutation_trans; [exact IH1| exact IH2].
Qed.
Lemma lremove_perm : forall od (L L' : list block), Permutation L L' -> Permutation (lremove od L) (lremove od L').
Proof. intros [[q n]|] L L' HP; cbn [lremove]; [apply lb_remove_perm; exact HP| exact HP]. Qed.

Lemma scts_blocks_app : forall adr l1 l2, scts_blocks adr (l1 ++ l2) = scts_blocks adr l1 ++ scts_blocks adr l2.
Proof. intros adr l1 l2. induction l1 as [|x t IH]; cbn; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma sct_blocks_ids : forall adr x, map blk_id (sct_blocks adr x) = sct_ids x.
Proof.
  intros adr x. unfold sct_blocks, sct_ids. rewrite !map_app.
  destruct (sc_logid x) as [l|]; destruct (sc_ext x) as [[e en]|]; destruct (sc_sig x) as [[g gn]|]; destruct (sc_blob x) as [[b bn]|]; reflexivity.
Qed.

Lemma sct_blocks_ext : forall (adr1 adr2 : bptr -> Z) x, (forall q, In q (sct_ids x) -> adr2 q = adr1 q) -> sct_blocks adr2 x = sct_blocks adr1 x.
Proof.
  intros adr1 adr2 x H. unfold sct_blocks. unfold sct_ids in H.
  assert (E5 : adr2 (sc_blk x) = adr1 (sc_blk x)) by (apply H; rewrite !in_app_iff; right; right; right; right; left; reflexivity).
  rewrite E5.
  destruct (sc_logid x) as [l|]; destruct (sc_ext x) as [[e en]|]; destruct (sc_sig x) as [[g gn]|]; destruct (sc_blob x) as [[b bn]|]; cbn [osz32 option_map oblk fst app] in *;
    rewrite ?(H l), ?(H e), ?(H g), ?(H b) by (cbn; rewrite ?in_app_iff; cbn; tauto); reflexivity.
Qed.

Lemma sct_cells_ext : forall (adr1 adr2 : bptr -> Z) x et vs, (forall q, In q (sct_ids x) -> adr2 q = adr1 q) -> sct_cells adr2 x et vs = sct_cells adr1 x et vs.
Proof.
  intros adr1 adr2 x et vs H. unfold sct_cells. unfold sct_ids in H.
  destruct (sc_logid x) as [l|]; destruct (sc_ext x) as [[e en]|]; destruct (sc_sig x) as [[g gn]|]; destruct (sc_blob x) as [[b bn]|]; cbn [osz32 option_map optr fst app] in *;
    rewrite ?(H l), ?(H e), ?(H g), ?(H b) by (cbn; rewrite ?in_app_iff; cbn; tauto); reflexivity.
Qed.

Lemma scts_blocks_ext : forall (adr1 adr2 : bptr -> Z) l,
  (forall x q, In x l -> In q (sct_ids x) -> adr2 q = adr1 q) -> scts_blocks adr2 l = scts_blocks adr1 l.
Proof.
  intros adr1 adr2 l H. induction l as [|x t IH]; cbn; [reflexivity|].
  rewrite (sct_blocks_ext adr1 adr2 x) by (intros q Hq; apply (H x q); [left; reflexivity| exact Hq]). rewrite IH; [reflexivity|].
  intros y q Hy Hq. apply (H y q); [right; exact Hy| exact Hq].
Qed.

(* [comment removed for export] *)
Lemma sct_blocks_adr : forall adr x q A n, In (q, A, n) (sct_blocks adr x) -> A = adr q.
Proof.
  intros adr x q A n H. unfold sct_blocks in H. rewrite !in_app_iff in H.
  destruct H as [H|[H|[H|[H|H]]]].
  - destruct (sc_logid x) as [l|]; cbn in H; [| destruct H]. destruct H as [E0|[]]. injection E0; intros; subst; reflexivity.
  - destruct (sc_ext x) as [[e en]|]; cbn in H; [| destruct H]. destruct H as [E0|[]]. injection E0; intros; subst; reflexivity.
  - destruct (sc_sig x) as [[g gn]|]; cbn in H; [| destruct H]. destruct H as [E0|[]]. injection E0; intros; subst; reflexivity.
  - destruct (sc_blob x) as [[b bn]|]; cbn in H; [| destruct H]. destruct H as [E0|[]]. injection E0; intros; subst; reflexivity.
  - destruct H as [E0|[]]. injection E0; intros; subst; reflexivity.
Qed.
Lemma scts_blocks_adr : forall adr l q A n, In (q, A, n) (scts_blocks adr l) -> A = adr q.
Proof. intros adr l q A n H. induction l as [|x t IH]; [destruct H|]. cbn in H. apply in_app_iff in H. destruct H as [H|H]; [exact (sct_blocks_adr _ _ _ _ _ H)| exact (IH H)]. Qed.
Lemma sk_blocks_adr : forall adr k q A n, In (q, A, n) (sk_blocks adr k) -> A = adr q.
Proof.
  intros adr k q A n H. unfold sk_blocks in H. rewrite !in_app_iff in H. destruct H as [H|[H|H]].
  - exact (scts_blocks_adr _ _ _ _ _ H).
  - destruct (sk_data k) as [[d na]|]; cbn in H; [| destruct H]. destruct H as [E0|[]]. injection E0; intros; subst; reflexivity.
  - destruct H as [E0|[]]. injection E0; intros; subst; reflexivity.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma rs_of_state : forall st m OW E bo, ap_state st m OW E bo -> realloc_statics m.
Proof. intros st m OW E bo (_ & _ & (_ & RS & _) & _). exact RS. Qed.

Lemma sct_rep_ext : forall (adr1 adr2 : bptr -> Z) mA L x, (forall q, In q (sct_ids x) -> adr2 q = adr1 q) -> sct_rep mA L adr1 x -> sct_rep mA L adr2 x.
Proof.
  intros adr1 adr2 mA L x H (H1 & H2 & H3 & H4 & H5 & H6 & H7 & REST).
  assert (H' : forall q, In q (oid (sc_logid x)) \/ In q (oid (option_map fst (sc_ext x))) \/ In q (oid (option_map fst (sc_sig x))) \/ In q (oid (option_map fst (sc_blob x))) \/ sc_blk x = q ->
               adr2 q = adr1 q).
  { intros q Hq. apply H. unfold sct_ids. rewrite !in_app_iff. cbn [In]. tauto. }
  assert (E5 : adr2 (sc_blk x) = adr1 (sc_blk x)) by (apply H'; right; right; right; right; reflexivity).
  assert (AR : forall o, (forall q n, o = Some (q, n) -> adr2 q = adr1 q) -> arr_rep mA L adr1 o -> arr_rep mA L adr2 o).
  { intros [[q n]|] Ho Hr; cbn in *; [| exact I]. rewrite (Ho q n eq_refl). exact Hr. }
  split; [rewrite E5; exact H1|]. split; [rewrite E5, (sct_cells_ext adr1 adr2 x) by exact H; exact H2|].
  split; [apply AR; [intros q n Ho; apply H'; left; unfold osz32 in Ho; destruct (sc_logid x); cbn in Ho |- *; [injection Ho; intros; subst; left; reflexivity| discriminate]| exact H3]|].
  split; [apply AR; [intros q n Ho; apply H'; right; left; rewrite Ho; left; reflexivity| exact H4]|].
  split; [apply AR; [intros q n Ho; apply H'; right; right; left; rewrite Ho; left; reflexivity| exact H5]|].
  split; [apply AR; [intros q n Ho; apply H'; right; right; right; left; rewrite Ho; left; reflexivity| exact H6]|].
  split; [rewrite (sct_blocks_ext adr1 adr2 x) by exact H; exact H7| exact REST].
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HR : rrealloc_stmt.

  (* [comment removed for export] *)
  Lemma arr_rep_agreeP : forall P mA mB L adr1 o,
    agree_on P mA mB -> (forall q n a, o = Some (q, n) -> adr1 q <= a < adr1 q + n -> P a) -> arr_rep mA L adr1 o -> arr_rep mB L adr1 o.
  Proof.
    intros P mA mB L adr1 [[q n]|] AG HP H; cbn in *; [| exact I]. destruct H as (Hn & HL & bs & HC). split; [exact Hn|]. split; [exact HL|]. exists bs.
    eapply rw_cells_agree; [exact AG| exact HC|]. intros a Ha. cbn in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. eapply HP; [reflexivity| lia].
  Qed.

  Lemma sct_rep_agreeP : forall P mA mB L adr1 x,
    agree_on P mA mB -> (forall q Aq n a, In (q, Aq, n) (sct_blocks adr1 x) -> Aq <= a < Aq + n -> P a) -> sct_rep mA L adr1 x -> sct_rep mB L adr1 x.
  Proof.
    intros P mA mB L adr1 x AG HP (H1 & H2 & H3 & H4 & H5 & H6 & REST).
    assert (HB : forall q Aq n a, In (q, Aq, n) (oblk adr1 (osz32 (sc_logid x))) \/ In (q, Aq, n) (oblk adr1 (sc_ext x)) \/ In (q, Aq, n) (oblk adr1 (sc_sig x)) \/ In (q, Aq, n) (oblk adr1 (sc_blob x))
                                \/ (q, Aq, n) = (sc_blk x, adr1 (sc_blk x), SCT_SIZE) -> Aq <= a < Aq + n -> P a).
    { intros q Aq n a Hq Ha. eapply HP; [| exact Ha]. unfold sct_blocks. rewrite !in_app_iff. cbn [In]. destruct Hq as [Hq|[Hq|[Hq|[Hq| ->]]]]; tauto. }
    split; [exact H1|]. split.
    { eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. rewrite sct_cells_size in Ha. eapply (HB (sc_blk x) (adr1 (sc_blk x)) SCT_SIZE); [right; right; right; right; reflexivity| lia]. }
    split; [eapply arr_rep_agreeP; [exact AG| intros q n a Ho Ha; eapply (HB q (adr1 q) n); [left; unfold osz32 in *; rewrite Ho; left; reflexivity| exact Ha]| exact H3]|].
    split; [eapply arr_rep_agreeP; [exact AG| intros q n a Ho Ha; eapply (HB q (adr1 q) n); [right; left; rewrite Ho; left; reflexivity| exact Ha]| exact H4]|].
    split; [eapply arr_rep_agreeP; [exact AG| intros q n a Ho Ha; eapply (HB q (adr1 q) n); [right; right; left; rewrite Ho; left; reflexivity| exact Ha]| exact H5]|].
    split; [eapply arr_rep_agreeP; [exact AG| intros q n a Ho Ha; eapply (HB q (adr1 q) n); [right; right; right; left; rewrite Ho; left; reflexivity| exact Ha]| exact H6]|].
    exact REST.
  Qed.

  Lemma sk_rep_agreeP : forall P mA mB L adr1 k,
    agree_on P mA mB -> (forall q Aq n a, In (q, Aq, n) (sk_blocks adr1 k) -> Aq <= a < Aq + n -> P a) -> sk_rep mA L adr1 k -> sk_rep mB L adr1 k.
  Proof.
    intros P mA mB L adr1 k AG HP (HIN & (sorted & SR & HC) & HD & HFA & ND).
    split; [exact HIN|]. split.
    { exists sorted. split; [exact SR|]. eapply rw_cells_agree; [exact AG| exact HC|]. intros a Ha. rewrite sk_cells_size in Ha.
      eapply (HP (sk_blk k) (adr1 (sk_blk k)) STACK_SIZE); [unfold sk_blocks; rewrite !in_app_iff; right; right; left; reflexivity| lia]. }
    split. { destruct (sk_data k) as [[q na]|] eqn:ED; [| exact HD]. destruct HD as (HI & Hn & Hna & jb & JB & HB). split; [exact HI|]. split; [exact Hn|]. split; [exact Hna|]. exists jb. split; [exact JB|].
             eapply rw_cells_agree; [exact AG| exact HB|]. intros a Ha. rewrite data_block_size in Ha. unfold sk_num in *.
             eapply (HP q (adr1 q) (8 * na)); [unfold sk_blocks; rewrite ED, !in_app_iff; right; left; left; reflexivity| lia]. }
    split; [| exact ND]. apply Forall_forall. intros x Hx. eapply sct_rep_agreeP; [exact AG| | exact (proj1 (Forall_forall _ _) HFA x Hx)].
    intros q Aq n a Hq Ha. eapply HP; [| exact Ha]. unfold sk_blocks. rewrite !in_app_iff. left. eapply scts_blocks_in; [exact Hx| exact Hq].
  Qed.

  Lemma sct_rep_mono : forall mA L L' adr1 x, (forall b, In b (sct_blocks adr1 x) -> In b L') -> sct_rep mA L adr1 x -> sct_rep mA L' adr1 x.
  Proof.
    intros mA L L' adr1 x HL (H1 & H2 & H3 & H4 & H5 & H6 & REST).
    assert (AR : forall o, (forall q n, o = Some (q, n) -> In (q, adr1 q, n) L') -> arr_rep mA L adr1 o -> arr_rep mA L' adr1 o).
    { intros [[q n]|] Ho H; cbn in *; [| exact I]. destruct H as (Hn & _ & R). split; [exact Hn|]. split; [apply Ho; reflexivity| exact R]. }
    split; [apply HL; unfold sct_blocks; rewrite !in_app_iff; right; right; right; right; left; reflexivity|]. split; [exact H2|].
    split; [apply AR; [intros q n Ho; apply HL; unfold sct_blocks; unfold osz32 in *; rewrite Ho; left; reflexivity| exact H3]|].
    split; [apply AR; [intros q n Ho; apply HL; unfold sct_blocks; rewrite Ho, !in_app_iff; right; left; left; reflexivity| exact H4]|].
    split; [apply AR; [intros q n Ho; apply HL; unfold sct_blocks; rewrite Ho, !in_app_iff; right; right; left; left; reflexivity| exact H5]|].
    split; [apply AR; [intros q n Ho; apply HL; unfold sct_blocks; rewrite Ho, !in_app_iff; right; right; right; left; left; reflexivity| exact H6]|].
    exact REST.
  Qed.

  Lemma sk_rep_mono : forall mA L L' adr1 k, (forall b, In b (sk_blocks adr1 k) -> In b L') -> sk_rep mA L adr1 k -> sk_rep mA L' adr1 k.
  Proof.
    intros mA L L' adr1 k HL (HIN & HS & HD & HFA & ND).
    split; [apply HL; unfold sk_blocks; rewrite !in_app_iff; right; right; left; reflexivity|]. split; [exact HS|].
    split. { destruct (sk_data k) as [[q na]|] eqn:ED; [| exact HD]. destruct HD as (HI & REST). split; [| exact REST]. apply HL. unfold sk_blocks. rewrite ED, !in_app_iff. right. left. left. reflexivity. }
    split; [| exact ND]. apply Forall_forall. intros x Hx. eapply sct_rep_mono; [| exact (proj1 (Forall_forall _ _) HFA x Hx)].
    intros b Hb. apply HL. unfold sk_blocks. rewrite !in_app_iff. left. eapply scts_blocks_in; [exact Hx| exact Hb].
  Qed.


  Section Act.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (errv canary : word) (K : list block).
  Variables (adr : bptr -> Z) (c : list Z) (D len PIN : Z).
  Hypothesis PRE : ap_pre s st m OW LB E bo sp lo B errv canary O2I_SCT_LIST_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis FRM : frm0 fc.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis ELEN : len = zlength c.
  Hypothesis D0 : 0 <= D.
  Hypothesis D63 : D + zlength c < 2 ^ 63.
  Hypothesis DF : Forall (fun b => 0 <= b < 256) c.
  Hypothesis HB0 : bytes_at ctusegs m D (to_bytes c).
  Hypothesis PBX : c = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz.
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.
  Hypothesis PINlo : bv_unsigned sp <= PIN.
  Hypothesis PINhi : PIN + 8 <= B.
  Hypothesis PIN8 : PIN mod 8 = 0.
  Hypothesis HPIN : rw_cells ctusegs m PIN [C8 (wz D)].

  (* [comment removed for export] *)
  Definition STK : Z := O2I_SCT_STACK.
  Lemma CEIL : alloc_ceiling <= lo. Proof using PRE. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma GLO : 3493888 <= lo. Proof using PRE. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). unfold GLOBALS_TOP in H. exact H. Qed.
  Lemma LO : lo <= bv_unsigned sp + -96 - STK. Proof using PRE PIN. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). unfold O2I_SCT_LIST_STACK in H. unfold STK. lia. Qed.
  Lemma STK0 : 0 <= STK. Proof. unfold STK, O2I_SCT_STACK, O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK. lia. Qed.
  Lemma OFS0 : -96 <= 0. Proof. lia. Qed.
  Lemma OFS16 : -96 mod 16 = 0. Proof. reflexivity. Qed.
  Lemma SPB : bv_unsigned sp <= B. Proof using PRE. destruct PRE as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma B63 : B < 2 ^ 63. Proof using PRE. destruct PRE as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma SP16 : bv_unsigned sp mod 16 = 0. Proof using PRE. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
  Lemma SPR : 0 <= bv_unsigned sp < 2 ^ 64. Proof. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn in H. exact H. Qed.
  Lemma DLEN : Z.of_nat (length (to_bytes c)) = zlength c. Proof. apply zlength_to_bytes. Qed.
  Lemma NDL : List.NoDup (map blk_id (OW ++ LB)). Proof using PRE. destruct PRE as (HEAP & _). exact (LH_nodup _ _ _ HEAP). Qed.

  Local Notation oinvL := (oinv sp m s LB E lo B canary K c D PIN (-96) STK).
  Local Notation KFACTS := (oinv_facts sp m s LB E lo B canary K c D PIN (-96) STK).
  Local Notation KMUNCH := (oinv_munch sp m s LB E lo B canary K c D PIN (-96) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 PINlo PINhi PBX).
  Local Notation KHEAP := (oinv_heap sp m s LB E lo B canary K c D PIN (-96) STK CEIL GLO LO STK0 OFS0 SPB B63 PBX).
  Local Notation KALLOC := (oinv_alloc sp m s LB E lo B canary K c D PIN (-96) STK CEIL GLO LO STK0 OFS0 SPB B63 PBX).
  Local Notation KCALL := (oinv_call sp m s LB E lo B canary K c D PIN (-96) STK GLO LO STK0 OFS0 SPB B63).
  Local Notation KAFTER := (oinv_after sp m s LB E lo B canary K c D PIN (-96) STK CEIL GLO LO STK0 OFS0 SPB B63 OFS16 PINlo PBX).
  Local Notation KPERM := (oinv_perm sp m s LB E lo B canary K c D PIN (-96) STK).
  Local Notation KRESP := (pre_resp sp E lo B canary c (-96) STK LO STK0 OFS0 SPB SP16).
  Local Notation SPOST := (o2i_list_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr PIN) (only parsing).

  Local Ltac ctx := pose proof CEIL as CEIL; pose proof GLO as GLO; pose proof LO as LO; pose proof STK0 as STK0; pose proof SPB as SPB; pose proof B63 as B63;
                    pose proof SP16 as SP16; pose proof SPR as SPR; pose proof DLEN as DLEN; pose proof (ESP sp lo B (-96) STK GLO LO STK0 OFS0 SPB B63) as ESP;
                    unfold STK, O2I_SCT_STACK, O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK in LO.

  (* [comment removed for export] *)
  Definition lframe : list cell := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition site_ok (base : Z) (nj : nat) (tl : Z) (rs : rsite) : Prop :=
    (base = 0x19ce4c /\ nj = 6%nat /\ tl = 0x19cfa0 /\ rs = RS_list_len) \/ (base = 0x19cf88 /\ nj = 5%nat /\ tl = 0x19cfa0 /\ rs = RS_list_mismatch)
    \/ (base = 0x19cff4 /\ nj = 6%nat /\ tl = 0x19d040 /\ rs = RS_list_lt2) \/ (base = 0x19d028 /\ nj = 5%nat /\ tl = 0x19d040 /\ rs = RS_list_sctlen).

  Definition raise_post (pc : Z) (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 : word) (mX : mem) (NEW : list block) (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) bo',
      ms' = MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6)
               F' (Z_to_bv 64 pc) fc' None m' (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
      /\ oinvL s' (snd r) m' OW' errv' bo' NEW
      /\ lx_pres (NEW ++ LB) (bv_unsigned sp + -96) LIBW_AP mX m'.

  Lemma raise_gen : forall base nj tl rs (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (FX : bvmap 5 word) (fcX : bv 32) sX stX mX OWX errvX boX NEW,
    site_ok base nj tl rs -> oinvL sX stX mX OWX errvX boX NEW -> frm0 fcX -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FX k = reg_get F k) ->
    implM ctusegs (interp (ap_embed (err_raise rs stX))) sX (raise_post (tl + 20) x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 mX NEW)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 base) fcX None mX (seg_rom ctusegs)).
  Proof using HF HM PBX PINlo PRE.
    intros until NEW. intros SITE OI FRMX FEX. ctx.
    pose proof OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    destruct (lit_ok_auto A_CT_OCT_C 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_ok_auto A_O2I_SCT_LIST 13 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    assert (RSF : rs_flen rs = 19) by (destruct SITE as [(_ & _ & _ & ->)|[(_ & _ & _ & ->)|[(_ & _ & _ & ->)|(_ & _ & _ & ->)]]]; reflexivity).
    assert (RSN : rs_fnlen rs = 13) by (destruct SITE as [(_ & _ & _ & ->)|[(_ & _ & _ & ->)|[(_ & _ & _ & ->)|(_ & _ & _ & ->)]]]; reflexivity).
    rewrite <- RSF in LF. rewrite <- RSN in LN.
    unfold err_raise.
    (* [comment removed for export] *)
    assert (TAIL : forall (r1 : unit * ap_st bptr) (sA : PState) (q1 q5 q6 q7 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (F1 : bvmap 5 word) (fc1 : bv 32) mA OW1 (errv1 : word),
      (tl = 0x19cfa0 \/ tl = 0x19d040) ->
      frm0 fc1 -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get F k) ->
      oinvL sA (snd r1) mA OW1 errv1 boX NEW -> lx_pres (NEW ++ LB) (bv_unsigned sp + -96) LIBW_AP mX mA ->
      implM ctusegs (interp (ap_embed (abind (err_set_debug rs) (fun _ => err_set_error rs) (snd r1)))) sA (raise_post (tl + 20) x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 mX NEW)
        (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) q5 q6 q7 x8 x9 (wz A_CT_OCT_C) (wz (rs_line rs)) (wz A_O2I_SCT_LIST) q13 q14 q15 q16 q17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 q28 q29 q30 q31)
            F1 (Z_to_bv 64 tl) fc1 None mA (seg_rom ctusegs))).
    { intros until errv1. intros HTL FRM1 FE1 OIa LXa.
      pose proof OIa as (PREa & _ & KOa & KIa & _).
      destruct HTL as [-> | ->];
        (unfold implM; iprefix; step; ihere; to_implM;
         eapply implM_abind;
         [ pose proof (ERR_set_debug_walk HM HF rs A_CT_OCT_C A_O2I_SCT_LIST boX _ _ _ _ LF LN) as W; unfold ap_stmt in W;
           eapply W; [eapply ap_pre_stack_le; [exact PREa| unfold ERR_SET_DEBUG_STACK, STK, O2I_SCT_STACK, O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK; lia]| reflexivity| exact FRM1| repeat split; reflexivity| exact KOa| exact KIa]
         | intros r2 sB ms2 PO2; cbv beta in PO2;
           destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & errv2 & bo2
                            & -> & FRM2 & FE2 & PREb & LXb & SOb & FAb & BKb & EBO2); subst bo2; rewrite ESP in LXb;
           lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end;
           assert (OIb : oinvL sB (snd r2) mB OW2 errv2 boX NEW) by
             (eapply (KAFTER _ _ _ _ _ _ NEW sB (snd r2) mB OW2 errv2 boX [] []); [exact OIa| exact PREb| exact LXb| intros a []| exact SOb| exact FAb| exact BKb]);
           pose proof OIb as (PREb' & _ & KOb & KIb & _);
           unfold implM; iprefix; do 3 step; step; ihere; to_implM;
           eapply implM_mono;
           [ pose proof (ERR_set_error_walk rs 50 105 boX) as W; unfold ap_stmt in W;
             eapply W; [eapply ap_pre_stack_le; [exact PREb'| unfold STK, O2I_SCT_STACK, O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK; lia]| reflexivity| exact FRM2| | exact KOb| exact KIb];
             cbn; unfold ERR_LIB_SYS, MallocRep.wz; repeat split; try reflexivity; try lia;
             destruct SITE as [(_ & _ & _ & ->)|[(_ & _ & _ & ->)|[(_ & _ & _ & ->)|(_ & _ & _ & ->)]]]; reflexivity
           | intros r3 sC ms3 PO3; cbv beta in PO3;
             destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & errv3 & bo3
                              & -> & FRM3 & FE3 & PREc & LXc & SOc & FAc & BKc & EBO3); subst bo3; rewrite ESP in LXc;
             lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end;
             assert (OIc : oinvL sC (snd r3) mC OW3 errv3 boX NEW) by
               (eapply (KAFTER _ _ _ _ _ _ NEW sC (snd r3) mC OW3 errv3 boX [] []); [exact OIb| exact PREc| exact LXc| intros a []| exact SOc| exact FAc| exact BKc]);
             unfold raise_post; exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, errv3, boX;
             split; [reflexivity|]; split; [exact FRM3|]; split; [intros k Hk; rewrite (FE3 k Hk), (FE2 k Hk); apply (FE1 k Hk)|];
             split; [exact OIc|];
             eapply lx_pres_trans; [exact LXa|]; eapply lx_pres_trans; [exact LXb| exact LXc] ] ]). }
    (* [comment removed for export] *)
    destruct SITE as [(-> & -> & -> & ->)|[(-> & -> & -> & ->)|[(-> & -> & -> & ->)|(-> & -> & -> & ->)]]];
      (unfold implM; iprefix; step; ihere; to_implM;
       eapply implM_abind;
       [ pose proof (ERR_new_walk HF boX) as W; unfold ap_stmt in W;
         eapply W; [eapply ap_pre_stack_le; [exact PREX| unfold ERR_NEW_STACK, STK, O2I_SCT_STACK, O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK; lia]| reflexivity| exact FRMX| reflexivity| exact KO| exact KI]
       | intros r1 sA ms1 PO1; cbv beta in PO1;
         destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1 & bo1
                          & -> & FRM1 & FE1 & PREa & LXa & SOa & FAa & BKa & EBO1); subst bo1; rewrite ESP in LXa;
         lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end;
         assert (OIa : oinvL sA (snd r1) mA OW1 errv1 boX NEW) by
           (eapply (KAFTER _ _ _ _ _ _ NEW sA (snd r1) mA OW1 errv1 boX [] []); [exact OI| exact PREa| exact LXa| intros a []| exact SOa| exact FAa| exact BKa]);
         unfold implM; iprefix ]).
    - do 6 step. ihere. to_implM. eapply TAIL; [left; reflexivity| exact FRM1| intros k Hk; rewrite (FE1 k Hk); apply (FEX k Hk)| exact OIa| exact LXa].
    - do 5 step. ihere. to_implM. eapply TAIL; [left; reflexivity| exact FRM1| intros k Hk; rewrite (FE1 k Hk); apply (FEX k Hk)| exact OIa| exact LXa].
    - do 6 step. ihere. to_implM. eapply TAIL; [right; reflexivity| exact FRM1| intros k Hk; rewrite (FE1 k Hk); apply (FEX k Hk)| exact OIa| exact LXa].
    - do 5 step. ihere. to_implM. eapply TAIL; [right; reflexivity| exact FRM1| intros k Hk; rewrite (FE1 k Hk); apply (FEX k Hk)| exact OIa| exact LXa].
  Qed.

  (* [comment removed for export] *)
  Lemma sk_blocks_client : forall sX stX mX OWX errvX boX NEW adr1 k q Aq n a,
    oinvL sX stX mX OWX errvX boX NEW -> Permutation NEW (sk_blocks adr1 k) -> In (q, Aq, n) (sk_blocks adr1 k) -> Aq <= a < Aq + n ->
    lx_client (NEW ++ LB) (bv_unsigned sp + -96) LIBW_AP a.
  Proof using PRE PIN8 PINlo.
    intros until a. intros OI PM Hq Ha. ctx. pose proof (KFACTS _ _ _ _ _ _ _ OI) as (_ & _ & BND & _).
    assert (HN : In (q, Aq, n) NEW) by (eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hq]).
    pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HN)) as (B1 & B2 & B3 & B4 & B5).
    split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|]. right. left. exists (q, Aq, n). split; [apply in_app_iff; left; exact HN| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sk_rep_munch : forall sX stX mX OWX errvX boX NEW adrk k L mY W,
    oinvL sX stX mX OWX errvX boX NEW -> Permutation NEW (sk_blocks adrk k) ->
    sk_rep mX L adrk k -> munch W mX mY -> wmono ctusegs mX mY -> Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> sk_rep mY L adrk k.
  Proof.
    intros until W. intros OI PM SK MU WM HW. pose proof (KFACTS _ _ _ _ _ _ _ OI) as (_ & _ & BND & _).
    eapply sk_rep_agreeP; [apply (agree_on_of_munch _ _ _ MU WM)| | exact SK].
    intros q Aq n a Hq Ha. cbn beta.
    assert (HN : In (q, Aq, n) NEW) by (eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hq]).
    pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HN)) as (B1 & B2 & B3 & B4 & B5).
    apply seg_outside. eapply Forall_impl; [| exact HW]. intros [x y] Hx. cbn in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ret_null : forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 pv : word) (FX : bvmap 5 word) (fcX : bv 32)
      sX stX mX OWX errvX boX,
    oinvL sX stX mX OWX errvX boX [] -> frm0 fcX -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FX k = reg_get F k) ->
    rw_cells ctusegs mX (bv_unsigned sp + -96) lframe -> rw_cells ctusegs mX PIN [C8 pv] ->
    evt ctusegs (fun ms'' => o2i_list_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr PIN (None, stX) sX ms'')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 0x19cfb4) fcX None mX (seg_rom ctusegs)).
  Proof using PRE.
    intros until boX. intros OI FRMX FEX FR HP. ctx.
    pose proof (KFACTS _ _ _ _ _ _ _ OI) as (HEAPX & NDX & _).
    pose proof (KCALL _ _ _ _ _ _ _ OI) as (_ & _ & _ & STX & _ & _ & ERRX & MI & _).
    pose proof OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    unfold lframe in FR. unfold MallocRep.wz.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    step. step. do 12 step. release_frame FR STX (bv_unsigned sp). step. step.
    apply evt_done. unfold o2i_list_post. cbn [fst snd].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FX, fcX, mX, OWX, errvX, boX, adr, [], pv.
    split; [reflexivity|]. split; [exact FRMX|]. split; [exact FEX|].
    split; [eapply KRESP; [exact PREX| exact STX]|].
    split; [exact LX|]. split; [exact SO|]. split; [exact FA|].
    split; [split; [exact KO| split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP]]|].
    split; [intros b Hb; reflexivity|]. split; [intros b []|]. split; [exact HP|]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ret_some : forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 pv : word) (FX : bvmap 5 word) (fcX : bv 32)
      sX stX mX OWX errvX boX NEW (adrk : bptr -> Z) (k : skr bptr),
    oinvL sX stX mX OWX errvX boX NEW -> frm0 fcX -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FX k = reg_get F k) ->
    Permutation NEW (sk_blocks adrk k) -> sk_rep mX (OWX ++ NEW ++ LB) adrk k -> (forall b, In b LB -> adrk (blk_id b) = adr (blk_id b)) ->
    rw_cells ctusegs mX (bv_unsigned sp + -96) lframe -> rw_cells ctusegs mX PIN [C8 pv] ->
    evt ctusegs (fun ms'' => o2i_list_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr PIN (Some k, stX) sX ms'')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (wz (adrk (sk_blk k))) x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 0x19cfb8) fcX None mX (seg_rom ctusegs)).
  Proof using PRE.
    intros until k. intros OI FRMX FEX PM SK ADRK FR HP. ctx.
    pose proof (KFACTS _ _ _ _ _ _ _ OI) as (HEAPX & NDX & _ & FRESH & _).
    pose proof (KCALL _ _ _ _ _ _ _ OI) as (_ & _ & _ & STX & _ & _ & ERRX & MI & _).
    pose proof OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    unfold lframe in FR. unfold MallocRep.wz.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    step. do 12 step. release_frame FR STX (bv_unsigned sp). step. step.
    apply evt_done. unfold o2i_list_post. cbn [fst snd].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FX, fcX, mX, OWX, errvX, boX, adrk, NEW, pv.
    split; [reflexivity|]. split; [exact FRMX|]. split; [exact FEX|].
    split; [eapply KRESP; [exact PREX| exact STX]|].
    split; [exact LX|]. split; [exact SO|]. split; [exact FA|].
    split; [split; [exact KO| split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP]]|].
    split; [exact ADRK|]. split; [intros [[q Aq] n] Hb; cbn; exact (FRESH q Aq n Hb)|]. split; [exact HP|]. split; [exact PM| exact SK].
  Qed.

  (* [comment removed for export] *)
  Lemma free_exit : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 pv : word) (FX : bvmap 5 word) (fcX : bv 32)
      sX stX mX OWX errvX boX NEW (adrk : bptr -> Z) (k : skr bptr),
    oinvL sX stX mX OWX errvX boX NEW -> frm0 fcX -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FX k = reg_get F k) ->
    Permutation NEW (sk_blocks adrk k) -> sk_rep mX (OWX ++ NEW ++ LB) adrk k ->
    rw_cells ctusegs mX (bv_unsigned sp + -96) lframe -> rw_cells ctusegs mX PIN [C8 pv] ->
    implM ctusegs (interp (ap_embed (abind (sk_free_all k) (fun _ => aret None) stX))) sX SPOST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) x5 x6 x7 x8 (wz 0) x10 x11 x12 x13 x14 x15 x16 x17 (wz (adrk (sk_blk k))) x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 0x19d054) fcX None mX (seg_rom ctusegs)).
  Proof using HF PBX PINlo PRE.
    intros until k. intros OI FRMX FEX PM SK FR HP. ctx.
    pose proof (KFACTS _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & _).
    pose proof (KCALL _ _ _ _ _ _ _ OI) as (_ & AUXX & SPBX & STX & _ & _ & ERRX & MI & CSX & ASX).
    pose proof OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    pose proof (sk_rep_free_view _ _ _ _ SK) as (STC & HIN & HDAT & DCS & PCS & HINS & NDK).
    pose proof SK as (_ & _ & HD3 & _).
    assert (N31 : zlength (sk_items k) < 2 ^ 31).
    { destruct (sk_data k) as [[q na]|]; [destruct HD3 as (_ & Hn & Hna & _); unfold sk_num in Hn; lia| rewrite HD3; unfold zlength; cbn; lia]. }
    unfold lframe in FR. unfold MallocRep.wz.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    unfold implM. iprefix.
    step. if_cases K9; zc K9; [| exfalso; apply K9; reflexivity]. clear K9.
    step. step. ihere. to_implM.
    rewrite ap_embed_sk_free_all.
    eapply (SCT_LIST_free_walk HF) with (L := OWX ++ NEW ++ LB) (lo := lo) (B := B) (adr := adrk) (sk := k);
      [exact HEAPX| exact AUXX| rewrite ESP; lia| rewrite ESP; exact STX| exact CEIL| unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold SCT_LIST_FREE_STACK, SK_POP_FREE_STACK, SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia
      | rewrite ESP; replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) by lia; rewrite Zminus_mod, SP16; reflexivity
      | exact ERRX| exact MI| reflexivity| exact CSX| exact (got_of_state _ _ _ _ _ ASX)
      | exact STC| exact HIN| | exact N31| exact DCS| exact PCS| exact HINS| | exact NDX| reflexivity|].
    { destruct (sk_data k) as [[q na]|]; [| exact HDAT]. destruct HDAT as [H1 H2]. split; [exact H1| unfold sk_num in H2; exact H2]. }
    { revert NDK. unfold sk_blocks. destruct (sk_data k) as [[q na]|]; cbn [dblk oblk]; rewrite !map_app; cbn [map blk_id fst snd app]; intros ND0; exact ND0. }
    intros sG msG PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (g0 & g1 & g2 & g10 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g3 & g4 & g5 & g6 & mG
                    & -> & MIG & STG & ERRG & AUXG & HPG & FAG & SOG & HEAPG).
    replace (ret_pc (Z_to_bv 64 0x19d06c)) with (Z_to_bv 64 0x19d06c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (remove_sk_perm adrk k OWX NEW LB PM NDX) as PMR.
    assert (OIG : oinvL sG stX mG OWX errvX boX []).
    { eapply (KHEAP _ _ _ _ _ _ NEW sG mG errvX _ _ []); [exact OI| exact HPG| | exact HEAPG| cbn [app]; exact PMR| exact MIG| exact STG| exact ERRG| exact AUXG| exact FAG| exact SOG].
      intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PMR|]. apply in_app_iff. exact Hb. }
    cbn [ap_embed aret interp]. apply implM_ret.
    pose proof (agree_of_heap_pres _ _ _ _ HPG) as AGG.
    apply (rw_cells_agree _ _ _ _ _ AGG) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGG) in HP; [| intros a Ha; left; cbn in Ha; lia].
    clear MU WM MI. rename MIG into MI. pose proof (munch_refl (@nil (Z * Z)) mG) as MU. pose proof (wmono_refl ctusegs mG) as WM.
    step.
    eapply ret_null; [exact OIG| exact FRMX| exact FEX| exact FR| exact HP].
  Qed.

  (* [comment removed for export] *)
  Definition linv (k : skr bptr) (pq ll : Z) (sX : PState) (stX : ap_st bptr) (mX : mem) (OWX : list block) (errvX : word) (boX : Z * Z)
      (NEW : list block) (adrk : bptr -> Z) : Prop :=
    oinvL sX stX mX OWX errvX boX NEW /\ NEW = sk_blocks adrk k /\ sk_rep mX (OWX ++ NEW ++ LB) adrk k
    /\ (forall b, In b LB -> adrk (blk_id b) = adr (blk_id b))
    /\ rw_cells ctusegs mX (bv_unsigned sp + -96) lframe /\ rw_cells ctusegs mX PIN [C8 (wz (D + pq))]
    /\ 2 <= pq /\ 0 <= ll /\ pq + ll <= zlength c /\ 3 * sk_num k + 2 <= pq.

  (* [comment removed for export] *)
  Lemma iter_body : forall (LOOPF : skr bptr -> Z -> Z -> AM (option (skr bptr))) (ll : Z)
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32)
      (k : skr bptr) (pq : Z) sX stX mX OWX errvX boX NEW adrk,
    (forall (k' : skr bptr) (pq' ll' : Z) (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y28 y29 y30 y31 : word) (FY : bvmap 5 word) (fcY : bv 32)
            sY stY mY OWY errvY boY NEW' adrk',
        linv k' pq' ll' sY stY mY OWY errvY boY NEW' adrk' -> ll' <= ll - 3 -> frm0 fcY -> (forall r : reg, bv_unsigned r <> 10 -> reg_get FY r = reg_get F r) ->
        implM ctusegs (interp (ap_embed (LOOPF k' pq' ll' stY))) sY SPOST
          (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) y5 y6 y7 y8 (wz 0) y10 y11 y12 y13 y14 y15 y16 y17 (wz (adrk' (sk_blk k'))) (wz PIN) y20 y21 y22 (wz ll') (wz 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3)) s11 y28 y29 y30 y31)
              FY (Z_to_bv 64 0x19cf14) fcY None mY (seg_rom ctusegs))) ->
    linv k pq ll sX stX mX OWX errvX boX NEW adrk -> 2 <= ll -> zlength c <= MAX_SCT_LIST_SIZE -> frm0 fcX -> (forall r : reg, bv_unsigned r <> 10 -> reg_get FX r = reg_get F r) ->
    implM ctusegs (interp (ap_embed ((let sct_len := u16be c pq in
                                      let p := pq + 2 in
                                      let ll2 := ll - 2 in
                                      if (sct_len =? 0) || (ll2 <? sct_len) then err_raise RS_list_sctlen ;;; sk_free_all k ;;; aret None
                                      else
                                        let ll3 := ll2 - sct_len in
                                        r <- o2i_sct c p sct_len ;;
                                        match r with
                                        | None => sk_free_all k ;;; aret None
                                        | Some sc => k' <- sk_push k sc ;; LOOPF k' (p + sct_len) ll3
                                        end) stX))) sX SPOST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) x5 x6 x7 x8 (wz 0) x10 x11 x12 x13 x14 x15 x16 x17 (wz (adrk (sk_blk k))) (wz PIN) x20 x21 x22 (wz ll) (wz 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3)) s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 0x19cf1c) fcX None mX (seg_rom ctusegs)).
  Proof using ADR D63 DF HF HM HR PBX PINhi PINlo PRE fc tp D0 PIN8.
    intros until adrk. intros IH LI L2 LENB FRMX FEX. ctx.
    destruct LI as (OI & ENEW & SK & ADRK & FR & HP & PQ2 & LL0 & PQL & NUMB).
    assert (PM : Permutation NEW (sk_blocks adrk k)) by (rewrite ENEW; apply Permutation_refl).
    pose proof (KFACTS _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & DJL & _).
    pose proof (KCALL _ _ _ _ _ _ _ OI) as (_ & _ & _ & STX & _ & _ & ERRX & MI & _).
    unfold LX_ERRNO, RATP in ERRX. change (3355176 - 164) with 3355012 in ERRX.
    pose proof OI as (_ & _ & _ & _ & _ & _ & _ & HB).
    destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)]; [exfalso; rewrite E0 in PQL; unfold zlength in PQL; cbn in PQL; lia|].
    pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HPB)) as (PB3 & _ & PB4 & PB5 & _).
    set (KA := adrk (sk_blk k)) in *.
    assert (HKIN : In (sk_blk k, KA, STACK_SIZE) (sk_blocks adrk k)) by (unfold sk_blocks; rewrite !in_app_iff; right; right; left; reflexivity).
    assert (HKN : In (sk_blk k, KA, STACK_SIZE) NEW) by (eapply Permutation_in; [apply Permutation_sym; exact PM| exact HKIN]).
    pose proof (BND (sk_blk k) KA STACK_SIZE ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HKN)) as (BK0 & _ & BKC & BKI & _). unfold STACK_SIZE in BKC, BKI.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range c i DF). lia. }
    pose proof (znth_range c pq DF) as R0. pose proof (znth_range c (pq + 1) DF) as R1.
    unfold lframe in FR. unfold MallocRep.wz in HP. unfold MallocRep.wz. cbv zeta.
    set (sl := u16be c pq). pose proof (u16be_range c pq) as SLR. fold sl in SLR.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (PIN, PIN + 8)]%Z mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step.
    step. if_cases KC1; zify_cond KC1; [exfalso; rewrite ?unsigned_lit in KC1 by lia; lia|]. clear KC1.
    step. if_cases KC2; zify_cond KC2; [exfalso; rewrite ?unsigned_lit in KC2 by lia; lia|]. clear KC2.
    step. if_cases KC3; zify_cond KC3; [exfalso; rewrite ?unsigned_lit in KC3 by lia; lia|]. clear KC3.
    pose proof (payload_read _ D c pq (wa (D + pq)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD. rewrite (zxb_lit (znth c pq)) by lia.
    pose proof (payload_read _ D c (pq + 1) (wa (D + pq + 1)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD. rewrite (zxb_lit (znth c (pq + 1))) by lia.
    step. step. step.
    setreg 20%Z (Z_to_bv 64 sl)
      ltac:(subst sl; unfold u16be; rewrite !BY by lia; f_equal;
            rewrite (unsigned_lit (znth c pq)), (unsigned_lit (znth c (pq + 1))) by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256;
            rewrite (unsigned_lit (znth c pq * 256)) by lia; symmetry; apply lor_shl8; lia).
    step. setreg 23%Z (Z_to_bv 64 (ll - 2)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    step. step. setreg 10%Z (Z_to_bv 64 (D + pq + 2)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve) || idtac.
    name_mem m1.
    assert (OI1 : oinvL sX stX m1 OWX errvX boX NEW).
    { eapply KMUNCH; [exact OI| exact MU| exact WM| exact MI| exact STX| exact ERRX|]. constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity| constructor]. }
    step. if_cases KS; zc KS.
    - (* [comment removed for export] *)
      replace ((sl =? 0) || (ll - 2 <? sl)) with true.
      2:{ symmetry. destruct (Z.eq_dec sl 0) as [->|NZ]; [reflexivity|]. rewrite land_ones64_small in KS by lia. apply orb_true_intro. right. apply Z.ltb_lt. lia. }
      ihere. to_implM.
      eapply implM_abind; [eapply (raise_gen 0x19d028 5%nat 0x19d040 RS_list_sctlen); [right; right; right; repeat split; reflexivity| exact OI1| exact FRMX| exact FEX]|].
      intros r sF msF RP. cbv beta. unfold raise_post in RP.
      destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & errvF & boF
                      & -> & FRMF & FEF & OIF & LXF).
      pose proof (agree_of_lx_pres _ _ _ _ _ LXF) as AGF.
      assert (CLs : forall a, bv_unsigned sp + -96 <= a -> lx_client (NEW ++ LB) (bv_unsigned sp + -96) LIBW_AP a).
      { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
      apply (rw_cells_agree _ _ _ _ _ AGF) in FR; [| intros a Ha; apply CLs; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGF) in HP; [| intros a Ha; apply CLs; cbn in Ha; lia].
      change (Z_to_bv 64 (1691712 + 20)) with (Z_to_bv 64 0x19d054).
      eapply (free_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (D + pq + 2)) FF fcF sF (snd r) mF OWF errvF boF NEW adrk k);
        [exact OIF| exact FRMF| exact FEF| exact PM| | exact FR| exact HP].
      eapply sk_rep_mono; [intros b Hb; apply in_app_iff; right; apply in_app_iff; left; eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]|].
      eapply (sk_rep_agreeP _ m1 mF); [exact AGF| intros q Aq n a Hq Ha; eapply (sk_blocks_client sX stX m1 OWX errvX boX NEW adrk k); [exact OI1| exact PM| exact Hq| exact Ha]|].
      eapply (sk_rep_munch sX stX mX); [exact OI| exact PM| exact SK| exact MU| exact WM|]. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor].
    - (* [comment removed for export] *)
      assert (SL1 : 1 <= sl <= ll - 2).
      { destruct (Z.eq_dec sl 0) as [E0|NZ]; [exfalso; rewrite E0 in KS; change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615 in KS; unfold MAX_SCT_LIST_SIZE in LENB; lia|].
        rewrite land_ones64_small in KS by lia. lia. }
      clear KS. replace ((sl =? 0) || (ll - 2 <? sl)) with false by (symmetry; apply orb_false_intro; [apply Z.eqb_neq| apply Z.ltb_ge]; lia).
      step. step. step. step. ihere. to_implM.
      pose proof OI1 as (PRE1 & LX1 & KO1 & KI1 & KP1 & SO1 & FA1 & HB1).
      pose proof (o2i_sct_walk HM HF) as W. unfold o2i_sct_spec in W.
      eapply implM_abind.
      { eapply W with (LB := NEW ++ LB) (K := K) (adr := adrk) (c := c) (D := D) (p := pq + 2) (len := sl) (PIN := PIN) (lo := lo) (B := B) (E := E) (bo := boX) (OW := OWX) (errv := errvX) (canary := canary); clear W.
        - exact PRE1.
        - reflexivity.
        - exact FRMX.
        - exact KO1.
        - exact KI1.
        - split; [exact HB1|]. split; [exact DF|]. split; [lia|]. split; [lia|]. split; [unfold MAX_SCT_LIST_SIZE in LENB; lia|].
          right. exists (pb, PA, psz). split; [apply in_app_iff; right; exact HPB| cbn; lia].
        - lia.
        - unfold MAX_SCT_SIZE. lia.
        - lia.
        - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| rewrite (ADRK b Hb); apply ADR; exact Hb].
          destruct b as [[q Aq] n]. cbn. symmetry. eapply (sk_blocks_adr adrk k). eapply Permutation_in; [exact PM| exact Hb].
        - lia.
        - lia.
        - exact PIN8.
        - replace (D + (pq + 2)) with (D + pq + 2) by lia. exact HP.
        - reflexivity.
        - reflexivity.
        - reflexivity. }
      clear W.
      intros r sO msO POST. unfold o2i_sct_post in POST. rewrite ?ESP in POST.
      destruct POST as (v0 & v1 & v2 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v3 & v4 & v5 & v6 & FS & fcS & mO & OWO & errvO & boO & adrO & NEWO
                        & -> & FRMS & FES & PREO & LXO & SOO & FAO & BKO & ADRO & FRO & RES).
      destruct r as [ox stO]. cbn [fst snd] in *.
      replace (ret_pc (Z_to_bv 64 0x19cf60)) with (Z_to_bv 64 0x19cf60) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (OIO : oinvL sO stO mO OWO errvO boO (NEWO ++ NEW)).
      { eapply (KAFTER sX stX m1 OWX errvX boX NEW sO stO mO OWO errvO boO [(PIN, PIN + 8)]%Z NEWO); [exact OI1| exact PREO| exact LXO| | exact SOO| exact FAO| exact BKO].
        intros a Ha. cbn [rin_ivs fst snd] in Ha. destruct Ha as [Ha|[]]. right. left. lia. }
      pose proof (agree_of_lx_pres _ _ _ _ _ LXO) as AGO.
      assert (CLo : forall a, bv_unsigned sp + -96 <= a < bv_unsigned sp -> lx_client (NEW ++ LB) (bv_unsigned sp + -96) ([(PIN, PIN + 8)]%Z ++ LIBW_AP) a).
      { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AGO) in FR; [| intros a Ha; apply CLo; cbn in Ha; lia].
      assert (SKO : sk_rep mO (OWO ++ (NEWO ++ NEW) ++ LB) adrk k).
      { eapply sk_rep_mono; [intros b Hb; apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]|].
        eapply (sk_rep_agreeP _ m1 mO); [exact AGO| |].
        - intros q Aq n a Hq Ha. pose proof (sk_blocks_client sX stX m1 OWX errvX boX NEW adrk k q Aq n a OI1 PM Hq Ha) as [C1 C2].
          split; [| exact C2]. intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| exact (C1 HIN)]. cbn [rin_ivs fst snd] in HIN.
          assert (HN : In (q, Aq, n) NEW) by (eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hq]).
          pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HN)). lia.
        - eapply (sk_rep_munch sX stX mX); [exact OI| exact PM| exact SK| exact MU| exact WM|]. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
      clear MU WM MI. pose proof (KCALL _ _ _ _ _ _ _ OIO) as (HEAPO & AUXO & SPBO & STO & _ & _ & ERRO & MI & CSO & ASO).
      unfold LX_ERRNO, RATP in ERRO. change (3355176 - 164) with 3355012 in ERRO.
      pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (PIN, PIN + 8)]%Z mO) as MU. pose proof (wmono_refl ctusegs mO) as WM.
      unfold MallocRep.wz in FRO.
      destruct ox as [x|].
      + (* [comment removed for export] *)
        destruct RES as (ENO & SRX & HPO & VERX). unfold MallocRep.wz in HPO.
        pose proof (KFACTS _ _ _ _ _ _ _ OIO) as (_ & NDO & BNDO & FRESHO & _).
        assert (HXB : In (sc_blk x, adrO (sc_blk x), SCT_SIZE) NEWO) by (rewrite ENO; unfold sct_blocks; rewrite !in_app_iff; right; right; right; right; left; reflexivity).
        pose proof (BNDO (sc_blk x) (adrO (sc_blk x)) SCT_SIZE ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; left; exact HXB)) as (AX0 & _ & AXC & AXI & _). unfold SCT_SIZE in AXC, AXI.
        set (AX := adrO (sc_blk x)) in *.
        (* [comment removed for export] *)
        pose proof SKO as (HKL & (sorted & SRT & HCK) & HDK & HFK & NDK). fold KA in HKL, HCK. rewrite sk_cells_raw in HCK.
        assert (HDW : exists Dd jb, Dd = optr adrk (sk_data k) /\
                  match sk_data k with
                  | Some (q, na) => In (q, Dd, 8 * na) (OWO ++ (NEWO ++ NEW) ++ LB) /\ q <> sk_blk k /\ sk_num k <= na /\ SK_MIN_NODES <= na < 2^23
                                    /\ rw_cells ctusegs mO Dd (map C8 (map (ptrw adrk) (sk_items k)) ++ [CB (length jb) jb]) /\ Z.of_nat (length jb) = 8 * (na - sk_num k)
                  | None => sk_items k = [] /\ Dd = 0 /\ jb = []
                  end).
        { destruct (sk_data k) as [[q na]|] eqn:EDK.
          - destruct HDK as (HI & Hn & Hna & jb & JB & HBK). exists (adrk q), jb. split; [reflexivity|]. split; [exact HI|]. split.
            { intros E0. unfold sk_blocks in NDK. rewrite ?EDK in NDK. rewrite !map_app in NDK. cbn [dblk map blk_id fst snd app] in NDK.
              destruct (NoDup_app_split _ _ NDK) as (N23 & _ & _). apply NoDup_cons_iff in N23. destruct N23 as [NN _]. apply NN. left. symmetry. exact E0. }
            split; [exact Hn|]. split; [exact Hna|]. split; [exact HBK| exact JB].
          - exists 0, []. split; [reflexivity|]. split; [exact HDK|]. split; reflexivity. }
        destruct HDW as (Dd & jb & EDd & HDW).
        unfold MallocRep.wz. unfold implM. iprefix.
        step. if_cases KN; zc KN; [exfalso; revert KN; rewrite ?land_ones64_small, ?unsigned_lit by lia; lia|]. clear KN.
        step. step. setreg 23%Z (Z_to_bv 64 (ll - 2 - sl)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
        step. step. step. ihere. to_implM.
        eapply implM_abind.
        { eapply (OPENSSL_sk_push_walk HM HR) with (L := OWO ++ (NEWO ++ NEW) ++ LB) (lo := lo) (B := B) (SA := KA) (X := AX) (D := Dd) (sorted := sorted) (ws := map (ptrw adrk) (sk_items k)) (jb := jb);
            [exact HEAPO| exact AUXO| rewrite ESP; lia| rewrite ESP; exact STO| exact CEIL| unfold GLOBALS_TOP; lia
            | rewrite ESP; unfold SK_PUSH_STACK, CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK; lia
            | exact ERRO| exact MI| reflexivity| exact CSO| exact (rs_of_state _ _ _ _ _ ASO)
            | exact HKL| rewrite EDd; exact HCK| exact SRT| unfold MAX_SCT_LIST_SIZE in LENB; lia| exact HDW
            | unfold zlength; rewrite !length_map; reflexivity| lia| reflexivity| reflexivity]. }
        intros r1 sP msP POP. unfold push_post in POP. rewrite ?ESP in POP.
        destruct POP as (z0 & z1 & z2 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z3 & z4 & z5 & z6 & mP & errvP & q' & D' & na' & jb'
                         & -> & ER1 & MIP & STP & ERRP & AUXP & HPP & FAP & SOP & BRP & HEAPP & HCP & HDP & JBP & NA1 & NA2).
        subst r1. cbn [fst snd].
        replace (ret_pc (Z_to_bv 64 0x19cf78)) with (Z_to_bv 64 0x19cf78) by (symmetry; apply ret_pc_even; [lia| reflexivity]). unfold MallocRep.wz.
        set (L := OWO ++ (NEWO ++ NEW) ++ LB) in *.
        (* [comment removed for export] *)
        assert (DNI : forall b, In b OWO \/ In b LB -> match sk_data k with Some (q, _) => blk_id b <> q | None => True end /\ blk_id b <> sk_blk k).
        { intros b Hb. assert (Hb' : In (blk_id b) (map blk_id (OWO ++ LB))) by (rewrite map_app; apply in_app_iff; destruct Hb as [Hb|Hb]; [left| right]; apply in_map; exact Hb).
          split.
          - destruct (sk_data k) as [[q na]|] eqn:EDK; [| exact I]. intros E0. apply (FRESHO q (adrk q) (8 * na)); [| rewrite <- E0; exact Hb'].
            apply in_app_iff. right. rewrite ENEW. unfold sk_blocks. rewrite EDK, !in_app_iff. right. left. left. reflexivity.
          - intros E0. apply (FRESHO (sk_blk k) KA STACK_SIZE); [apply in_app_iff; right; exact HKN| rewrite <- E0; exact Hb']. }
        set (NEW1 := (q', D', 8 * na') :: lremove (sk_data k) (NEWO ++ NEW)).
        assert (EL : lremove (sk_data k) L = OWO ++ lremove (sk_data k) (NEWO ++ NEW) ++ LB).
        { subst L. rewrite !lremove_app. rewrite (lremove_notin (sk_data k) OWO), (lremove_notin (sk_data k) LB); [reflexivity| |].
          - destruct (sk_data k) as [[q na]|]; [| exact I]. intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). exact (proj1 (DNI b (or_intror Hb)) Eb).
          - destruct (sk_data k) as [[q na]|]; [| exact I]. intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). exact (proj1 (DNI b (or_introl Hb)) Eb). }
        assert (OIP : oinvL sP stO mP OWO errvP boO NEW1).
        { eapply (KHEAP _ _ _ _ _ _ (NEWO ++ NEW) sP mP errvP _ _ NEW1); [exact OIO| exact HPP| | exact HEAPP| | exact MIP| exact STP| exact ERRP| exact AUXP| exact FAP| exact SOP].
          - intros b Hb. destruct (DNI b Hb) as [D1 D2]. apply in_lb_remove_other; [| exact D2]. apply in_lremove_other; [| exact D1]. subst L. rewrite !in_app_iff.
            destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb].
          - rewrite EL. subst NEW1. apply Permutation_middle. }
        (* [comment removed for export] *)
        set (k1 := mkSK (sk_blk k) (Some (q', na')) (sk_items k ++ [x])) in *.
        set (adrk' := fun b : bptr => if bptr_eqb b q' then D' else adrO b).
        assert (E1 : adrk' q' = D') by (subst adrk'; cbn beta; rewrite bptr_eqb_refl; reflexivity).
        pose proof (LH_nodup _ _ _ HEAPP) as NDP. cbn [map blk_id fst snd] in NDP. apply NoDup_cons_iff in NDP. destruct NDP as [NQ' NDP].
        assert (AGX : forall b, In b (lremove (sk_data k) L) -> adrk' (blk_id b) = adrO (blk_id b)).
        { intros b Hb. subst adrk'. cbn beta. rewrite (bptr_eqb_neq (blk_id b) q'); [reflexivity|]. intros E0. apply NQ'. rewrite <- E0. apply in_map. exact Hb. }
        (* [comment removed for export] *)
        assert (DID : forall b, In b (scts_blocks adrk (sk_items k)) \/ In b NEWO \/ b = (sk_blk k, KA, STACK_SIZE) ->
                      In b (lremove (sk_data k) L) /\ (adrO (blk_id b) = adrk (blk_id b) \/ In b NEWO)).
        { intros b Hb.
          assert (HbL : In b L).
          { subst L. rewrite !in_app_iff. destruct Hb as [Hb|[Hb| ->]]; [right; left; right; rewrite ENEW; unfold sk_blocks; rewrite !in_app_iff; left; exact Hb| right; left; left; exact Hb| right; left; right; exact HKN]. }
          split.
          - apply in_lremove_other; [exact HbL|]. destruct (sk_data k) as [[q na]|] eqn:EDK; [| exact I]. intros E0.
            unfold sk_blocks in NDK. rewrite !map_app in NDK. cbn [dblk map blk_id fst snd app] in NDK.
            destruct Hb as [Hb|[Hb| ->]].
            + destruct (NoDup_app_split _ _ NDK) as (_ & DX & _). apply (DX q); [rewrite <- E0; apply in_map; exact Hb| left; reflexivity].
            + apply (FRO b Hb). rewrite E0, ENEW. unfold sk_blocks. rewrite EDK, !map_app, !in_app_iff. right. left. right. left. left. reflexivity.
            + cbn in E0. destruct (NoDup_app_split _ _ NDK) as (N23 & _ & _). apply NoDup_cons_iff in N23. destruct N23 as [NN _]. apply NN. rewrite <- E0. left. reflexivity.
          - destruct Hb as [Hb|[Hb| ->]]; [left; apply ADRO; apply in_app_iff; left; rewrite ENEW; unfold sk_blocks; rewrite !in_app_iff; left; exact Hb| right; exact Hb| left; apply ADRO; apply in_app_iff; left; exact HKN]. }
        assert (EKA : adrk' (sk_blk k) = KA).
        { destruct (DID (sk_blk k, KA, STACK_SIZE) ltac:(right; right; reflexivity)) as [D1 [D2|D2]]; [rewrite (AGX _ D1); exact D2|].
          exfalso. apply (FRO _ D2). cbn. rewrite !map_app, !in_app_iff. right. left. exact (in_ids _ _ _ _ HKN). }
        assert (AGI : forall x0 q0, In x0 (sk_items k) -> In q0 (sct_ids x0) -> adrk' q0 = adrk q0).
        { intros x0 q0 Hx0 Hq0. rewrite <- (sct_blocks_ids adrk) in Hq0. apply in_map_iff in Hq0. destruct Hq0 as (b & Eb & Hb). subst q0.
          destruct (DID b ltac:(left; eapply scts_blocks_in; [exact Hx0| exact Hb])) as [D1 [D2|D2]]; [rewrite (AGX _ D1); exact D2|].
          exfalso. apply (FRO _ D2). rewrite ENEW. unfold sk_blocks. rewrite !map_app, !in_app_iff. right. left. left.
          apply in_map. eapply scts_blocks_in; [exact Hx0| exact Hb]. }
        assert (AGN : forall q0, In q0 (sct_ids x) -> adrk' q0 = adrO q0).
        { intros q0 Hq0. rewrite <- (sct_blocks_ids adrO), <- ENO in Hq0. apply in_map_iff in Hq0. destruct Hq0 as (b & Eb & Hb). subst q0.
          destruct (DID b ltac:(right; left; exact Hb)) as [D1 _]. exact (AGX _ D1). }
        assert (EAX : adrk' (sc_blk x) = AX) by (rewrite AGN; [reflexivity| unfold sct_ids; rewrite !in_app_iff; right; right; right; right; left; reflexivity]).
        assert (EB1 : sk_blocks adrk' k1 = (scts_blocks adrk (sk_items k) ++ NEWO) ++ [(q', D', 8 * na')] ++ [(sk_blk k, KA, STACK_SIZE)]).
        { unfold sk_blocks. subst k1. cbn [sk_items sk_data sk_blk dblk]. rewrite scts_blocks_app. cbn [scts_blocks]. rewrite app_nil_r.
          rewrite (scts_blocks_ext adrk adrk' (sk_items k)) by (intros x0 q0 Hx0 Hq0; exact (AGI x0 q0 Hx0 Hq0)).
          rewrite (sct_blocks_ext adrO adrk' x) by (intros q0 Hq0; exact (AGN q0 Hq0)). rewrite <- ENO, E1, EKA. reflexivity. }
        assert (PERM1 : Permutation NEW1 (sk_blocks adrk' k1)).
        { rewrite EB1. subst NEW1. rewrite ENEW.
          assert (ELR : lremove (sk_data k) (NEWO ++ sk_blocks adrk k) = NEWO ++ scts_blocks adrk (sk_items k) ++ [(sk_blk k, KA, STACK_SIZE)]).
          { unfold sk_blocks. unfold sk_blocks in NDK. destruct (sk_data k) as [[q na]|] eqn:EDK; cbn [lremove dblk]; [| rewrite app_nil_l || reflexivity; reflexivity].
            rewrite !map_app in NDK. cbn [dblk map blk_id fst snd app] in NDK. destruct (NoDup_app_split _ _ NDK) as (N23 & DX & _). apply NoDup_cons_iff in N23. destruct N23 as [NN _].
            rewrite !lb_remove_app. rewrite (lb_remove_notin q NEWO), (lb_remove_notin q (scts_blocks adrk (sk_items k))), lb_remove_cons, bptr_eqb_refl, (lb_remove_notin q [(sk_blk k, KA, STACK_SIZE)]); [reflexivity| | |].
            - cbn. intros [E0|[]]. apply NN. left. exact E0.
            - intros Hin. exact (DX q Hin (or_introl eq_refl)).
            - intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). apply (FRO b Hb).
              rewrite ENEW. unfold sk_blocks. rewrite EDK, !map_app, !in_app_iff. right. left. right. left. left. cbn. symmetry. exact Eb. }
          rewrite ELR.
          apply Permutation_trans with ((q', D', 8 * na') :: (scts_blocks adrk (sk_items k) ++ NEWO) ++ [(sk_blk k, KA, STACK_SIZE)]).
          - apply perm_skip. rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
          - apply (Permutation_middle (scts_blocks adrk (sk_items k) ++ NEWO) [(sk_blk k, KA, STACK_SIZE)] (q', D', 8 * na')). }
        assert (OIQ : oinvL sP stO mP OWO errvP boO (sk_blocks adrk' k1)) by (eapply KPERM; [exact PERM1| exact OIP]).
        pose proof (KFACTS _ _ _ _ _ _ _ OIQ) as (_ & NDQ & _ & FRESHQ & _).
        pose proof (agree_of_heap_pres _ _ _ _ HPP) as AGP.
        assert (SK1 : sk_rep mP (OWO ++ sk_blocks adrk' k1 ++ LB) adrk' k1).
        { split; [change (sk_blk k1) with (sk_blk k); rewrite EKA; apply in_app_iff; right; apply in_app_iff; left; rewrite EB1; rewrite !in_app_iff; right; right; left; reflexivity|].
          split. { exists (sorted_after sorted (sk_num k)). split; [unfold sorted_after; destruct (negb (sorted =? 0) && (0 <? sk_num k)); lia|].
                   change (sk_blk k1) with (sk_blk k). rewrite EKA, sk_cells_raw. subst k1. cbn [sk_num sk_data sk_items optr olen]. rewrite E1.
                   unfold sk_num in HCP |- *. unfold zlength in HCP |- *. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. exact HCP. }
          split. { subst k1. cbn [sk_data sk_items sk_num]. rewrite E1. split; [apply in_app_iff; right; apply in_app_iff; left; rewrite EB1, !in_app_iff; right; left; left; reflexivity|].
                   unfold sk_num in *. unfold zlength in *. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat].
                   split; [lia|]. split; [exact NA2|]. exists jb'. split; [lia|].
                   unfold data_block. rewrite !map_app. cbn [map]. unfold ptrw at 2. rewrite EAX.
                   rewrite (map_ext_in (ptrw adrk') (ptrw adrk) (sk_items k)); [rewrite map_app in HDP; cbn [map] in HDP; exact HDP|].
                   intros x0 Hx0. unfold ptrw. rewrite (AGI x0 (sc_blk x0) Hx0); [reflexivity|]. unfold sct_ids. rewrite !in_app_iff. right. right. right. right. left. reflexivity. }
          split. { subst k1. cbn [sk_items]. apply Forall_app. split.
                   - apply Forall_forall. intros x0 Hx0. pose proof (proj1 (Forall_forall _ _) HFK x0 Hx0) as SR0.
                     eapply sct_rep_mono; [| eapply (sct_rep_ext adrk adrk'); [intros q0 Hq0; exact (AGI x0 q0 Hx0 Hq0)|]].
                     + intros b Hb. rewrite (sct_blocks_ext adrk adrk' x0) in Hb by (intros q0 Hq0; exact (AGI x0 q0 Hx0 Hq0)).
                       apply in_app_iff. right. apply in_app_iff. left. rewrite EB1, !in_app_iff. left. left. eapply scts_blocks_in; [exact Hx0| exact Hb].
                     + eapply (sct_rep_agreeP _ mO mP); [exact AGP| | exact SR0].
                       intros q0 Aq n a Hq Ha. right. right. exists (q0, Aq, n). split; [| cbn; lia].
                       destruct (DID (q0, Aq, n) ltac:(left; eapply scts_blocks_in; [exact Hx0| exact Hq])) as [D1 _].
                       apply in_lb_remove_other; [exact D1|]. cbn. intros ->.
                       unfold sk_blocks in NDK. rewrite !map_app in NDK. destruct (NoDup_app_split _ _ NDK) as (N23 & DX & _).
                       apply (DX (sk_blk k)); [apply in_map_iff; exists (sk_blk k, Aq, n); split; [reflexivity| eapply scts_blocks_in; [exact Hx0| exact Hq]]|].
                       apply in_app_iff. right. left. reflexivity.
                   - constructor; [| constructor].
                     eapply sct_rep_mono; [| eapply (sct_rep_ext adrO adrk'); [intros q0 Hq0; exact (AGN q0 Hq0)|]].
                     + intros b Hb. rewrite (sct_blocks_ext adrO adrk' x) in Hb by (intros q0 Hq0; exact (AGN q0 Hq0)). rewrite <- ENO in Hb.
                       apply in_app_iff. right. apply in_app_iff. left. rewrite EB1, !in_app_iff. left. right. exact Hb.
                     + eapply (sct_rep_agreeP _ mO mP); [exact AGP| | exact SRX].
                       intros q0 Aq n a Hq Ha. right. right. exists (q0, Aq, n). split; [| cbn; lia]. rewrite <- ENO in Hq.
                       destruct (DID (q0, Aq, n) ltac:(right; left; exact Hq)) as [D1 _].
                       apply in_lb_remove_other; [exact D1|]. cbn. intros ->. apply (FRO _ Hq). cbn. rewrite !map_app, !in_app_iff. right. left. exact (in_ids _ _ _ _ HKN). }
          rewrite (map_app blk_id OWO), (map_app blk_id (sk_blocks adrk' k1) LB) in NDQ.
          destruct (NoDup_app_split _ _ NDQ) as (N23 & _ & _). destruct (NoDup_app_split _ _ N23) as (_ & _ & N2). exact N2. }
        assert (ADRK1 : forall b, In b LB -> adrk' (blk_id b) = adr (blk_id b)).
        { intros b Hb. rewrite <- (ADRK b Hb), <- (ADRO b) by (apply in_app_iff; right; exact Hb). apply AGX.
          destruct (DNI b (or_intror Hb)) as [D1 D2]. apply in_lremove_other; [| exact D1]. subst L. rewrite !in_app_iff. right. right. exact Hb. }
        apply (rw_cells_agree _ _ _ _ _ AGP) in FR; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGP) in HPO; [| intros a Ha; left; cbn in Ha; lia].
        clear MU WM MI. rename MIP into MI. pose proof (munch_refl (@nil (Z * Z)) mP) as MU. pose proof (wmono_refl ctusegs mP) as WM.
        (* [comment removed for export] *)
        unfold implM. iprefix. step. if_cases KZ; zc KZ.
        2:{ exfalso. revert KZ. unfold sk_num, zlength in *. unfold MAX_SCT_LIST_SIZE in LENB. rewrite land_ones64_small by lia. lia. }
        ihere. to_implM.
        replace (Z_to_bv 64 KA) with (wz (adrk' (sk_blk k1))) by (change (sk_blk k1) with (sk_blk k); rewrite EKA; reflexivity).
        eapply (IH k1 (pq + 2 + sl) (ll - 2 - sl) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FS fcS sP stO mP OWO errvP boO (sk_blocks adrk' k1) adrk');
          [| lia| exact FRMS| intros r0 Hr0; rewrite (FES r0 Hr0); apply (FEX r0 Hr0)].
        split; [exact OIQ|]. split; [reflexivity|]. split; [exact SK1|]. split; [exact ADRK1|]. split; [exact FR|].
        split; [replace (D + (pq + 2 + sl)) with (D + (pq + 2) + sl) by lia; exact HPO|].
        subst k1. unfold sk_num in *. cbn [sk_items]. unfold zlength in *. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. repeat split; lia.
      + (* [comment removed for export] *)
        destruct RES as [ENO HPO]. subst NEWO. cbn [app] in OIO, SKO |- *.
        unfold implM. iprefix. step. if_cases KN; zc KN; [| exfalso; apply KN; reflexivity]. clear KN.
        ihere. to_implM.
        eapply (free_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (D + (pq + 2))) FS fcS sO stO mO OWO errvO boO NEW adrk k);
          [exact OIO| exact FRMS| intros r0 Hr0; rewrite (FES r0 Hr0); apply (FEX r0 Hr0)| exact PM| exact SKO| exact FR| exact HPO].
  Qed.

  (* [comment removed for export] *)
  Lemma loop_ok : forall fuel (ll : Z) (k : skr bptr) (pq : Z)
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32)
      sX stX mX OWX errvX boX NEW adrk,
    linv k pq ll sX stX mX OWX errvX boX NEW adrk -> ll < Z.of_nat fuel -> zlength c <= MAX_SCT_LIST_SIZE -> frm0 fcX -> (forall r : reg, bv_unsigned r <> 10 -> reg_get FX r = reg_get F r) ->
    implM ctusegs (interp (ap_embed (o2i_loop fuel c k pq ll stX))) sX SPOST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) x5 x6 x7 x8 (wz 0) x10 x11 x12 x13 x14 x15 x16 x17 (wz (adrk (sk_blk k))) (wz PIN) x20 x21 x22 (wz ll) (wz 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3)) s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 0x19cf14) fcX None mX (seg_rom ctusegs)).
  Proof using ADR D0 D63 DF HF HM HR PBX PINhi PINlo PRE fc tp PIN8.
    induction fuel as [|f IH]; intros until adrk; intros LI LLF LENB FRMX FEX.
    { exfalso. destruct LI as (_ & _ & _ & _ & _ & _ & _ & LL0 & _). cbn in LLF. lia. }
    ctx. pose proof LI as (OI & ENEW & SK & ADRK & FR & HP & PQ2 & LL0 & PQL & NUMB).
    assert (PM : Permutation NEW (sk_blocks adrk k)) by (rewrite ENEW; apply Permutation_refl).
    pose proof (KFACTS _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & _).
    pose proof (KCALL _ _ _ _ _ _ _ OI) as (_ & _ & _ & STX & _ & _ & ERRX & MI & _).
    cbn [o2i_loop]. unfold MallocRep.wz.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    unfold lframe in FR. unfold MallocRep.wz in HP.
    unfold implM. iprefix. step. if_cases K0; zc K0.
    - (* [comment removed for export] *)
      replace (ll <=? 0) with true by (symmetry; apply Z.leb_le; revert K0; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LENB; lia); lia).
      step. if_cases K9; zc K9; [| exfalso; apply K9; reflexivity]. clear K9.
      ihere. to_implM. apply implM_aret.
      eapply ret_some; [exact OI| exact FRMX| exact FEX| exact PM| exact SK| exact ADRK| exact FR| exact HP].
    - assert (L1 : 1 <= ll) by (revert K0; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LENB; lia); lia). clear K0.
      replace (ll <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
      step. if_cases K1; zc K1.
      + (* [comment removed for export] *)
        replace (ll <? 2) with true by (symmetry; apply Z.ltb_lt; revert K1; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LENB; lia); lia).
        ihere. to_implM.
        assert (OI0 : oinvL sX stX mX OWX errvX boX NEW) by exact OI.
        eapply implM_abind; [eapply (raise_gen 0x19cff4 6%nat 0x19d040 RS_list_lt2); [right; right; left; repeat split; reflexivity| exact OI0| exact FRMX| exact FEX]|].
        intros r sF msF RP. cbv beta. unfold raise_post in RP.
        destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & errvF & boF
                        & -> & FRMF & FEF & OIF & LXF).
        pose proof (agree_of_lx_pres _ _ _ _ _ LXF) as AGF.
        assert (CLs : forall a, bv_unsigned sp + -96 <= a -> lx_client (NEW ++ LB) (bv_unsigned sp + -96) LIBW_AP a).
        { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
        apply (rw_cells_agree _ _ _ _ _ AGF) in FR; [| intros a Ha; apply CLs; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGF) in HP; [| intros a Ha; apply CLs; cbn in Ha; lia].
        change (Z_to_bv 64 (1691712 + 20)) with (Z_to_bv 64 0x19d054).
        eapply (free_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (D + pq)) FF fcF sF (snd r) mF OWF errvF boF NEW adrk k);
          [exact OIF| exact FRMF| exact FEF| exact PM| | exact FR| exact HP].
        eapply sk_rep_mono; [intros b Hb; apply in_app_iff; right; apply in_app_iff; left; eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]|].
        eapply (sk_rep_agreeP _ mX mF); [exact AGF| intros q Aq n a Hq Ha; eapply (sk_blocks_client sX stX mX OWX errvX boX NEW adrk k); [exact OI| exact PM| exact Hq| exact Ha]| exact SK].
      + (* [comment removed for export] *)
        assert (L2 : 2 <= ll) by (revert K1; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LENB; lia); lia). clear K1.
        replace (ll <? 2) with false by (symmetry; apply Z.ltb_ge; lia).
        ihere. to_implM.
        eapply (iter_body (o2i_loop f c) ll); [| exact LI| exact L2| exact LENB| exact FRMX| exact FEX].
        intros until adrk'. intros LI' LL' FRMY FEY. eapply IH; [exact LI'| cbn in LLF; lia| exact LENB| exact FRMY| exact FEY].
  Qed.

  Theorem list_main : forall (t0 t1 t2 t3 a3 a4 a5 a6 a7 t4 t5 t6 : word),
    implM ctusegs (interp (ap_embed (o2i_sct_list c len st))) s SPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz PIN) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz O2I_SCT_LIST) fc None m (seg_rom ctusegs)).
  Proof using ADR D0 D63 DF ELEN FRM HB0 HF HM HPIN HR KIDS KOW PBX PINhi PINlo PRE TP PIN8.
    intros. ctx. rewrite TP.
    pose proof PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST & CEIL' & GLO' & LO' & ERR & SSP & MI & _).
    unfold MallocRep.wz in ERR. rewrite (EA) in ERR.
    unfold MallocRep.wz in HPIN. pose proof HPIN as HP. clear HPIN.
    assert (OI0 : oinvL s st m OW errv bo []).
    { eapply (oinv_entry sp m s LB E lo B canary K c D PIN (-96) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 PINlo PINhi st OW bo errv); [| exact KOW| exact KIDS| exact HB0].
      unfold STK. unfold O2I_SCT_LIST_STACK in PRE. exact PRE. }
    unfold O2I_SCT_LIST, MallocRep.wz.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 96%nat ST. do 14 step. step.
    step. step. step. name_mem m1.
    assert (OI1 : oinvL s st m1 OW errv bo []).
    { eapply KMUNCH; [exact OI0| exact MU| exact WM| exact MI| exact ST| exact ERR|]. constructor; [left; cbn; lia| constructor]. }
    unfold o2i_sct_list.
    step. if_cases KL; zc KL.
    2:{ (* [comment removed for export] *)
        replace ((len <? 2) || (MAX_SCT_LIST_SIZE <? len)) with true.
        2:{ symmetry. unfold MAX_SCT_LIST_SIZE. destruct (Z.lt_ge_cases len 2) as [Hl|Hl]; [apply orb_true_intro; left; apply Z.ltb_lt; exact Hl|].
            destruct (Z.lt_ge_cases 65535 len) as [Hh|Hh]; [apply orb_true_intro; right; apply Z.ltb_lt; exact Hh|].
            exfalso. revert KL. rewrite land_ones64_neg by lia. lia. }
        ihere. to_implM.
        eapply implM_abind; [eapply (raise_gen 0x19ce4c 6%nat 0x19cfa0 RS_list_len); [left; repeat split; reflexivity| exact OI1| exact FRM| intros; reflexivity]|].
        intros r sF msF RP. cbv beta. unfold raise_post in RP.
        destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & errvF & boF
                        & -> & FRMF & FEF & OIF & LXF).
        pose proof (agree_of_lx_pres _ _ _ _ _ LXF) as AGF.
        assert (CLs : forall a, bv_unsigned sp + -96 <= a -> lx_client ([] ++ LB) (bv_unsigned sp + -96) LIBW_AP a).
        { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
        apply (rw_cells_agree _ _ _ _ _ AGF) in FR; [| intros a Ha; apply CLs; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGF) in HP; [| intros a Ha; apply CLs; cbn in Ha; lia].
        apply implM_aret. change (Z_to_bv 64 (1691552 + 20)) with (Z_to_bv 64 0x19cfb4).
        eapply ret_null; [exact OIF| exact FRMF| exact FEF| exact FR| exact HP]. }
    (* [comment removed for export] *)
    assert (LEN : 2 <= len <= MAX_SCT_LIST_SIZE).
    { unfold MAX_SCT_LIST_SIZE. destruct (Z.lt_ge_cases len 2); [exfalso| destruct (Z.lt_ge_cases 65535 len); [exfalso| lia]];
        revert KL; first [rewrite land_ones64_neg by lia| rewrite land_ones64_small by lia| idtac]; lia. }
    replace ((len <? 2) || (MAX_SCT_LIST_SIZE <? len)) with false by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.ltb_ge]; lia). clear KL.
    destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)]; [exfalso; rewrite E0 in ELEN; unfold zlength in ELEN; cbn in ELEN; lia|].
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HPB)) as (PB3 & _ & _ & PB4 & PB5). cbn [blk_addr blk_size fst snd] in PB3, PB4, PB5.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range c i DF). lia. }
    pose proof (znth_range c 0 DF) as R0. pose proof (znth_range c 1 DF) as R1.
    pose proof OI1 as (_ & _ & _ & _ & _ & _ & _ & HB1).
    set (ll := u16be c 0). pose proof (u16be_range c 0) as LLR. fold ll in LLR.
    clear MU WM. pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (PIN, PIN + 8)]%Z m1) as MU. pose proof (wmono_refl ctusegs m1) as WM.
    (* [comment removed for export] *)
    pose proof PIN8 as PIN8a.
    step. if_cases KC0; zify_cond KC0; [exfalso; rewrite ?unsigned_lit in KC0 by lia; lia|]. clear KC0.
    step. step. step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; change 7 with (Z.ones 3) in KA; rewrite Z.land_ones in KA by lia; change (2 ^ 3) with 8 in KA; lia|]. clear KA.
    step. step. if_cases KC1; zify_cond KC1; [exfalso; rewrite ?unsigned_lit in KC1 by lia; lia|]. clear KC1.
    step. step. if_cases KC2; zify_cond KC2; [exfalso; rewrite ?unsigned_lit in KC2 by lia; lia|]. clear KC2.
    step. step. if_cases KC3; zify_cond KC3; [exfalso; rewrite ?unsigned_lit in KC3 by lia; lia|]. clear KC3.
    pose proof (payload_read _ D c 0 (wa (D + 0)) HB1 DF ltac:(lia) eq_refl) as RD. replace (wa (D + 0)) with (wa D) in RD by (unfold wa; f_equal; lia). step. clear RD. rewrite (zxb_lit (znth c 0)) by lia.
    pose proof (payload_read _ D c 1 (wa (D + 1)) HB1 DF ltac:(lia) eq_refl) as RD. step. clear RD. rewrite (zxb_lit (znth c 1)) by lia.
    step. step. step.
    setreg 23%Z (Z_to_bv 64 ll)
      ltac:(subst ll; unfold u16be; rewrite !BY by lia; replace (0 + 1) with 1 by lia; f_equal;
            rewrite (unsigned_lit (znth c 0)), (unsigned_lit (znth c 1)) by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256;
            rewrite (unsigned_lit (znth c 0 * 256)) by lia; symmetry; apply lor_shl8; lia).
    step. setreg 12%Z (Z_to_bv 64 (len - 2)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LEN; lia); bv_solve).
    step. name_mem m2.
    assert (OI2 : oinvL s st m2 OW errv bo []).
    { eapply KMUNCH; [exact OI1| exact MU| exact WM| exact MI| exact ST| exact ERR|]. constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity| constructor]. }
    step. if_cases KM; zc KM.
    { (* [comment removed for export] *)
      replace (negb (ll =? len - 2)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; intros E0; apply KM; rewrite E0; reflexivity).
      ihere. to_implM.
      eapply implM_abind; [eapply (raise_gen 0x19cf88 5%nat 0x19cfa0 RS_list_mismatch); [right; left; repeat split; reflexivity| exact OI2| exact FRM| intros; reflexivity]|].
      intros r sF msF RP. cbv beta. unfold raise_post in RP.
      destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & errvF & boF
                      & -> & FRMF & FEF & OIF & LXF).
      pose proof (agree_of_lx_pres _ _ _ _ _ LXF) as AGF.
      assert (CLs : forall a, bv_unsigned sp + -96 <= a -> lx_client ([] ++ LB) (bv_unsigned sp + -96) LIBW_AP a).
      { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
      apply (rw_cells_agree _ _ _ _ _ AGF) in FR; [| intros a Ha; apply CLs; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGF) in HP; [| intros a Ha; apply CLs; cbn in Ha; lia].
      apply implM_aret. change (Z_to_bv 64 (1691552 + 20)) with (Z_to_bv 64 0x19cfb4).
      eapply ret_null; [exact OIF| exact FRMF| exact FEF| exact FR| exact HP]. }
    assert (ELL : ll = len - 2) by (revert KM; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LEN; lia); lia). clear KM.
    replace (negb (ll =? len - 2)) with false by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; exact ELL).
    (* [comment removed for export] *)
    step. step. if_cases K9; zc K9; [| exfalso; apply K9; reflexivity]. clear K9.
    step. ihere. cbn [abind apbind amalloc aret ap_embed fst snd]. to_implM.
    pose proof (KCALL _ _ _ _ _ _ _ OI2) as (HEAP2 & AUX2 & _ & ST2 & _ & _ & ERR2 & MI2 & CS2 & _).
    change SZ_STACK with STACK_SIZE.
    eapply (OPENSSL_sk_new_null_walk HM) with (B := B) (lo := lo) (errv := errv) (L := OW ++ [] ++ LB);
      [exact HEAP2| exact AUX2| rewrite ESP; lia| rewrite ESP; exact ST2| exact CEIL| unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold SK_NEW_NULL_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
      | exact ERR2| exact MI2| reflexivity| exact CS2| reflexivity|].
    intros kb sN msN PON. unfold calloc_post in PON. rewrite ?ESP in PON.
    destruct PON as (n0 & n1 & n2 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n3 & n4 & n5 & n6 & mN & KA & errvN
                     & -> & MIN & STN & ERRN & AUXN & HPN & FAN & SON & BRN & HEAPN & BLKN).
    replace (ret_pc (Z_to_bv 64 0x19cec8)) with (Z_to_bv 64 0x19cec8) by (symmetry; apply ret_pc_even; [lia| reflexivity]). unfold MallocRep.wz.
    assert (OI3 : oinvL sN st mN OW errvN bo [(kb, KA, STACK_SIZE)]).
    { eapply KALLOC; [exact OI2| exact HPN| exact HEAPN| exact MIN| exact STN| exact ERRN| exact AUXN| exact FAN| exact SON]. }
    pose proof (KFACTS _ _ _ _ _ _ _ OI3) as (_ & ND3 & _ & FRESH3 & _).
    pose proof BRN as (BK0 & BK16 & _ & BKC & BKI). unfold STACK_SIZE in BKC, BKI.
    cbn [apbind fst snd].
    pose proof (agree_of_heap_pres _ _ _ _ HPN) as AGN.
    apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGN) in HP; [| intros a Ha; left; cbn in Ha; lia].
    unfold LX_ERRNO, RATP in ERRN. change (3355176 - 164) with 3355012 in ERRN.
    clear MU WM AGN MI. rename MIN into MI.
    pose proof (munch_refl [(bv_unsigned sp - 96 - 16, bv_unsigned sp - 96); (KA, KA + 56)]%Z mN) as MU. pose proof (wmono_refl ctusegs mN) as WM.
    (* [comment removed for export] *)
    unfold implM. iprefix.
    step. step. step.
    eapply evt_cut; [eapply (OPENSSL_sk_set_thunk_spec OPENSSL_SK_SET_CMP_THUNKS 0 0 0 SK_SCT_CMP_THUNK SK_SCT_CMP_THUNK 0 0);
      [left; repeat split; reflexivity| rewrite ESP; exact STN| exact MI| exact CEIL| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact BRN| exact BLKN| unfold SK_SCT_CMP_THUNK; lia| reflexivity| reflexivity]|].
    post_call_esp2 ESP mN. name_mem mA. rename POST into HC.
    step. step. step.
    eapply evt_cut; [eapply (OPENSSL_sk_set_thunk_spec OPENSSL_SK_SET_COPY_THUNKS SK_SCT_CMP_THUNK 0 0 SK_SCT_COPY_THUNK SK_SCT_CMP_THUNK 0 SK_SCT_COPY_THUNK);
      [right; right; repeat split; reflexivity| rewrite ESP; eassumption| eassumption| exact CEIL| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact BRN| exact HC| unfold SK_SCT_COPY_THUNK; lia| reflexivity| reflexivity]|].
    clear HC. post_call_esp2 ESP mA. name_mem mB. rename POST into HC.
    step. step. step.
    eapply evt_cut; [eapply (OPENSSL_sk_set_thunk_spec OPENSSL_SK_SET_THUNKS SK_SCT_CMP_THUNK 0 SK_SCT_COPY_THUNK SK_SCT_FREEFUNC_THUNK SK_SCT_CMP_THUNK SK_SCT_FREEFUNC_THUNK SK_SCT_COPY_THUNK);
      [right; left; repeat split; reflexivity| rewrite ESP; eassumption| eassumption| exact CEIL| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact BRN| exact HC| unfold SK_SCT_FREEFUNC_THUNK; lia| reflexivity| reflexivity]|].
    clear HC. post_call_esp2 ESP mB. name_mem mC. rename POST into HC. rename MI0 into MI.
    assert (OI4 : oinvL sN st mC OW errvN bo [(kb, KA, STACK_SIZE)]).
    { eapply KMUNCH; [exact OI3| exact MU| exact WM| exact MI| eassumption| exact ERRN|].
      constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists kb, KA, STACK_SIZE. split; [left; reflexivity| cbn; unfold STACK_SIZE; lia]. }
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mC) as MU. pose proof (wmono_refl ctusegs mC) as WM.
    (* [comment removed for export] *)
    step. step. if_cases K1; zc K1; [| exfalso; revert K1; rewrite ?land_ones64_small, ?unsigned_lit by lia; lia]. clear K1.
    step. step. step. ihere. to_implM.
    set (k0 := mkSK kb (@None (bptr * Z)) (@nil (sctr bptr))).
    set (adrk := fun b : bptr => if bptr_eqb b kb then KA else adr b).
    assert (EKA : adrk kb = KA) by (subst adrk; cbn beta; rewrite bptr_eqb_refl; reflexivity).
    assert (EB0 : sk_blocks adrk k0 = [(kb, KA, STACK_SIZE)]) by (unfold sk_blocks; subst k0; cbn [sk_items sk_data sk_blk scts_blocks dblk app]; rewrite EKA; reflexivity).
    replace (wz KA) with (wz (adrk (sk_blk k0))) by (change (sk_blk k0) with kb; rewrite EKA; reflexivity).
    eapply (loop_ok (Z.to_nat len) ll k0 2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc sN st mC OW errvN bo [(kb, KA, STACK_SIZE)] adrk);
      [| rewrite Z2Nat.id by lia; lia| subst len; exact (proj2 LEN)| exact FRM| intros; reflexivity].
    split; [exact OI4|]. split; [symmetry; exact EB0|]. split.
    { split; [change (sk_blk k0) with kb; rewrite EKA; apply in_app_iff; right; left; reflexivity|].
      split. { exists 1. split; [lia|]. change (sk_blk k0) with kb. rewrite EKA. unfold sk_cells. subst k0. cbn [sk_num sk_data sk_items optr olen zlength length Z.of_nat].
               unfold sk_cells0 in HC. exact HC. }
      split; [subst k0; cbn [sk_data sk_items]; reflexivity|].
      split; [subst k0; cbn [sk_items]; constructor|].
      subst k0. cbn [sk_items sk_data sk_blk scts_blocks dblk app map blk_id fst snd]. constructor; [intros []| constructor]. }
    split. { intros b Hb. subst adrk. cbn beta. rewrite (bptr_eqb_neq (blk_id b) kb); [reflexivity|]. intros E0.
             destruct b as [[q Aq] n]. cbn in E0. subst q. apply (FRESH3 kb KA STACK_SIZE ltac:(left; reflexivity)). rewrite map_app. apply in_app_iff. right. exact (in_ids _ _ _ _ Hb). }
    split; [exact FR|]. split; [exact HP|].
    subst k0. unfold sk_num. cbn [sk_items]. subst len ll. unfold zlength in *. cbn [length Z.of_nat]. repeat split; lia.
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem o2i_sct_list_walk : o2i_sct_list_spec.
  Proof using HF HM HR.
    unfold o2i_sct_list_spec. intros until PIN. intros PRE TP FRM KOW KIDS ELEN D0 D63 DF HB0 PBX ADR PINlo PINhi PIN8 HPIN -> -> ->.
    eapply list_main; eassumption.
  Qed.
End Proofs.
End WithCeiling0.
