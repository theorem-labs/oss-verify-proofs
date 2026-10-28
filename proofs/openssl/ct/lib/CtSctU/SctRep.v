(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition u32 (z : Z) : Z := z mod 2^32.
Lemma u32_m1 : u32 (-1) = 2^32 - 1. Proof. reflexivity. Qed.
Lemma u32_small : forall z, 0 <= z < 2^32 -> u32 z = z. Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

Definition logid_len (o : option bptr) : Z := match o with Some _ => CT_V1_HASHLEN | None => 0 end.

Definition sct_cells (adr : bptr -> Z) (s : sctr bptr) (et vs : Z) : list cell :=
  [C4 (wz (u32 (sc_version s))); C4 (wz 0);
   C8 (wz (optr adr (sc_blob s))); C8 (wz (sc_bloblen s));
   C8 (wz (optr adr (osz32 (sc_logid s)))); C8 (wz (logid_len (sc_logid s)));
   C8 (wz (sc_ts s));
   C8 (wz (optr adr (sc_ext s))); C8 (wz (sc_extlen s));
   C1 (Z_to_bv 8 (sc_hash s)); C1 (Z_to_bv 8 (sc_sigalg s)); CB 6%nat (repeat (Z_to_bv 8 0) 6%nat);
   C8 (wz (optr adr (sc_sig s))); C8 (wz (sc_siglen s));
   C4 (wz (u32 et)); C4 (wz 0); C4 (wz (u32 vs)); C4 (wz 0)].

Lemma sct_cells_size : forall adr s et vs, Z.of_nat (cells_size (sct_cells adr s et vs)) = SCT_SIZE.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)

Section WithCeiling. Context {CE__ : Ceiling}.
(* [comment removed for export] *)
Lemma sct_ptr_cells_of_cells : forall m adr s et vs,
  rw_cells ctusegs m (adr (sc_blk s)) (sct_cells adr s et vs) -> sct_ptr_cells m adr s.
Proof.
  intros m adr s et vs H. unfold sct_ptr_cells. cbn zeta. unfold SCTO_SCT, SCTO_LOG_ID, SCTO_EXT, SCTO_SIG.
  assert (SPLIT : forall k pre c post, sct_cells adr s et vs = pre ++ c :: post -> Z.of_nat (cells_size pre) = k ->
                  ro_cells ctusegs m (adr (sc_blk s) + k) [c]).
  { intros k pre c post E Hk. rewrite E in H. apply rw_cells_app in H. destruct H as [_ H2]. rewrite Hk in H2.
    change (c :: post) with ([c] ++ post) in H2. apply rw_cells_app in H2. destruct H2 as [H3 _]. exact (proj1 H3). }
  split; [|split; [|split]].
  - apply (SPLIT 8 [C4 (wz (u32 (sc_version s))); C4 (wz 0)] _ _ eq_refl eq_refl).
  - eapply (SPLIT 24 (firstn 4 (sct_cells adr s et vs))); [reflexivity| reflexivity].
  - eapply (SPLIT 48 (firstn 7 (sct_cells adr s et vs))); [reflexivity| reflexivity].
  - eapply (SPLIT 72 (firstn 12 (sct_cells adr s et vs))); [reflexivity| reflexivity].
Qed.
End WithCeiling.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition olen (o : option (bptr * Z)) : Z := match o with Some (_, n) => n | None => 0 end.
Local Notation mem := (word -> option byte).

Section WithCeiling2. Context {CE__ : Ceiling}.
(* [comment removed for export] *)
Definition arr_rep (m : mem) (L : list block) (adr : bptr -> Z) (o : option (bptr * Z)) : Prop :=
  match o with
  | Some (q, n) => 0 < n /\ In (q, adr q, n) L /\ exists bs, rw_cells ctusegs m (adr q) [CB (Z.to_nat n) bs]
  | None => True
  end.

Definition sct_rep (m : mem) (L : list block) (adr : bptr -> Z) (x : sctr bptr) : Prop :=
  In (sc_blk x, adr (sc_blk x), SCT_SIZE) L
  /\ rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) 0)
  /\ arr_rep m L adr (osz32 (sc_logid x)) /\ arr_rep m L adr (sc_ext x) /\ arr_rep m L adr (sc_sig x) /\ arr_rep m L adr (sc_blob x)
  /\ List.NoDup (map blk_id (sct_blocks adr x))
  /\ (sc_version x = -1 \/ 0 <= sc_version x < 256) /\ (sc_version x = 0 -> sct_nid x <> NID_undef)      (* [comment removed for export] *)
  /\ 0 <= sc_hash x < 256 /\ 0 <= sc_sigalg x < 256 /\ 0 <= sc_ts x < 2^64
  /\ sc_extlen x = olen (sc_ext x)
  /\ olen (sc_ext x) <= MAX_SCT_SIZE /\ olen (sc_sig x) <= MAX_SCT_SIZE /\ olen (sc_blob x) <= MAX_SCT_SIZE.

(* [comment removed for export] *)
Definition scts_rep (m : mem) (L : list block) (adr : bptr -> Z) (l : list (sctr bptr)) : Prop :=
  Forall (sct_rep m L adr) l /\ List.NoDup (map blk_id (scts_blocks adr l)).

Lemma sc_siglen_olen : forall (x : sctr bptr), sc_siglen x = olen (sc_sig x).
Proof. intros x. unfold sc_siglen, olen. destruct (sc_sig x) as [[q n]|]; reflexivity. Qed.
Lemma sc_bloblen_olen : forall (x : sctr bptr), sc_bloblen x = olen (sc_blob x).
Proof. intros x. unfold sc_bloblen, olen. destruct (sc_blob x) as [[q n]|]; reflexivity. Qed.

Lemma arr_rep_pres : forall m m' L L' SP adr o,
  rheap_pres L' SP m m' -> (forall b, In b (oblk adr o) -> In b L') -> arr_rep m L adr o -> arr_rep m' L adr o.
Proof.
  intros m m' L L' SP adr [[q n]|] HP HIN H; cbn in *; [|exact I]. destruct H as (Hn & HL & bs & HB). split; [exact Hn|]. split; [exact HL|]. exists bs.
  eapply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)); [exact HB|].
  intros a Ha. right. right. exists (q, adr q, n). split; [apply HIN; left; reflexivity|]. cbn. cbn in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. lia.
Qed.

Lemma sct_rep_pres : forall m m' L L' SP adr x,
  rheap_pres L' SP m m' -> (forall b, In b (sct_blocks adr x) -> In b L') -> sct_rep m L adr x -> sct_rep m' L adr x.
Proof.
  intros m m' L L' SP adr x HP HIN (H1 & H2 & H3 & H4 & H5 & H6 & REST).
  assert (INC : forall b, In b (oblk adr (osz32 (sc_logid x))) \/ In b (oblk adr (sc_ext x)) \/ In b (oblk adr (sc_sig x)) \/ In b (oblk adr (sc_blob x))
                          \/ b = (sc_blk x, adr (sc_blk x), SCT_SIZE) -> In b L').
  { intros b Hb. apply HIN. unfold sct_blocks. rewrite !in_app_iff. cbn. destruct Hb as [Hb|[Hb|[Hb|[Hb| ->]]]]; tauto. }
  split; [exact H1|]. split.
  { eapply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)); [exact H2|].
    intros a Ha. right. right. exists (sc_blk x, adr (sc_blk x), SCT_SIZE). split; [apply INC; right; right; right; right; reflexivity|].
    cbn. rewrite sct_cells_size in Ha. unfold SCT_SIZE in *. lia. }
  split; [eapply arr_rep_pres; [exact HP| intros b Hb; apply INC; left; exact Hb| exact H3]|].
  split; [eapply arr_rep_pres; [exact HP| intros b Hb; apply INC; right; left; exact Hb| exact H4]|].
  split; [eapply arr_rep_pres; [exact HP| intros b Hb; apply INC; right; right; left; exact Hb| exact H5]|].
  split; [eapply arr_rep_pres; [exact HP| intros b Hb; apply INC; right; right; right; left; exact Hb| exact H6]|].
  exact REST.
Qed.

Lemma scts_rep_pres : forall m m' L L' SP adr l,
  rheap_pres L' SP m m' -> (forall b, In b (scts_blocks adr l) -> In b L') -> scts_rep m L adr l -> scts_rep m' L adr l.
Proof.
  intros m m' L L' SP adr l HP HIN [HF ND]. split; [|exact ND]. clear ND.
  induction l as [|x t IH]; [constructor|]. inversion HF; subst. cbn in HIN. constructor.
  - eapply sct_rep_pres; [exact HP| intros b Hb; apply HIN; apply in_app_iff; left; exact Hb| assumption].
  - apply IH; [intros b Hb; apply HIN; apply in_app_iff; right; exact Hb| assumption].
Qed.

(* [comment removed for export] *)
Lemma sct_rep_ptr_cells : forall m L adr x, sct_rep m L adr x -> sct_ptr_cells m adr x.
Proof. intros m L adr x (_ & H & _). eapply sct_ptr_cells_of_cells. exact H. Qed.

Lemma sct_rep_blocks_in : forall m L adr x, sct_rep m L adr x -> forall b, In b (sct_blocks adr x) -> In b L.
Proof.
  intros m L adr x (H1 & _ & H3 & H4 & H5 & H6 & _) b Hb. unfold sct_blocks in Hb. rewrite !in_app_iff in Hb.
  assert (AR : forall o, arr_rep m L adr o -> In b (oblk adr o) -> In b L).
  { intros [[q n]|] Ho Hi; cbn in *; [|tauto]. destruct Hi as [<-|[]]. tauto. }
  destruct Hb as [Hb|[Hb|[Hb|[Hb|Hb]]]]; [eapply AR; [exact H3|exact Hb]| eapply AR; [exact H4|exact Hb]| eapply AR; [exact H5|exact Hb]| eapply AR; [exact H6|exact Hb]|].
  cbn in Hb. destruct Hb as [<-|[]]. exact H1.
Qed.
End WithCeiling2.

