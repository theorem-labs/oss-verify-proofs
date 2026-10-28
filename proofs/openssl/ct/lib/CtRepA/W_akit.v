(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge Arr FP Frame Cells Step Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnIfaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acl_sub : forall (L L' : list block) SP SP' a,
  (forall b, In b L' -> In b L) -> SP <= SP' -> aclient_addr L' SP' a -> aclient_addr L SP a.
Proof.
  intros L L' SP SP' a HL HS [Ha|[Ha|(b & Hb & Hr)]]; [left; lia| right; left; exact Ha| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma lb_remove_app_incl1 : forall p (OW LB : list block) b,
  In b (lb_remove p OW ++ LB) -> In b (OW ++ LB).
Proof.
  intros p OW LB b Hb. apply in_app_iff in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
  eapply lb_remove_incl. exact Hb.
Qed.

Lemma lb_remove2_app_incl : forall p q (OW LB : list block) b,
  In b (lb_remove p (lb_remove q OW) ++ LB) -> In b (OW ++ LB).
Proof.
  intros p q OW LB b Hb. apply (lb_remove_app_incl1 q). apply in_app_iff in Hb. apply in_or_app.
  destruct Hb as [Hb|Hb]; [left; eapply lb_remove_incl; exact Hb| right; exact Hb].
Qed.

(* [comment removed for export] *)
Lemma lb_remove_app_l : forall p (OW LB : list block) b,
  (forall b', In b' LB -> blk_id b' <> p) -> In b (lb_remove p OW ++ LB) -> In b (lb_remove p (OW ++ LB)).
Proof.
  intros p OW LB b HLB Hb. apply lb_remove_In. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
  - apply lb_remove_In in Hb. destruct Hb as [Hb Hne]. split; [apply in_or_app; left; exact Hb| exact Hne].
  - split; [apply in_or_app; right; exact Hb| exact (HLB b Hb)].
Qed.

Lemma lb_remove_id_ne : forall p (L : list block) b, In b (lb_remove p L) -> blk_id b <> p.
Proof. intros p L b Hb. apply lb_remove_In in Hb. exact (proj2 Hb). Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acl_off_frame : forall Σ OW LB m (L' : list block) SP lo F a,
  AHEAP Σ OW LB m -> (forall b, In b L' -> In b (OW ++ LB)) -> ACEIL <= lo -> lo <= SP - F ->
  aclient_addr L' SP a -> ~ (SP - F <= a < SP).
Proof.
  intros Σ OW LB m L' SP lo F a HEAP HL CEIL LO Ha.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _ & _). unfold SEGTOP_A in C1.
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - lia.
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP (HL b Hb)) as (_ & _ & _ & B3 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma acl_off_block : forall Σ OW LB m (L' : list block) SP lo (blk : block) a,
  AHEAP Σ OW LB m -> In blk (OW ++ LB) -> (forall b, In b L' -> In b (OW ++ LB) /\ blk_id b <> blk_id blk) ->
  ACEIL <= lo -> lo <= SP ->
  aclient_addr L' SP a -> ~ (blk_addr blk <= a < blk_addr blk + blk_size blk).
Proof.
  intros Σ OW LB m L' SP lo blk a HEAP HIN HL CEIL LO Ha.
  pose proof (AH_range_gen _ _ _ _ blk HEAP HIN) as (B0 & _ & _ & B3 & B4).
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - lia.
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - destruct (HL b Hb) as [Hb' NE]. pose proof (AH_disjoint_gen _ _ _ _ b blk HEAP Hb' HIN NE) as DJ. lia.
Qed.

(* [comment removed for export] *)
Lemma acl_outside1 : forall Σ OW LB m (L' : list block) SP lo F a,
  AHEAP Σ OW LB m -> (forall b, In b L' -> In b (OW ++ LB)) -> ACEIL <= lo -> lo <= SP - F ->
  aclient_addr L' SP a -> outside [(SP - F, SP)] a.
Proof.
  intros Σ OW LB m L' SP lo F a HEAP HL CEIL LO Ha. cbn [outside fst snd]. split; [| exact I].
  exact (acl_off_frame Σ OW LB m L' SP lo F a HEAP HL CEIL LO Ha).
Qed.

Lemma acl_outside2 : forall Σ OW LB m (L' : list block) SP lo F (blk : block) a,
  AHEAP Σ OW LB m -> In blk (OW ++ LB) -> (forall b, In b L' -> In b (OW ++ LB) /\ blk_id b <> blk_id blk) ->
  ACEIL <= lo -> lo <= SP - F -> 0 <= F ->
  aclient_addr L' SP a -> outside [(SP - F, SP); (blk_addr blk, blk_addr blk + blk_size blk)] a.
Proof.
  intros Σ OW LB m L' SP lo F blk a HEAP HIN HL CEIL LO F0 Ha. cbn [outside fst snd]. split; [| split; [| exact I]].
  - exact (acl_off_frame Σ OW LB m L' SP lo F a HEAP (fun b Hb => proj1 (HL b Hb)) CEIL LO Ha).
  - exact (acl_off_block Σ OW LB m L' SP lo blk a HEAP HIN HL CEIL ltac:(lia) Ha).
Qed.

(* [comment removed for export] *)
Lemma acl_outside3 : forall Σ OW LB m (L' : list block) SP lo F (b1 b2 : block) a,
  AHEAP Σ OW LB m -> In b1 (OW ++ LB) -> In b2 (OW ++ LB) ->
  (forall b, In b L' -> In b (OW ++ LB) /\ blk_id b <> blk_id b1 /\ blk_id b <> blk_id b2) ->
  ACEIL <= lo -> lo <= SP - F -> 0 <= F ->
  aclient_addr L' SP a ->
  outside [(SP - F, SP); (blk_addr b1, blk_addr b1 + blk_size b1); (blk_addr b2, blk_addr b2 + blk_size b2)] a.
Proof.
  intros Σ OW LB m L' SP lo F b1 b2 a HEAP H1 H2 HL CEIL LO F0 Ha. cbn [outside fst snd]. split; [| split; [| split; [| exact I]]].
  - exact (acl_off_frame Σ OW LB m L' SP lo F a HEAP (fun b Hb => proj1 (HL b Hb)) CEIL LO Ha).
  - exact (acl_off_block Σ OW LB m L' SP lo b1 a HEAP H1 (fun b Hb => match HL b Hb with conj A (conj B _) => conj A B end) CEIL ltac:(lia) Ha).
  - exact (acl_off_block Σ OW LB m L' SP lo b2 a HEAP H2 (fun b Hb => match HL b Hb with conj A (conj _ C) => conj A C end) CEIL ltac:(lia) Ha).
Qed.

(* [comment removed for export] *)
Lemma acl_off_fresh : forall Σ Σ' OW LB m m' SP lo (p : bptr) A n a,
  AHEAP Σ OW LB m -> AHEAP Σ' ((p, A, n) :: OW) LB m' -> ~ In p (map blk_id (OW ++ LB)) ->
  ACEIL <= lo -> lo <= SP ->
  aclient_addr (OW ++ LB) SP a -> ~ (A <= a < A + n).
Proof.
  intros Σ Σ' OW LB m m' SP lo p A n a HEAP HEAP' Hp CEIL LO Ha HA.
  pose proof (@AH_range_gen AR _ _ _ _ (p, A, n) HEAP' (or_introl eq_refl)) as (B0 & _ & _ & B3 & B4). cbn [blk_addr blk_size fst snd] in B0, B3, B4.
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - lia.
  - eapply (blk_not_static _ ((p, A, n) :: OW) LB m' (p, A, n) a HEAP' (or_introl eq_refl)); [cbn; lia | exact Ha].
  - assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; exact Hb).
    pose proof (@AH_disjoint_gen AR _ _ _ _ b (p, A, n) HEAP' (or_intror Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. lia.
Qed.

End WithRT.
