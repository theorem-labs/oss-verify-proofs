(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_W5_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition rm_nth {X} (j : nat) (l : list X) : list X := firstn j l ++ skipn (S j) l.

Lemma nth_split3 : forall {X} j (l : list X) x, nth_error l j = Some x -> l = firstn j l ++ x :: skipn (S j) l.
Proof.
  intros X j l x H. pose proof (nth_error_lt _ _ _ H) as Hj.
  rewrite <- (firstn_skipn j l) at 1. f_equal.
  destruct (skipn j l) as [|y t] eqn:Es.
  - exfalso. apply (f_equal (@length X)) in Es. rewrite length_skipn in Es. cbn in Es. lia.
  - pose proof (nth_error_skipn j l 0) as E0. rewrite Nat.add_0_r, H, Es in E0. cbn in E0. injection E0 as ->. f_equal.
    change (S j) with (1 + j)%nat. rewrite <- skipn_skipn, Es. reflexivity.
Qed.

Lemma rm_nth_map : forall {X Y} (g : X -> Y) j (l : list X), map g (rm_nth j l) = rm_nth j (map g l).
Proof. intros X Y g j l. unfold rm_nth. rewrite map_app, firstn_map, skipn_map. reflexivity. Qed.

Lemma rm_nth_length : forall {X} j (l : list X) x, nth_error l j = Some x -> length (rm_nth j l) = (length l - 1)%nat.
Proof.
  intros X j l x H. pose proof (nth_error_lt _ _ _ H) as Hj. unfold rm_nth. rewrite length_app, length_firstn, length_skipn. lia.
Qed.

Lemma rm_nth_nth : forall {X} j (l : list X) x n, nth_error l j = Some x ->
  nth_error (rm_nth j l) n = if Nat.ltb n j then nth_error l n else nth_error l (S n).
Proof.
  intros X j l x n H. pose proof (nth_error_lt _ _ _ H) as Hj. unfold rm_nth.
  destruct (Nat.lt_ge_cases n j) as [Hn|Hn].
  - rewrite nth_error_app1 by (rewrite length_firstn; lia). rewrite nth_error_firstn. replace (n <? j)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
  - rewrite nth_error_app2 by (rewrite length_firstn; lia). replace (n <? j)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    rewrite length_firstn, nth_error_skipn. f_equal. lia.
Qed.

Lemma rm_nth_In : forall {X} j (l : list X) x y, nth_error l j = Some x -> In y (rm_nth j l) -> In y l.
Proof.
  intros X j l x y H Hy. rewrite (nth_split3 j l x H). unfold rm_nth in Hy. apply in_app_or in Hy. apply in_or_app.
  destruct Hy as [Hy|Hy]; [left; exact Hy| right; right; exact Hy].
Qed.

Lemma rm_nth_In_other : forall {X} j (l : list X) x y, nth_error l j = Some x -> In y l -> y <> x -> In y (rm_nth j l).
Proof.
  intros X j l x y H Hy NE. rewrite (nth_split3 j l x H) in Hy. unfold rm_nth. apply in_app_or in Hy. apply in_or_app.
  destruct Hy as [Hy|[Hy|Hy]]; [left; exact Hy| exfalso; exact (NE (eq_sym Hy))| right; exact Hy].
Qed.

Lemma rm_nth_NoDup : forall {X} j (l : list X) x, NoDup l -> nth_error l j = Some x -> NoDup (rm_nth j l).
Proof.
  intros X j l x ND H. rewrite NoDup_ListNoDup in ND |- *. rewrite (nth_split3 j l x H) in ND. unfold rm_nth. exact (NoDup_remove_1 _ _ _ ND).
Qed.

Lemma NoDup_nth_inj : forall {X} (l : list X) i j x, NoDup l -> nth_error l i = Some x -> nth_error l j = Some x -> i = j.
Proof.
  intros X l i j x ND Hi Hj. rewrite NoDup_ListNoDup in ND. apply (proj1 (List.NoDup_nth_error l) ND i j); [exact (nth_error_lt _ _ _ Hi)| congruence].
Qed.

(* [comment removed for export] *)
Lemma slot_unowned_zero : forall fs fn ks strs (i : Z) (isf : bool), slots_ok fs fn ks strs -> length fs = 16%nat -> length fn = 16%nat ->
  0 <= i < 16 -> ~ In (i, isf) ks -> slot_word fs fn (i, isf) = Some (Z_to_bv 64 0).
Proof.
  intros fs fn ks strs i isf (ND & LEN & RNG & SL & NUL & NDS) L1 L2 Hi NI.
  destruct (nth_error (if isf then fn else fs) (Z.to_nat i)) as [w|] eqn:Hw.
  - unfold slot_word. cbn [fst snd]. rewrite Hw. f_equal. apply (NUL (i, isf) w); [cbn; lia| unfold slot_word; cbn [fst snd]; exact Hw| exact NI].
  - exfalso. apply nth_error_None in Hw. destruct isf; lia.
Qed.

(* [comment removed for export] *)
Lemma slot_owned : forall fs fn ks strs ik, slots_ok fs fn ks strs -> In ik ks ->
  exists j b, nth_error ks j = Some ik /\ nth_error strs j = Some b /\ slot_word fs fn ik = Some (Z_to_bv 64 (blk_addr b)) /\ 0 < blk_addr b /\ 0 < blk_size b.
Proof.
  intros fs fn ks strs ik (ND & LEN & RNG & SL & NUL & NDS) Hin.
  destruct (In_nth_error _ _ Hin) as [j Hj]. pose proof (nth_error_lt _ _ _ Hj) as Lj.
  destruct (nth_error strs j) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
  exists j, b. destruct (SL j ik b Hj Hb) as (W & A & SZ). auto 6.
Qed.

(* [comment removed for export] *)
Lemma slot_dec : forall (ik : Z * bool) (ks : list (Z * bool)), {In ik ks} + {~ In ik ks}.
Proof.
  intros ik ks. apply In_dec. intros [a b] [c d]. destruct (Z.eq_dec a c) as [->|NE]; [| right; congruence].
  destruct (Bool.bool_dec b d) as [->|NE]; [left; reflexivity| right; congruence].
Qed.

(* [comment removed for export] *)
Definition zero_slot (fs fn : list word) (ik : Z * bool) : list word * list word :=
  if snd ik then (fs, upd fn (Z.to_nat (fst ik)) (Z_to_bv 64 0)) else (upd fs (Z.to_nat (fst ik)) (Z_to_bv 64 0), fn).

Lemma slot_free : forall fs fn ks strs j ik b, slots_ok fs fn ks strs -> length fs = 16%nat -> length fn = 16%nat ->
  nth_error ks j = Some ik -> nth_error strs j = Some b ->
  slots_ok (fst (zero_slot fs fn ik)) (snd (zero_slot fs fn ik)) (rm_nth j ks) (rm_nth j strs).
Proof.
  intros fs fn ks strs j ik b (ND & LEN & RNG & SL & NUL & NDS) L1 L2 Hk Hs.
  pose proof (nth_error_lt _ _ _ Hk) as Lj. pose proof (RNG _ (nth_error_In _ _ Hk)) as Ri.
  assert (SW : forall ik', ik' <> ik -> 0 <= fst ik' < 16 -> slot_word (fst (zero_slot fs fn ik)) (snd (zero_slot fs fn ik)) ik' = slot_word fs fn ik').
  { intros ik' NE Hi'. destruct ik as [i f], ik' as [i' f']. unfold slot_word, zero_slot. cbn [fst snd] in *.
    destruct f, f'; cbn [fst snd]; try reflexivity; rewrite nth_error_upd_other; try reflexivity; intros EQ; apply NE; f_equal; lia. }
  assert (SW0 : slot_word (fst (zero_slot fs fn ik)) (snd (zero_slot fs fn ik)) ik = Some (Z_to_bv 64 0)).
  { destruct ik as [i f]. unfold slot_word, zero_slot. cbn [fst snd] in *. destruct f; cbn [fst snd]; apply nth_error_upd_same; lia. }
  assert (OTHER : forall n ik', nth_error (rm_nth j ks) n = Some ik' -> ik' <> ik).
  { intros n ik' Hn ->. rewrite (rm_nth_nth j ks _ n Hk) in Hn.
    destruct (Nat.lt_ge_cases n j) as [Hn'|Hn'];
      [replace (n <? j)%nat with true in Hn by (symmetry; apply Nat.ltb_lt; lia)| replace (n <? j)%nat with false in Hn by (symmetry; apply Nat.ltb_ge; lia)];
      pose proof (NoDup_nth_inj _ _ _ _ ND Hn Hk); lia. }
  split; [exact (rm_nth_NoDup j ks _ ND Hk)|].
  split; [rewrite (rm_nth_length j ks _ Hk), (rm_nth_length j strs _ Hs); lia|].
  split; [intros ik' Hin; apply RNG; eapply rm_nth_In; [exact Hk| exact Hin]|].
  split.
  - intros n ik' b' Hn Hb'. pose proof (OTHER n ik' Hn) as NE.
    assert (R' : 0 <= fst ik' < 16) by (apply RNG; eapply rm_nth_In; [exact Hk| eapply nth_error_In; exact Hn]).
    rewrite (SW ik' NE R').
    rewrite (rm_nth_nth j ks _ n Hk) in Hn. rewrite (rm_nth_nth j strs _ n Hs) in Hb'.
    destruct (n <? j)%nat; exact (SL _ _ _ Hn Hb').
  - split.
    { intros ik' w Hi' Hw NI'. destruct (slot_dec ik' [ik]) as [[<-|[]]|NE1].
      + rewrite SW0 in Hw. congruence.
      + assert (NE : ik' <> ik) by (intros ->; apply NE1; left; reflexivity).
        rewrite (SW ik' NE Hi') in Hw. apply (NUL ik' w Hi' Hw). intros Hin. apply NI'. eapply rm_nth_In_other; [exact Hk| exact Hin| exact NE]. }
    rewrite rm_nth_map. rewrite <- NoDup_ListNoDup. eapply rm_nth_NoDup; [rewrite NoDup_ListNoDup; exact NDS| exact (map_nth_error blk_id _ _ Hs)].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rm_nth_In_iff : forall {X} j (l : list X) x y, List.NoDup l -> nth_error l j = Some x -> In y (rm_nth j l) <-> In y l /\ y <> x.
Proof.
  intros X j l x y ND H. split.
  - intros Hy. split; [exact (rm_nth_In j l x y H Hy)|]. intros ->.
    pose proof ND as ND'. rewrite (nth_split3 j l x H) in ND'. pose proof (List.NoDup_remove_2 _ _ _ ND') as NI. apply NI. unfold rm_nth in Hy. exact Hy.
  - intros [Hy NE]. exact (rm_nth_In_other j l x y H Hy NE).
Qed.

Lemma nodup_map_In_eq : forall {X Y} (g : X -> Y) (l : list X) x y, List.NoDup (map g l) -> In x l -> In y l -> g x = g y -> x = y.
Proof.
  intros X Y g l x y ND Hx Hy E. induction l as [|z l IH]; [destruct Hx|]. cbn [map] in ND. inversion ND as [|z' l' NI ND2]; subst.
  destruct Hx as [->|Hx], Hy as [->|Hy]; [reflexivity| | | exact (IH ND2 Hx Hy)].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma rm_nth_id_notin : forall {X Y} (g : X -> Y) j (l : list X) x y, List.NoDup (map g l) -> nth_error l j = Some x -> In y (rm_nth j l) -> g y <> g x.
Proof.
  intros X Y g j l x y ND H Hy. apply (in_map g) in Hy. rewrite rm_nth_map in Hy.
  exact (proj2 (proj1 (rm_nth_In_iff j (map g l) (g x) (g y) ND (map_nth_error g j l H)) Hy)).
Qed.

(* [comment removed for export] *)
Lemma cremove_In_iff : forall (L1 : @clist bptr) idx (p : bptr) nm0 q nm, List.NoDup (map fst L1) -> nth_error L1 idx = Some (p, nm0) ->
  In (q, nm) (cremove idx L1) <-> In (q, nm) L1 /\ q <> p.
Proof.
  intros L1 idx p nm0 q nm ND HN. destruct (cremove_split L1 idx _ HN) as (l1 & l2 & EL & _ & EC). rewrite EC. split.
  - intros Hin. split; [rewrite EL; apply in_app_or in Hin; apply in_or_app; destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; exact Hin]|].
    intros ->. rewrite EL, map_app in ND. cbn [map fst] in ND. pose proof (List.NoDup_remove_2 _ _ _ ND) as NI. apply NI.
    rewrite <- map_app. apply in_map_iff. exists (p, nm). split; [reflexivity| exact Hin].
  - intros [Hin NE]. rewrite <- EC. exact (cremove_keep L1 idx p nm0 q nm HN Hin NE).
Qed.

(* [comment removed for export] *)
Lemma blk_eta : forall b : block, (blk_id b, blk_addr b, blk_size b) = b.
Proof. intros [[p A] n]. reflexivity. Qed.

Lemma clr_LB_step : forall (LBall LB1 strs strs1 : list block) j bj,
  List.NoDup (map blk_id LB1) -> List.NoDup (map blk_id strs1) -> nth_error strs1 j = Some bj ->
  (forall b, In b strs1 -> In b strs) -> In bj LB1 ->
  (forall b, In b LB1 <-> In b LBall /\ (In b strs -> In b strs1)) ->
  forall b, In b (lb_remove (blk_id bj) LB1) <-> In b LBall /\ (In b strs -> In b (rm_nth j strs1)).
Proof.
  intros LBall LB1 strs strs1 j bj NDB NDS Hs SUB INB HLB b. rewrite lb_remove_In, HLB.
  assert (NDS' : List.NoDup strs1) by (exact (List.NoDup_map_inv _ _ NDS)).
  pose proof (rm_nth_In_iff j strs1 bj b NDS' Hs) as RM.
  split.
  - intros [[H1 H2] NE]. split; [exact H1|]. intros H3. apply RM. split; [exact (H2 H3)|]. intros ->. exact (NE eq_refl).
  - intros [H1 H2].
    assert (H1' : In b LBall /\ (In b strs -> In b strs1)) by (split; [exact H1| intros H3; exact (rm_nth_In j strs1 bj b Hs (H2 H3))]).
    split; [exact H1'|]. intros E. assert (INb1 : In b LB1) by (apply HLB; exact H1').
    pose proof (nodup_map_In_eq blk_id LB1 b bj NDB INb1 INB E) as ->.
    exact (rm_nth_id_notin blk_id j strs1 bj bj NDS Hs (H2 (SUB _ (nth_error_In _ _ Hs))) eq_refl).
Qed.

Lemma clr_L_step : forall (L L1 : @clist bptr) (strs strs1 : list block) j bj idx,
  List.NoDup (map fst L1) -> List.NoDup (map blk_id strs1) -> nth_error strs1 j = Some bj -> (forall b, In b strs1 -> In b strs) ->
  nth_error L1 idx = Some (blk_id bj, blk_size bj) ->
  (forall q nm, In (q, nm) L1 <-> In (q, nm) L /\ (In q (map blk_id strs) -> In q (map blk_id strs1))) ->
  forall q nm, In (q, nm) (cremove idx L1) <-> In (q, nm) L /\ (In q (map blk_id strs) -> In q (map blk_id (rm_nth j strs1))).
Proof.
  intros L L1 strs strs1 j bj idx NDL NDS Hs SUB HN HL q nm. rewrite (cremove_In_iff L1 idx _ _ q nm NDL HN), HL, rm_nth_map.
  pose proof (rm_nth_In_iff j (map blk_id strs1) (blk_id bj) q NDS (map_nth_error blk_id j strs1 Hs)) as RM.
  split.
  - intros [[H1 H2] NE]. split; [exact H1|]. intros H3. apply RM. split; [exact (H2 H3)| exact NE].
  - intros [H1 H2]. split; [split; [exact H1| intros H3; exact (proj1 (proj1 RM (H2 H3)))]|].
    intros ->. exact (proj2 (proj1 RM (H2 (in_map blk_id strs bj (SUB _ (nth_error_In _ _ Hs))))) eq_refl).
Qed.

(* [comment removed for export] *)
Lemma clr_own_step : forall (LB1 strs1 : list block) (L1 : @clist bptr) j bj idx,
  List.NoDup (map blk_id strs1) -> nth_error strs1 j = Some bj -> nth_error L1 idx = Some (blk_id bj, blk_size bj) ->
  Forall (fun b => cown LB1 L1 (blk_id b) (blk_addr b) (blk_size b) (blk_size b)) strs1 ->
  Forall (fun b => cown (lb_remove (blk_id bj) LB1) (cremove idx L1) (blk_id b) (blk_addr b) (blk_size b) (blk_size b)) (rm_nth j strs1).
Proof.
  intros LB1 strs1 L1 j bj idx NDS Hs HN OWN. apply List.Forall_forall. intros b Hb.
  pose proof (proj1 (List.Forall_forall _ _) OWN b (rm_nth_In j strs1 bj b Hs Hb)) as O. cbv beta in O.
  eapply cown_remove; [exact O| exact HN| exact (rm_nth_id_notin blk_id j strs1 bj b NDS Hs Hb)].
Qed.
End WithCeiling0.
