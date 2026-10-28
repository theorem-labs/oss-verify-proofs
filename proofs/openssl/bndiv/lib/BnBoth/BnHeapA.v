(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_kit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bptr_eqb_refl : forall p, bptr_eqb p p = true.
Proof. intros [[r o] z]. unfold bptr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, !Z.eqb_refl. reflexivity. Qed.

Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true -> p = q.
Proof.
  intros [[r o] z] [[r' o'] z'] H. unfold bptr_eqb, aptr_eqb in H. cbn in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
  apply N.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. unfold lb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
  rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
  - rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
  - exfalso. destruct (bptr_eqb (blk_id b) p) eqn:E.
    + apply H. left. apply bptr_eqb_eq in E. exact E.
    + apply N. cbn [negb]. exact I.
Qed.

Lemma lb_remove_head : forall b LB, List.NoDup (map blk_id (b :: LB)) -> lb_remove (blk_id b) (b :: LB) = LB.
Proof.
  intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  unfold lb_remove. rewrite filter_cons, bptr_eqb_refl. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
  apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.


Lemma bptr_eqb_neq : forall p q, p <> q -> bptr_eqb p q = false.
Proof. intros p q H. destruct (bptr_eqb p q) eqn:E; [|reflexivity]. exfalso. apply H. apply bptr_eqb_eq. exact E. Qed.

Lemma lb_remove_cons : forall p b L,
  lb_remove p (b :: L) = if bptr_eqb (blk_id b) p then lb_remove p L else b :: lb_remove p L.
Proof.
  intros p b L. unfold lb_remove. rewrite filter_cons. destruct (bptr_eqb (blk_id b) p); cbn [negb];
    destruct (decide _) as [Y|N]; try reflexivity; [exfalso; exact Y| exfalso; apply N; exact I].
Qed.

Lemma lb_remove_In : forall p L b, In b (lb_remove p L) <-> In b L /\ blk_id b <> p.
Proof.
  intros p L b. induction L as [|c L IH]; [cbn; tauto|].
  rewrite lb_remove_cons. destruct (bptr_eqb (blk_id c) p) eqn:E.
  - apply bptr_eqb_eq in E. rewrite IH. cbn [In]. split; [intros [H N]; split; [right; exact H| exact N]|].
    intros [[<-|H] N]; [contradiction| split; assumption].
  - cbn [In]. rewrite IH. split; [intros [<-|[H N]]; [split; [left; reflexivity|]| split; [right; exact H| exact N]]|].
    + intros E2. rewrite E2, bptr_eqb_refl in E. discriminate.
    + intros [[<-|H] N]; [left; reflexivity| right; split; assumption].
Qed.

Lemma lb_remove_app : forall p L1 L2, lb_remove p (L1 ++ L2) = lb_remove p L1 ++ lb_remove p L2.
Proof.
  intros p L1 L2. induction L1 as [|c L1 IH]; [reflexivity|].
  cbn [app]. rewrite !lb_remove_cons. destruct (bptr_eqb (blk_id c) p); [exact IH| cbn [app]; rewrite IH; reflexivity].
Qed.

Lemma lb_remove_incl : forall p L b, In b (lb_remove p L) -> In b L.
Proof. intros p L b H. apply lb_remove_In in H. tauto. Qed.

(* [comment removed for export] *)
Lemma lb_remove_length : forall p (L : list block), List.NoDup (map blk_id L) -> In p (map blk_id L) ->
  S (length (lb_remove p L)) = length L.
Proof.
  intros p L. induction L as [|b L IH]; intros ND Hin; [destruct Hin|].
  cbn [map] in ND. apply NoDup_cons_iff in ND as [N1 N2]. rewrite lb_remove_cons. destruct (bptr_eqb (blk_id b) p) eqn:E.
  - apply bptr_eqb_eq in E. subst p. rewrite (lb_remove_notin _ _ N1). reflexivity.
  - cbn [length]. f_equal. apply IH; [exact N2|]. destruct Hin as [Hin|Hin]; [|exact Hin].
    rewrite Hin, bptr_eqb_refl in E. discriminate.
Qed.

Lemma lb_remove_app_l : forall p OW LB, List.NoDup (map blk_id (OW ++ LB)) -> In p (map blk_id OW) ->
  lb_remove p (OW ++ LB) = lb_remove p OW ++ LB.
Proof.
  intros p OW LB ND Hin. rewrite lb_remove_app. f_equal. apply lb_remove_notin.
  rewrite map_app in ND. intros H. revert ND Hin H. generalize (map blk_id OW) (map blk_id LB). clear.
  intros l1 l2 ND H1 H2. induction l1 as [|x l1 IH]; [contradiction|].
  cbn [app] in ND. apply NoDup_cons_iff in ND. destruct ND as [Hx ND]. destruct H1 as [->|H1]; [|auto].
  apply Hx. apply in_or_app. right. exact H2.
Qed.

Lemma nodup_app_l : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof. intros A l1 l2 H. induction l1 as [|x l1 IH]; [constructor|]. cbn in H. apply NoDup_cons_iff in H. destruct H as [Hx H].
  constructor; [intros Hin; apply Hx; apply in_or_app; left; exact Hin| auto]. Qed.

Lemma nodup_app_r : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. intros A l1 l2 H. induction l1 as [|x l1 IH]; [exact H|]. cbn in H. apply NoDup_cons_iff in H. tauto. Qed.

Lemma nodup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros A l1 l2 x H H1 H2. induction l1 as [|y l1 IH]; [contradiction|]. cbn in H. apply NoDup_cons_iff in H. destruct H as [Hy H].
  destruct H1 as [->|H1]; [apply Hy; apply in_or_app; right; exact H2| auto].
Qed.


(* [comment removed for export] *)
Lemma AH_addr_unique : forall (OW : list block) p A n A' n',
  List.NoDup (map blk_id OW) -> In (p, A, n) OW -> In (p, A', n') OW -> A = A' /\ n = n'.
Proof.
  intros OW p A n A' n' ND H1 H2. induction OW as [|c OW IH]; [contradiction|].
  cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [Hc ND].
  destruct H1 as [->|H1], H2 as [E|H2].
  - inversion E. auto.
  - exfalso. apply Hc. apply (in_map blk_id) in H2. exact H2.
  - subst c. exfalso. apply Hc. apply (in_map blk_id) in H1. exact H1.
  - auto.
Qed.


Lemma lb_remove_In_map : forall p (L : list block) b, In b L -> blk_id b <> p -> In b (lb_remove p L).
Proof. intros p L b H N. apply lb_remove_In. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation SP0 := (@ar_SP0 AR).

Definition ACEIL : Z := SP0 - STACK_WIN.

Definition blk_okA (b : block) : Prop := blk_addr b mod 16 = 0 /\ 0 < blk_size b.

Definition AHEAP (Σ : rts RT) (OW LB : list block) (m : mem) : Prop :=
  ART RT Σ m /\ rt_sp0 RT Σ = SP0 /\ rt_frames RT Σ = [] /\ Permutation (rt_live RT Σ) (map blk_an (OW ++ LB))
  /\ List.NoDup (map blk_id (OW ++ LB)) /\ Forall blk_okA OW /\ Forall (fun b => 0 < blk_size b) LB.

(* [comment removed for export] *)
Definition ablock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= ACEIL /\ (A + n <= 65536 \/ 12570624 <= A).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ablock_range_gen (A n : Z) : Prop :=
  0 < A /\ True /\ 0 <= n /\ A + n <= ACEIL /\ (A + n <= 65536 \/ 12570624 <= A).

Lemma AH_art : forall Σ OW LB m, AHEAP Σ OW LB m -> ART RT Σ m.
Proof. intros Σ OW LB m H. exact (proj1 H). Qed.

Lemma AH_ceil : forall Σ OW LB m, AHEAP Σ OW LB m -> SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP.
Proof.
  intros Σ OW LB m (HA & HS & _). pose proof (af_sp0_range RT AF Σ m HA) as R. pose proof (af_sp0_win RT AF Σ m HA) as R2.
  unfold ACEIL, SEGTOP_A, STACK_WIN, USTACK_TOP, SHHI in *. lia.
Qed.

Lemma AH_nodup : forall Σ OW LB m, AHEAP Σ OW LB m -> List.NoDup (map blk_id (OW ++ LB)).
Proof. intros Σ OW LB m H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.

Lemma AH_nodup_l : forall Σ OW LB m, AHEAP Σ OW LB m -> List.NoDup (map blk_id OW).
Proof. intros Σ OW LB m H. apply AH_nodup in H. rewrite map_app in H. eapply nodup_app_l; exact H. Qed.

Lemma AH_live : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) -> In (blk_addr b, blk_size b) (rt_live RT Σ).
Proof.
  intros Σ OW LB m b (_ & _ & _ & HL & _) Hin. eapply Permutation_in; [symmetry; exact HL|].
  apply in_map_iff. exists b. split; [reflexivity | exact Hin].
Qed.

(* [comment removed for export] *)
Lemma AH_same : forall Σ OW LB m m', AHEAP Σ OW LB m -> ART RT Σ m' -> AHEAP Σ OW LB m'.
Proof. intros Σ OW LB m m' (_ & H) HA. exact (conj HA H). Qed.

Lemma AH_frames : forall Σ OW LB m, AHEAP Σ OW LB m -> rt_frames RT Σ = [].
Proof. intros Σ OW LB m H. exact (proj1 (proj2 (proj2 H))). Qed.
Lemma AH_sp0 : forall Σ OW LB m, AHEAP Σ OW LB m -> rt_sp0 RT Σ = SP0.
Proof. intros Σ OW LB m H. exact (proj1 (proj2 H)). Qed.
Lemma AH_live_len : forall Σ OW LB m, AHEAP Σ OW LB m -> length (rt_live RT Σ) = length (OW ++ LB).
Proof. intros Σ OW LB m (_ & _ & _ & HL & _). rewrite (Permutation_length HL), length_map. reflexivity. Qed.
Lemma AH_incl : forall Σ OW LB m, AHEAP Σ OW LB m -> forall e, In e (map blk_an (OW ++ LB)) -> In e (rt_live RT Σ).
Proof. intros Σ OW LB m (_ & _ & _ & HL & _) e He. eapply Permutation_in; [symmetry; exact HL | exact He]. Qed.

(* [comment removed for export] *)
Lemma AH_agree : forall Σ OW LB m0 SP m m', AHEAP Σ OW LB m0 -> rt_pres (rt_live RT Σ) [] SP m m' -> agree_on (aclient_addr (OW ++ LB) SP) m m'.
Proof. intros Σ OW LB m0 SP m m' H P. exact (agree_of_rt_pres_incl _ _ SP m m' (AH_incl _ _ _ _ H) P). Qed.
Lemma AH_agree_ex : forall Σ OW LB m0 SP d n m m', AHEAP Σ OW LB m0 -> rt_pres_ex (rt_live RT Σ) [] SP d n m m' ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (d <= a < d + n)) m m'.
Proof. intros Σ OW LB m0 SP d n m m' H P. exact (agree_of_rt_pres_ex_incl _ _ SP d n m m' (AH_incl _ _ _ _ H) P). Qed.
Lemma AH_agree_fp : forall Σ OW LB m0 SP W m m', AHEAP Σ OW LB m0 -> rt_pres_fp (rt_live RT Σ) [] SP W m m' ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ outside W a) m m'.
Proof. intros Σ OW LB m0 SP W m m' H P. exact (agree_of_rt_pres_fp_incl _ _ SP W m m' (AH_incl _ _ _ _ H) P). Qed.

Lemma AH_okA : forall Σ OW LB m p A n, AHEAP Σ OW LB m -> In (p, A, n) OW -> A mod 16 = 0 /\ 0 < n.
Proof.
  intros Σ OW LB m p A n (_ & _ & _ & _ & _ & HF & _) Hin. exact (proj1 (Forall_forall _ _) HF (p, A, n) Hin).
Qed.

Lemma AH_pos_gen_ : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) -> 0 < blk_size b.
Proof.
  intros Σ OW LB m b (_ & _ & _ & _ & _ & HF1 & HF2) Hin. apply in_app_or in Hin as [Hin|Hin].
  - exact (proj2 (proj1 (Forall_forall _ _) HF1 b Hin)).
  - exact (proj1 (Forall_forall _ _) HF2 b Hin).
Qed.

Lemma AH_range : forall Σ OW LB m p A n, AHEAP Σ OW LB m -> In (p, A, n) OW -> ablock_range A n.
Proof.
  intros Σ OW LB m p A n H Hin. pose proof (AH_okA _ _ _ _ _ _ _ H Hin) as (H16 & Hn).
  pose proof (AH_live _ _ _ _ (p, A, n) H (in_or_app _ _ _ (or_introl Hin))) as HL. cbn in HL.
  destruct H as (HA & HS & _).
  destruct (af_live_range RT AF Σ m A n HA HL) as (R1 & R2 & R3). unfold ablock_range, ACEIL. rewrite <- HS.
  split; [exact R1|]. split; [exact H16|]. split; [lia|]. split; [exact R2 | unfold SEGTOP_A in R3; exact R3].
Qed.

Lemma AH_range_gen : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) -> ablock_range_gen (blk_addr b) (blk_size b).
Proof.
  intros Σ OW LB m b H Hin. pose proof (AH_pos_gen_ Σ OW LB m b H Hin) as Hn.
  pose proof (AH_live _ _ _ _ b H Hin) as HL. destruct H as (HA & HS & _).
  destruct (af_live_range RT AF Σ m _ _ HA HL) as (R1 & R2 & R3). unfold ablock_range_gen, ACEIL. rewrite <- HS.
  split; [exact R1|]. split; [exact I|]. split; [lia|]. split; [exact R2 | unfold SEGTOP_A in R3; exact R3].
Qed.

(* [comment removed for export] *)
Lemma AH_offsh : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) ->
  blk_addr b + blk_size b <= SHLO \/ SHHI <= blk_addr b.
Proof.
  intros Σ OW LB m b H Hin. pose proof (AH_live _ _ _ _ b H Hin) as HL. destruct H as (HA & _).
  destruct (af_live_offshadow RT AF Σ m _ _ HA HL) as [R|R]; unfold SHLO, SHHI; [left | right]; lia.
Qed.

(* [comment removed for export] *)
Lemma AH_acc : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) ->
  wr_at bsegs m (blk_addr b) (blk_size b) /\ acc bsegs m (blk_addr b) (blk_size b).
Proof.
  intros Σ OW LB m b H Hin. pose proof (AH_live _ _ _ _ b H Hin) as HL. destruct H as (HA & _).
  exact (af_acc_live RT AF Σ m _ _ HA HL).
Qed.

Lemma in_split_ne : forall (L : list block) b1 b2, In b1 L -> In b2 L -> b1 <> b2 ->
  exists l1 l2, L = l1 ++ b1 :: l2 /\ In b2 (l1 ++ l2).
Proof.
  intros L b1 b2 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & ->). exists l1, l2. split; [reflexivity|].
  apply in_app_or in H2. apply in_or_app. destruct H2 as [H2|[H2|H2]]; [left; exact H2 | congruence | right; exact H2].
Qed.

Lemma AH_disjoint_gen : forall Σ OW LB m b1 b2, AHEAP Σ OW LB m -> In b1 (OW ++ LB) -> In b2 (OW ++ LB) -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros Σ OW LB m b1 b2 H H1 H2 NE. assert (NEb : b1 <> b2) by congruence.
  destruct (in_split_ne _ _ _ H1 H2 NEb) as (L1 & L2 & E & Hin).
  pose proof (AH_live _ _ _ _ b1 H H1) as HL1.
  destruct H as (HA & _ & _ & HL & _).
  destruct (in_split _ _ HL1) as (l1 & l2 & El).
  apply (af_live_disj RT AF Σ m (blk_addr b1) (blk_size b1) (blk_addr b2) (blk_size b2) l1 l2 HA El).
  rewrite El, E, map_app in HL. cbn [map] in HL. change (blk_an b1) with (blk_addr b1, blk_size b1) in HL.
  apply Permutation_app_inv in HL. eapply Permutation_in; [symmetry; exact HL|].
  rewrite <- map_app. apply in_map_iff. exists b2. split; [reflexivity | exact Hin].
Qed.

Lemma AH_disjoint : forall Σ OW LB m p A n p' A' n',
  AHEAP Σ OW LB m -> In (p, A, n) OW -> In (p', A', n') OW -> p <> p' -> A + n <= A' \/ A' + n' <= A.
Proof.
  intros Σ OW LB m p A n p' A' n' H H1 H2 NE.
  exact (AH_disjoint_gen Σ OW LB m (p, A, n) (p', A', n') H (in_or_app _ _ _ (or_introl H1)) (in_or_app _ _ _ (or_introl H2)) NE).
Qed.

Lemma AH_pos_gen : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) -> 0 < blk_size b.
Proof.
  intros Σ OW LB m b (_ & _ & _ & _ & _ & HF1 & HF2) Hin. apply in_app_or in Hin as [Hin|Hin].
  - exact (proj2 (proj1 (Forall_forall _ _) HF1 b Hin)).
  - exact (proj1 (Forall_forall _ _) HF2 b Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma AH_malloc : forall Σ Σ' OW LB m m' p A n,
  AHEAP Σ OW LB m -> ART RT Σ' m' -> rt_live RT Σ' = (A, n) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> A mod 16 = 0 -> 0 < n -> ~ In p (map blk_id (OW ++ LB)) ->
  AHEAP Σ' ((p, A, n) :: OW) LB m'.
Proof.
  intros Σ Σ' OW LB m m' p A n (HA & HS & HFr & HL & ND & HF1 & HF2) HA' HL' HFr' HS' H16 Hn Hp.
  split; [exact HA'|]. split; [rewrite HS'; exact HS|]. split; [rewrite HFr'; exact HFr|].
  split; [rewrite HL'; cbn [app map]; apply perm_skip; exact HL|]. split; [cbn [app map]; constructor; [exact Hp | exact ND]|].
  split; [constructor; [split; [exact H16 | exact Hn] | exact HF1] | exact HF2].
Qed.

Lemma live_remove_cons : forall A e l,
  live_remove A (e :: l) = if fst e =? A then live_remove A l else e :: live_remove A l.
Proof.
  intros A e l. unfold live_remove. rewrite filter_cons. destruct (fst e =? A); cbn [negb];
    destruct (decide _) as [Y|N]; try reflexivity; [exfalso; exact Y| exfalso; apply N; exact I].
Qed.

Lemma live_remove_perm : forall A l l', Permutation l l' -> Permutation (live_remove A l) (live_remove A l').
Proof.
  intros A l l' H. induction H as [| e l l' H IH | e1 e2 l | l1 l2 l3 H1 IH1 H2 IH2].
  - apply Permutation_refl.
  - rewrite !live_remove_cons. destruct (fst e =? A); [exact IH | apply perm_skip; exact IH].
  - rewrite !live_remove_cons. destruct (fst e1 =? A), (fst e2 =? A); try apply Permutation_refl. apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma live_remove_map : forall p A (L : list block),
  (forall b, In b L -> blk_addr b = A -> blk_id b = p) -> (forall b, In b L -> blk_id b = p -> blk_addr b = A) ->
  live_remove A (map blk_an L) = map blk_an (lb_remove p L).
Proof.
  intros p A L. induction L as [|b L IH]; intros H1 H2; [reflexivity|].
  assert (IH' := IH (fun b' Hb' => H1 b' (or_intror Hb')) (fun b' Hb' => H2 b' (or_intror Hb'))).
  rewrite lb_remove_cons. cbn [map]. rewrite live_remove_cons.
  change (fst (blk_an b)) with (blk_addr b).
  destruct (bptr_eqb (blk_id b) p) eqn:E.
  - apply bptr_eqb_eq in E. rewrite (H2 b (or_introl eq_refl) E), Z.eqb_refl. exact IH'.
  - assert (NA : blk_addr b <> A) by (intros EA; rewrite (H1 b (or_introl eq_refl) EA), bptr_eqb_refl in E; discriminate).
    apply Z.eqb_neq in NA. rewrite NA. cbn [map]. rewrite IH'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma AH_free : forall Σ Σ' OW LB m m' p A n,
  AHEAP Σ OW LB m -> In (p, A, n) OW -> ART RT Σ' m' -> rt_live RT Σ' = live_remove A (rt_live RT Σ) ->
  rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
  AHEAP Σ' (lb_remove p OW) LB m'.
Proof.
  intros Σ Σ' OW LB m m' p A n H Hin HA' HL' HFr' HS'.
  pose proof (AH_nodup _ _ _ _ H) as ND.
  assert (HinL : In (p, A, n) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
  assert (U1 : forall b, In b (OW ++ LB) -> blk_addr b = A -> blk_id b = p).
  { intros b Hb EA. destruct (decide (blk_id b = p)) as [E|NE]; [exact E|]. exfalso.
    pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n) H Hb HinL NE) as D.
    pose proof (AH_pos_gen _ _ _ _ b H Hb) as P1. pose proof (AH_pos_gen _ _ _ _ _ H HinL) as P2. cbn in D, P2. lia. }
  assert (U2 : forall b, In b (OW ++ LB) -> blk_id b = p -> blk_addr b = A).
  { intros b Hb E. destruct b as [[q A'] n']. cbn in E. subst q.
    destruct (AH_addr_unique (OW ++ LB) p A' n' A n ND Hb HinL) as [-> _]. reflexivity. }
  destruct H as (HA & HS & HFr & HL & _ & HF1 & HF2).
  split; [exact HA'|]. split; [rewrite HS'; exact HS|]. split; [rewrite HFr'; exact HFr|].
  split. { rewrite HL'. eapply Permutation_trans; [apply live_remove_perm; exact HL|].
           rewrite (live_remove_map p A _ U1 U2), lb_remove_app_l; [reflexivity | exact ND |].
           apply in_map_iff. exists (p, A, n). split; [reflexivity | exact Hin]. }
  split. { rewrite <- (lb_remove_app_l p OW LB ND) by (apply in_map_iff; exists (p, A, n); split; [reflexivity | exact Hin]).
           clear - ND. induction (OW ++ LB) as [|b L IH]; [constructor|]. rewrite lb_remove_cons. cbn [map] in ND. apply NoDup_cons_iff in ND as [N1 N2].
           destruct (bptr_eqb (blk_id b) p); [exact (IH N2)|]. cbn [map]. constructor; [|exact (IH N2)].
           intros Hi. apply N1. apply in_map_iff in Hi as (b' & E & Hb'). apply in_map_iff. exists b'. split; [exact E | eapply lb_remove_incl; exact Hb']. }
  split; [| exact HF2]. apply Forall_forall. intros b Hb. apply lb_remove_incl in Hb. exact (proj1 (Forall_forall _ _) HF1 b Hb).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aclient_write_ok (L : list block) (iv : Z * Z) : Prop :=
  (ACEIL <= fst iv /\ snd iv <= USTACK_TOP)
  \/ (forall x, fst iv <= x < snd iv -> client_static x)
  \/ (exists b, In b L /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Lemma AH_frame : forall Σ OW LB m m' W,
  AHEAP Σ OW LB m -> munch W m m' -> wmono bsegs m m' -> Forall (aclient_write_ok (OW ++ LB)) W -> AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' W H MU WM HW. destruct H as (HA & HS & HFr & HL & Rest).
  split; [| split; [exact HS | split; [exact HFr | split; [exact HL | exact Rest]]]].
  apply (af_frame RT AF Σ m m' ACEIL HA); [unfold ACEIL; rewrite HS; lia | | exact WM].
  intros a Hna. apply MU. rewrite HFr in Hna.
  assert (HIL : forall x, in_block (OW ++ LB) x -> in_live (rt_live RT Σ) x).
  { intros x Hx. apply in_live_blocks in Hx. destruct Hx as (q & k & Hq & Hr). exists q, k. split; [|exact Hr].
    eapply Permutation_in; [symmetry; exact HL | exact Hq]. }
  clear - HW Hna HIL. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
  apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)].
  intros [L1 L2]. apply Hna.
  destruct H1 as [[C1 C2]|[C|(b & Hb & C1 & C2)]]; cbn [fst snd] in *.
  - left. lia.
  - right; left. apply C. lia.
  - right; right; left. apply HIL. exists b. split; [exact Hb | lia].
Qed.

End WithRT.
