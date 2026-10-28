(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun.
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
Local Notation FR := (@ar_FR AR).

Definition ACEIL : Z := SP0 - STACK_WIN.

Definition blk_okA (b : block) : Prop := blk_addr b mod 16 = 0 /\ 0 < blk_size b /\ gsz (blk_id b) = blk_size b.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pb_in (b : block) : Prop :=
  exists f k, In (f, k) FR /\ f <= blk_addr b /\ blk_addr b + blk_size b <= f + fs_size k - 8.
Definition pb_ok (m : mem) (b : block) : Prop :=
  pb_in b /\ 0 < blk_size b /\ wr_at ctasegs m (blk_addr b) (blk_size b) /\ acc ctasegs m (blk_addr b) (blk_size b).
Definition blk_apart (b b' : block) : Prop :=
  blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b.
Fixpoint apartl (l : list block) : Prop :=
  match l with [] => True | b :: l' => Forall (blk_apart b) l' /\ apartl l' end.

(* [comment removed for export] *)
Definition fr_wr (m : mem) : Prop :=
  Forall (fun fk : Z * nat => wr_at ctasegs m (fst fk) (fs_size (snd fk) - 8) /\ wr_at ctasegs m (shad (fst fk)) (fs_size (snd fk) / 8)) FR.

(* [comment removed for export] *)
Definition heap_split (Σ : rts RT) (OW LB : list block) (m : mem) : Prop :=
  fr_wr m /\ exists PB LBr, Permutation LB (PB ++ LBr) /\ Permutation (rt_live RT Σ) (map blk_an (OW ++ LBr))
    /\ Forall (pb_ok m) PB /\ apartl PB.

Definition AHEAP (Σ : rts RT) (OW LB : list block) (m : mem) : Prop :=
  ART RT Σ m /\ rt_sp0 RT Σ = SP0 /\ rt_frames RT Σ = FR /\ heap_split Σ OW LB m
  /\ List.NoDup (map blk_id (OW ++ LB)) /\ Forall blk_okA OW /\ Forall (fun b => 0 < blk_size b) LB.

(* [comment removed for export] *)
Definition ablock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= ACEIL /\ (A + n <= 65536 \/ 12365824 <= A).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ablock_range_gen (A n : Z) : Prop :=
  0 < A /\ True /\ 0 <= n /\ A + n <= ACEIL /\ (A + n <= 65536 \/ 12365824 <= A).

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

Lemma AH_frames : forall Σ OW LB m, AHEAP Σ OW LB m -> rt_frames RT Σ = FR.
Proof. intros Σ OW LB m H. exact (proj1 (proj2 (proj2 H))). Qed.
Lemma AH_sp0 : forall Σ OW LB m, AHEAP Σ OW LB m -> rt_sp0 RT Σ = SP0.
Proof. intros Σ OW LB m H. exact (proj1 (proj2 H)). Qed.
Lemma AH_split : forall Σ OW LB m, AHEAP Σ OW LB m -> heap_split Σ OW LB m.
Proof. intros Σ OW LB m H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.

Lemma AH_fr_wr : forall Σ OW LB m f k, AHEAP Σ OW LB m -> In (f, k) FR ->
  wr_at ctasegs m f (fs_size k - 8) /\ wr_at ctasegs m (shad f) (fs_size k / 8).
Proof. intros Σ OW LB m f k H Hin. exact (proj1 (Forall_forall _ _) (proj1 (AH_split _ _ _ _ H)) (f, k) Hin). Qed.

(* [comment removed for export] *)
Lemma AH_cases : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) -> In (blk_addr b, blk_size b) (rt_live RT Σ) \/ pb_ok m b.
Proof.
  intros Σ OW LB m b H Hin. destruct (AH_split _ _ _ _ H) as (_ & PB & LBr & P1 & P2 & F & _).
  assert (C : In b (OW ++ LBr) \/ In b PB).
  { apply in_app_or in Hin as [Hin|Hin]; [left; apply in_or_app; left; exact Hin|].
    apply (Permutation_in _ P1) in Hin. apply in_app_or in Hin as [Hin|Hin]; [right; exact Hin | left; apply in_or_app; right; exact Hin]. }
  destruct C as [C|C].
  - left. eapply Permutation_in; [symmetry; exact P2|]. apply in_map_iff. exists b. split; [reflexivity | exact C].
  - right. exact (proj1 (Forall_forall _ _) F b C).
Qed.

Lemma AH_live_ow : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b OW -> In (blk_addr b, blk_size b) (rt_live RT Σ).
Proof.
  intros Σ OW LB m b H Hin. destruct (AH_split _ _ _ _ H) as (_ & PB & LBr & _ & P2 & _).
  eapply Permutation_in; [symmetry; exact P2|]. apply in_map_iff. exists b. split; [reflexivity | apply in_or_app; left; exact Hin].
Qed.

(* [comment removed for export] *)
Lemma AH_nofr : forall Σ OW LB m, FR = [] -> AHEAP Σ OW LB m ->
  rt_frames RT Σ = [] /\ Permutation (rt_live RT Σ) (map blk_an (OW ++ LB)).
Proof.
  intros Σ OW LB m E H. split; [rewrite (AH_frames _ _ _ _ H); exact E|].
  destruct (AH_split _ _ _ _ H) as (_ & PB & LBr & P1 & P2 & F & _).
  destruct PB as [|b PB].
  - cbn [app] in P1. eapply Permutation_trans; [exact P2|]. apply Permutation_map. apply Permutation_app_head. symmetry. exact P1.
  - exfalso. apply Forall_cons_iff in F as [((f & k & Hin & _) & _) _]. rewrite E in Hin. exact Hin.
Qed.
(* [comment removed for export] *)
Lemma AH_intro_nofr : forall Σ OW LB m, FR = [] -> ART RT Σ m -> rt_sp0 RT Σ = SP0 -> rt_frames RT Σ = [] ->
  Permutation (rt_live RT Σ) (map blk_an (OW ++ LB)) -> List.NoDup (map blk_id (OW ++ LB)) -> Forall blk_okA OW -> Forall (fun b => 0 < blk_size b) LB ->
  AHEAP Σ OW LB m.
Proof.
  intros Σ OW LB m E HA HS HF HL ND F1 F2. split; [exact HA|]. split; [exact HS|]. split; [rewrite E; exact HF|].
  split; [| exact (conj ND (conj F1 F2))]. split; [unfold fr_wr; rewrite E; constructor|]. exists [], LB. split; [reflexivity|]. split; [exact HL|]. split; constructor.
Qed.
Lemma AH_live : forall Σ OW LB m b, FR = [] -> AHEAP Σ OW LB m -> In b (OW ++ LB) -> In (blk_addr b, blk_size b) (rt_live RT Σ).
Proof.
  intros Σ OW LB m b E H Hin. destruct (AH_nofr _ _ _ _ E H) as (_ & HL). eapply Permutation_in; [symmetry; exact HL|].
  apply in_map_iff. exists b. split; [reflexivity | exact Hin].
Qed.
Lemma AH_incl : forall Σ OW LB m, FR = [] -> AHEAP Σ OW LB m -> forall e, In e (map blk_an (OW ++ LB)) -> In e (rt_live RT Σ).
Proof. intros Σ OW LB m E H e He. destruct (AH_nofr _ _ _ _ E H) as (_ & HL). eapply Permutation_in; [symmetry; exact HL | exact He]. Qed.

Lemma AH_live_len : forall Σ OW LB m, AHEAP Σ OW LB m -> (length (rt_live RT Σ) <= length (OW ++ LB))%nat.
Proof.
  intros Σ OW LB m H. destruct (AH_split _ _ _ _ H) as (_ & PB & LBr & P1 & P2 & _).
  rewrite (Permutation_length P2), length_map, !length_app, (Permutation_length P1), length_app. lia.
Qed.

(* [comment removed for export] *)
Definition fr_addr (a : Z) : Prop := in_fframe FR a \/ in_fframe_shadow FR a.

Lemma pb_in_shadow : forall b i, pb_in b -> 0 <= i < blk_size b -> in_fframe_shadow FR (shad (blk_addr b + i)).
Proof.
  intros b i (f & k & Hin & H1 & H2) Hi. exists f, k. split; [exact Hin|]. unfold shad.
  assert (f / 8 <= (blk_addr b + i) / 8) by (apply Z.div_le_mono; lia).
  assert ((blk_addr b + i) / 8 < (f + fs_size k) / 8).
  { assert ((blk_addr b + i) / 8 <= (f + fs_size k - 8) / 8) by (apply Z.div_le_mono; lia).
    replace (f + fs_size k - 8) with (f + fs_size k + (-1) * 8) in H0 by lia. rewrite Z.div_add in H0 by lia. lia. }
  lia.
Qed.

Lemma fs_size_div8 : forall k, fs_size k = 8 * (fs_size k / 8) /\ 0 < fs_size k / 8.
Proof.
  intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as P.
  replace (64 * 2 ^ Z.of_nat k) with (8 * 2 ^ Z.of_nat k * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma fr_shadow_in : forall f k a, In (f, k) FR -> shad f <= a < shad f + fs_size k / 8 -> in_fframe_shadow FR a.
Proof.
  intros f k a Hin Ha. exists f, k. split; [exact Hin|]. unfold shad in *. destruct (fs_size_div8 k) as (E & _).
  rewrite E. replace (f + 8 * (fs_size k / 8)) with (f + (fs_size k / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma fr_wr_agree : forall m m', fr_wr m -> agree_on fr_addr m m' -> fr_wr m'.
Proof.
  intros m m' H AG. unfold fr_wr in *. apply Forall_forall. intros [f k] Hin. destruct (proj1 (Forall_forall _ _) H (f, k) Hin) as [W1 W2]. cbn [fst snd] in *.
  split.
  - eapply wr_at_agree; [exact AG | exact W1 |]. intros a Ha. left. exists f, k. split; [exact Hin | lia].
  - eapply wr_at_agree; [exact AG | exact W2 |]. intros a Ha. right. exact (fr_shadow_in f k a Hin Ha).
Qed.

Lemma fr_wr_wmono : forall m m', fr_wr m -> wmono ctasegs m m' -> fr_wr m'.
Proof.
  intros m m' H WM. unfold fr_wr in *. eapply Forall_impl; [| exact H]. intros [f k] [W1 W2]. cbn [fst snd] in *.
  split; eapply wr_at_transport; eassumption.
Qed.

Lemma pb_ok_agree : forall m m' b, pb_ok m b -> agree_on fr_addr m m' -> pb_ok m' b.
Proof.
  intros m m' b (PI & Hn & W & AC) AG. split; [exact PI|]. split; [exact Hn|]. split.
  - eapply wr_at_agree; [exact AG | exact W |]. intros a Ha. left. destruct PI as (f & k & Hin & H1 & H2). exists f, k. split; [exact Hin | lia].
  - eapply acc_agree; [exact AG | exact AC |]. intros i Hi. right. exact (pb_in_shadow b i PI Hi).
Qed.

Lemma heap_split_agree : forall Σ OW LB m m', heap_split Σ OW LB m -> agree_on fr_addr m m' -> heap_split Σ OW LB m'.
Proof.
  intros Σ OW LB m m' (FW & PB & LBr & P1 & P2 & F & AP) AG. split; [exact (fr_wr_agree m m' FW AG)|].
  exists PB, LBr. split; [exact P1|]. split; [exact P2|]. split; [|exact AP].
  eapply Forall_impl; [|exact F]. intros b Hb. exact (pb_ok_agree m m' b Hb AG).
Qed.

(* [comment removed for export] *)
Lemma fr_agree_of_rt_pres : forall live SP m m', rt_pres live FR SP m m' -> agree_on fr_addr m m'.
Proof.
  intros live SP m m' H a Ha [Hc|Hc]; apply H; unfold wa; rewrite unsigned_lit by lia; [right; right; right; left; exact Hc | right; right; right; right; exact Hc].
Qed.
Lemma fr_agree_of_rt_pres_ex : forall live SP d n m m', rt_pres_ex live FR SP d n m m' ->
  agree_on (fun a => fr_addr a /\ ~ (d <= a < d + n)) m m'.
Proof.
  intros live SP d n m m' H a Ha [[Hc|Hc] Hd]; apply H; unfold wa; rewrite unsigned_lit by lia;
    [right; right; right; left; exact Hc | exact Hd | right; right; right; right; exact Hc | exact Hd].
Qed.

(* [comment removed for export] *)
Lemma AH_same : forall Σ OW LB m m', AHEAP Σ OW LB m -> ART RT Σ m' -> agree_on fr_addr m m' -> AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' (_ & HS & HF & SPL & H) HA AG.
  split; [exact HA|]. split; [exact HS|]. split; [exact HF|]. split; [exact (heap_split_agree _ _ _ _ _ SPL AG) | exact H].
Qed.

(* [comment removed for export] *)
Lemma pb_in_fframe : forall b a, pb_in b -> blk_addr b <= a < blk_addr b + blk_size b -> in_fframe FR a.
Proof. intros b a (f & k & Hin & H1 & H2) Ha. exists f, k. split; [exact Hin | lia]. Qed.

Lemma AH_aclient : forall Σ OW LB m SP a, AHEAP Σ OW LB m -> aclient_addr (OW ++ LB) SP a -> aclient (rt_live RT Σ) FR SP a.
Proof.
  intros Σ OW LB m SP a H [Ha|[Ha|(b & Hb & Hr)]]; [left; exact Ha | right; left; exact Ha |].
  destruct (AH_cases _ _ _ _ b H Hb) as [HL|(PI & _)].
  - right; right; left. exists (blk_addr b), (blk_size b). split; [exact HL | exact Hr].
  - right; right; right; left. exact (pb_in_fframe b a PI Hr).
Qed.

(* [comment removed for export] *)
Lemma AH_agree : forall Σ OW LB m0 SP m m', AHEAP Σ OW LB m0 -> rt_pres (rt_live RT Σ) FR SP m m' -> agree_on (aclient_addr (OW ++ LB) SP) m m'.
Proof. intros Σ OW LB m0 SP m m' H P a Ha Hc. apply P. unfold wa. rewrite unsigned_lit by lia. exact (AH_aclient _ _ _ _ _ _ H Hc). Qed.
Lemma AH_agree_ex : forall Σ OW LB m0 SP d n m m', AHEAP Σ OW LB m0 -> rt_pres_ex (rt_live RT Σ) FR SP d n m m' ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (d <= a < d + n)) m m'.
Proof.
  intros Σ OW LB m0 SP d n m m' H P a Ha [Hc Hd]. apply P; unfold wa; rewrite unsigned_lit by lia; [exact (AH_aclient _ _ _ _ _ _ H Hc) | exact Hd].
Qed.
Lemma AH_agree_fp : forall Σ OW LB m0 SP W m m', AHEAP Σ OW LB m0 -> rt_pres_fp (rt_live RT Σ) FR SP W m m' ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ outside W a) m m'.
Proof.
  intros Σ OW LB m0 SP W m m' H P a Ha [Hc Hd]. apply P; unfold wa; rewrite unsigned_lit by lia; [exact (AH_aclient _ _ _ _ _ _ H Hc) | exact Hd].
Qed.

Lemma AH_okA : forall Σ OW LB m p A n, AHEAP Σ OW LB m -> In (p, A, n) OW -> A mod 16 = 0 /\ 0 < n.
Proof.
  intros Σ OW LB m p A n (_ & _ & _ & _ & _ & HF & _) Hin. pose proof (proj1 (Forall_forall _ _) HF (p, A, n) Hin) as (X & Y & _). exact (conj X Y).
Qed.

(* [comment removed for export] *)
Lemma AH_gsz : forall Σ OW LB m p A n, AHEAP Σ OW LB m -> In (p, A, n) OW -> gsz p = n.
Proof.
  intros Σ OW LB m p A n (_ & _ & _ & _ & _ & HF & _) Hin. exact (proj2 (proj2 (proj1 (Forall_forall _ _) HF (p, A, n) Hin))).
Qed.

Lemma AH_pos_gen_ : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) -> 0 < blk_size b.
Proof.
  intros Σ OW LB m b (_ & _ & _ & _ & _ & HF1 & HF2) Hin. apply in_app_or in Hin as [Hin|Hin].
  - exact (proj1 (proj2 (proj1 (Forall_forall _ _) HF1 b Hin))).
  - exact (proj1 (Forall_forall _ _) HF2 b Hin).
Qed.

Lemma AH_range : forall Σ OW LB m p A n, AHEAP Σ OW LB m -> In (p, A, n) OW -> ablock_range A n.
Proof.
  intros Σ OW LB m p A n H Hin. pose proof (AH_okA _ _ _ _ _ _ _ H Hin) as (H16 & Hn).
  pose proof (AH_live_ow _ _ _ _ (p, A, n) H Hin) as HL. cbn in HL.
  destruct H as (HA & HS & _).
  destruct (af_live_range RT AF Σ m A n HA HL) as (R1 & R2 & R3). unfold ablock_range, ACEIL. rewrite <- HS.
  split; [exact R1|]. split; [exact H16|]. split; [lia|]. split; [exact R2 | unfold SEGTOP_A in R3; exact R3].
Qed.

(* [comment removed for export] *)
Lemma AH_fr_range : forall Σ OW LB m f k, AHEAP Σ OW LB m -> In (f, k) FR ->
  0 < f /\ f + fs_size k <= ACEIL /\ (f + fs_size k <= 0x10000 \/ SEGTOP_A <= f) /\ (f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f)
  /\ (forall p n, In (p, n) (rt_live RT Σ) -> f + fs_size k <= p \/ p + n <= f).
Proof.
  intros Σ OW LB m f k H Hin. pose proof (AH_frames _ _ _ _ H) as EF. destruct H as (HA & HS & _). rewrite <- EF in Hin.
  destruct (af_frames_range RT AF Σ m f k HA Hin) as (R1 & R2 & R3 & R4). pose proof (af_frames_hi RT AF Σ m f k HA Hin) as R5.
  unfold ACEIL. rewrite <- HS. auto.
Qed.

Lemma AH_range_gen : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) -> ablock_range_gen (blk_addr b) (blk_size b).
Proof.
  intros Σ OW LB m b H Hin. pose proof (AH_pos_gen_ Σ OW LB m b H Hin) as Hn.
  destruct (AH_cases _ _ _ _ b H Hin) as [HL|((f & k & Hf & P1 & P2) & _)].
  - destruct H as (HA & HS & _).
    destruct (af_live_range RT AF Σ m _ _ HA HL) as (R1 & R2 & R3). unfold ablock_range_gen, ACEIL. rewrite <- HS.
    split; [exact R1|]. split; [exact I|]. split; [lia|]. split; [exact R2 | unfold SEGTOP_A in R3; exact R3].
  - destruct (AH_fr_range _ _ _ _ f k H Hf) as (R1 & R2 & R3 & _). unfold ablock_range_gen, SEGTOP_A in *.
    split; [lia|]. split; [exact I|]. split; [lia|]. split; [lia | lia].
Qed.

(* [comment removed for export] *)
Lemma AH_offsh : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) ->
  blk_addr b + blk_size b <= SHLO \/ SHHI <= blk_addr b.
Proof.
  intros Σ OW LB m b H Hin. destruct (AH_cases _ _ _ _ b H Hin) as [HL|((f & k & Hf & P1 & P2) & _)].
  - destruct H as (HA & _).
    destruct (af_live_offshadow RT AF Σ m _ _ HA HL) as [R|R]; unfold SHLO, SHHI; [left | right]; lia.
  - destruct (AH_fr_range _ _ _ _ f k H Hf) as (_ & _ & _ & R & _). unfold SHLO, SHHI. lia.
Qed.

(* [comment removed for export] *)
Lemma pb_shadow_range : forall Σ OW LB m b i, AHEAP Σ OW LB m -> pb_in b -> 0 <= i < blk_size b -> SHLO <= shad (blk_addr b + i) < SHHI.
Proof.
  intros Σ OW LB m b i H (f & k & Hf & P1 & P2) Hi.
  destruct (AH_fr_range _ _ _ _ f k H Hf) as (R1 & R2 & _). pose proof (AH_ceil _ _ _ _ H) as (C1 & C2 & C3).
  unfold shad, SHLO, SHHI, SHB. pose proof (Z.div_pos (blk_addr b + i) 8 ltac:(lia) ltac:(lia)).
  assert ((blk_addr b + i) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; unfold USTACK_TOP, STACK_WIN in *; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma AH_same_w : forall Σ OW LB m m', AHEAP Σ OW LB m -> ART RT Σ m' -> wmono ctasegs m m' ->
  agree_on (fun a => in_fframe_shadow FR a /\ SHLO <= a < SHHI) m m' -> AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' H HA WM AG. pose proof H as (_ & HS & HF & (FW & PB & LBr & P1 & P2 & F & AP) & Rest).
  split; [exact HA|]. split; [exact HS|]. split; [exact HF|]. split; [| exact Rest].
  split; [exact (fr_wr_wmono m m' FW WM)|]. exists PB, LBr. split; [exact P1|]. split; [exact P2|]. split; [| exact AP].
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) F b Hb) as (PI & Hn & WR & AC).
  split; [exact PI|]. split; [exact Hn|]. split; [exact (wr_at_transport ctasegs m m' _ _ WR WM)|].
  eapply acc_agree; [exact AG | exact AC |]. intros i Hi. split; [exact (pb_in_shadow b i PI Hi) | exact (pb_shadow_range _ _ _ _ b i H PI Hi)].
Qed.

(* [comment removed for export] *)
Lemma AH_same_ex : forall Σ OW LB m m' sp d n, AHEAP Σ OW LB m -> ART RT Σ m' -> wmono ctasegs m m' ->
  rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) sp d n m m' -> (d + n <= SHLO \/ SHHI <= d \/ n <= 0) ->
  AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' sp d n H HA WM PRES O. apply (AH_same_w Σ OW LB m m' H HA WM).
  rewrite (AH_frames _ _ _ _ H) in PRES.
  intros a Ha [Hs Hr]. apply PRES; unfold wa; rewrite unsigned_lit by lia; [right; right; right; right; exact Hs | lia].
Qed.

(* [comment removed for export] *)
Lemma AH_rng : forall Σ OW LB m sp b d n,
  AHEAP Σ OW LB m -> In b (OW ++ LB) -> blk_addr b <= d -> d + n <= blk_addr b + blk_size b ->
  rng_class RT Σ d n /\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp (d + i)).
Proof.
  intros Σ OW LB m sp b d n H Hb H1 H2. unfold rng_class. rewrite (AH_frames _ _ _ _ H).
  destruct (AH_cases _ _ _ _ b H Hb) as [INL|((f & k & Hf & P1 & P2) & _)].
  - split; [left; exists (blk_addr b), (blk_size b); split; [exact INL | lia] |].
    intros i Hi; right; right; left; exists (blk_addr b), (blk_size b); split; [exact INL | lia].
  - split; [right; left; exists f, k; split; [exact Hf | lia] |].
    intros i Hi; right; right; right; left; exists f, k; split; [exact Hf | lia].
Qed.

(* [comment removed for export] *)
Lemma AH_acc : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) ->
  wr_at ctasegs m (blk_addr b) (blk_size b) /\ acc ctasegs m (blk_addr b) (blk_size b).
Proof.
  intros Σ OW LB m b H Hin. destruct (AH_cases _ _ _ _ b H Hin) as [HL|(_ & _ & W & AC)]; [| exact (conj W AC)].
  destruct H as (HA & _). exact (af_acc_live RT AF Σ m _ _ HA HL).
Qed.

Lemma in_split_ne : forall (L : list block) b1 b2, In b1 L -> In b2 L -> b1 <> b2 ->
  exists l1 l2, L = l1 ++ b1 :: l2 /\ In b2 (l1 ++ l2).
Proof.
  intros L b1 b2 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & ->). exists l1, l2. split; [reflexivity|].
  apply in_app_or in H2. apply in_or_app. destruct H2 as [H2|[H2|H2]]; [left; exact H2 | congruence | right; exact H2].
Qed.

Lemma apartl_In : forall l b1 b2, apartl l -> In b1 l -> In b2 l -> b1 <> b2 -> blk_apart b1 b2.
Proof.
  induction l as [|c l IH]; intros b1 b2 AP H1 H2 NE; [contradiction|].
  cbn [apartl] in AP. destruct AP as [F AP]. destruct H1 as [->|H1], H2 as [->|H2].
  - congruence.
  - exact (proj1 (Forall_forall _ _) F b2 H2).
  - pose proof (proj1 (Forall_forall _ _) F b1 H1) as X. unfold blk_apart in *. lia.
  - exact (IH b1 b2 AP H1 H2 NE).
Qed.

Lemma AH_disjoint_gen : forall Σ OW LB m b1 b2, AHEAP Σ OW LB m -> In b1 (OW ++ LB) -> In b2 (OW ++ LB) -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros Σ OW LB m b1 b2 H H1 H2 NE. assert (NEb : b1 <> b2) by congruence.
  destruct (AH_split _ _ _ _ H) as (_ & PB & LBr & P1 & P2 & F & AP).
  assert (C : forall b, In b (OW ++ LB) -> In b (OW ++ LBr) \/ In b PB).
  { intros b Hin. apply in_app_or in Hin as [Hin|Hin]; [left; apply in_or_app; left; exact Hin|].
    apply (Permutation_in _ P1) in Hin. apply in_app_or in Hin as [Hin|Hin]; [right; exact Hin | left; apply in_or_app; right; exact Hin]. }
  assert (RP : forall b b', In b (OW ++ LBr) -> In b' PB -> blk_apart b b').
  { intros b b' Hb Hb'. destruct (proj1 (Forall_forall _ _) F b' Hb') as ((f & k & Hf & Q1 & Q2) & Q3 & _).
    destruct (AH_fr_range _ _ _ _ f k H Hf) as (_ & _ & _ & _ & R).
    assert (HL : In (blk_addr b, blk_size b) (rt_live RT Σ)).
    { eapply Permutation_in; [symmetry; exact P2|]. apply in_map_iff. exists b. split; [reflexivity | exact Hb]. }
    specialize (R _ _ HL). unfold blk_apart. lia. }
  destruct (C b1 H1) as [R1|Q1], (C b2 H2) as [R2|Q2].
  - destruct (in_split_ne _ _ _ R1 R2 NEb) as (L1 & L2 & E & Hin).
    assert (HL1 : In (blk_addr b1, blk_size b1) (rt_live RT Σ)).
    { eapply Permutation_in; [symmetry; exact P2|]. apply in_map_iff. exists b1. split; [reflexivity | exact R1]. }
    destruct H as (HA & _).
    destruct (in_split _ _ HL1) as (l1 & l2 & El).
    apply (af_live_disj RT AF Σ m (blk_addr b1) (blk_size b1) (blk_addr b2) (blk_size b2) l1 l2 HA El).
    rewrite El, E, map_app in P2. cbn [map] in P2. change (blk_an b1) with (blk_addr b1, blk_size b1) in P2.
    apply Permutation_app_inv in P2. eapply Permutation_in; [symmetry; exact P2|].
    rewrite <- map_app. apply in_map_iff. exists b2. split; [reflexivity | exact Hin].
  - exact (RP b1 b2 R1 Q2).
  - pose proof (RP b2 b1 R2 Q1) as X. unfold blk_apart in X. lia.
  - exact (apartl_In PB b1 b2 AP Q1 Q2 NEb).
Qed.

Lemma AH_disjoint : forall Σ OW LB m p A n p' A' n',
  AHEAP Σ OW LB m -> In (p, A, n) OW -> In (p', A', n') OW -> p <> p' -> A + n <= A' \/ A' + n' <= A.
Proof.
  intros Σ OW LB m p A n p' A' n' H H1 H2 NE.
  exact (AH_disjoint_gen Σ OW LB m (p, A, n) (p', A', n') H (in_or_app _ _ _ (or_introl H1)) (in_or_app _ _ _ (or_introl H2)) NE).
Qed.

Lemma AH_pos_gen : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) -> 0 < blk_size b.
Proof. exact AH_pos_gen_. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma AH_malloc : forall Σ Σ' OW LB m m' p A n SP,
  AHEAP Σ OW LB m -> ART RT Σ' m' -> rt_live RT Σ' = (A, n) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> A mod 16 = 0 -> 0 < n -> gsz p = n -> ~ In p (map blk_id (OW ++ LB)) ->      (* [comment removed for export] *)
  rt_pres (rt_live RT Σ) (rt_frames RT Σ) SP m m' ->
  AHEAP Σ' ((p, A, n) :: OW) LB m'.
Proof.
  intros Σ Σ' OW LB m m' p A n SP (HA & HS & HFr & SPL & ND & HF1 & HF2) HA' HL' HFr' HS' H16 Hn Hg Hp PRES.
  rewrite HFr in PRES. pose proof (fr_agree_of_rt_pres _ _ _ _ PRES) as AG.
  split; [exact HA'|]. split; [rewrite HS'; exact HS|]. split; [rewrite HFr'; exact HFr|].
  split. { destruct (heap_split_agree _ _ _ _ _ SPL AG) as (FW & PB & LBr & P1 & P2 & F & AP). split; [exact FW|]. exists PB, LBr.
           split; [exact P1|]. split; [rewrite HL'; cbn [app map]; apply perm_skip; exact P2|]. split; [exact F | exact AP]. }
  split; [cbn [app map]; constructor; [exact Hp | exact ND]|].
  split; [constructor; [split; [exact H16 | split; [exact Hn | exact Hg]] | exact HF1] | exact HF2].
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

Lemma nodup_ids_perm : forall (L L' : list block), Permutation L L' -> List.NoDup (map blk_id L) -> List.NoDup (map blk_id L').
Proof. intros L L' P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P | exact ND]. Qed.

(* [comment removed for export] *)
Lemma AH_free : forall Σ Σ' OW LB m m' p A n SP,
  AHEAP Σ OW LB m -> In (p, A, n) OW -> ART RT Σ' m' -> rt_live RT Σ' = live_remove A (rt_live RT Σ) ->
  rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
  rt_pres (rt_live RT Σ') (rt_frames RT Σ) SP m m' ->
  AHEAP Σ' (lb_remove p OW) LB m'.
Proof.
  intros Σ Σ' OW LB m m' p A n SP H Hin HA' HL' HFr' HS' PRES.
  pose proof (AH_nodup _ _ _ _ H) as ND.
  assert (HinL : In (p, A, n) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
  assert (U1 : forall b, In b (OW ++ LB) -> blk_addr b = A -> blk_id b = p).
  { intros b Hb EA. destruct (decide (blk_id b = p)) as [E|NE]; [exact E|]. exfalso.
    pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n) H Hb HinL NE) as D.
    pose proof (AH_pos_gen _ _ _ _ b H Hb) as P1. pose proof (AH_pos_gen _ _ _ _ _ H HinL) as P2. cbn in D, P2. lia. }
  assert (U2 : forall b, In b (OW ++ LB) -> blk_id b = p -> blk_addr b = A).
  { intros b Hb E. destruct b as [[q A'] n']. cbn in E. subst q.
    destruct (AH_addr_unique (OW ++ LB) p A' n' A n ND Hb HinL) as [-> _]. reflexivity. }
  destruct H as (HA & HS & HFr & SPL & _ & HF1 & HF2).
  rewrite HFr in PRES. pose proof (fr_agree_of_rt_pres _ _ _ _ PRES) as AG.
  split; [exact HA'|]. split; [rewrite HS'; exact HS|]. split; [rewrite HFr'; exact HFr|].
  split. { destruct (heap_split_agree _ _ _ _ _ SPL AG) as (FW & PB & LBr & P1 & P2 & F & AP). split; [exact FW|]. exists PB, LBr.
           assert (SUB : forall b, In b (OW ++ LBr) -> In b (OW ++ LB)).
           { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right].
             eapply Permutation_in; [symmetry; exact P1|]. apply in_or_app. right. exact Hb. }
           assert (NDr : List.NoDup (map blk_id (OW ++ LBr))).
           { assert (PX : Permutation (OW ++ LB) (PB ++ (OW ++ LBr))).
             { eapply Permutation_trans; [apply Permutation_app_head; exact P1|]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
             pose proof (nodup_ids_perm _ _ PX ND) as X. rewrite map_app in X. apply NoDup_app_remove_l in X. exact X. }
           split; [exact P1|]. split; [| split; [exact F | exact AP]].
           rewrite HL'. eapply Permutation_trans; [apply live_remove_perm; exact P2|].
           rewrite (live_remove_map p A _ (fun b Hb => U1 b (SUB b Hb)) (fun b Hb => U2 b (SUB b Hb))), lb_remove_app_l; [reflexivity | exact NDr |].
           apply in_map_iff. exists (p, A, n). split; [reflexivity | exact Hin]. }
  split. { rewrite <- (lb_remove_app_l p OW LB ND) by (apply in_map_iff; exists (p, A, n); split; [reflexivity | exact Hin]).
           clear - ND. induction (OW ++ LB) as [|b L IH]; [constructor|]. rewrite lb_remove_cons. cbn [map] in ND. apply NoDup_cons_iff in ND as [N1 N2].
           destruct (bptr_eqb (blk_id b) p); [exact (IH N2)|]. cbn [map]. constructor; [|exact (IH N2)].
           intros Hi. apply N1. apply in_map_iff in Hi as (b' & E & Hb'). apply in_map_iff. exists b'. split; [exact E | eapply lb_remove_incl; exact Hb']. }
  split; [| exact HF2]. apply Forall_forall. intros b Hb. apply lb_remove_incl in Hb. exact (proj1 (Forall_forall _ _) HF1 b Hb).
Qed.

(* [comment removed for export] *)
Lemma AH_free_perm : forall Σ Σ' OW LB m p A n, AHEAP Σ OW LB m -> In (p, A, n) OW ->
  rt_live RT Σ' = live_remove A (rt_live RT Σ) -> Permutation (rt_live RT Σ) ((A, n) :: rt_live RT Σ').
Proof.
  intros Σ Σ' OW LB m p A n H Hin HL'.
  pose proof (AH_nodup _ _ _ _ H) as ND. pose proof (AH_nodup_l _ _ _ _ H) as NDl.
  assert (HinL : In (p, A, n) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
  assert (U1 : forall b, In b (OW ++ LB) -> blk_addr b = A -> blk_id b = p).
  { intros b Hb EA. destruct (decide (blk_id b = p)) as [E|NE]; [exact E|]. exfalso.
    pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n) H Hb HinL NE) as DJ.
    pose proof (AH_pos_gen _ _ _ _ b H Hb) as P1. pose proof (AH_pos_gen _ _ _ _ _ H HinL) as P2. cbn in DJ, P2. lia. }
  assert (U2 : forall b, In b (OW ++ LB) -> blk_id b = p -> blk_addr b = A).
  { intros b Hb E. destruct b as [[q A'] n']. cbn in E. subst q.
    destruct (AH_addr_unique (OW ++ LB) p A' n' A n ND Hb HinL) as [-> _]. reflexivity. }
  destruct H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & F & AP) & _ & HF1 & HF2).
  assert (SUB : forall b, In b (OW ++ LBr) -> In b (OW ++ LB)).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right].
    eapply Permutation_in; [symmetry; exact P1|]. apply in_or_app. right. exact Hb. }
  assert (NDr : List.NoDup (map blk_id (OW ++ LBr))).
  { assert (PX : Permutation (OW ++ LB) (PB ++ (OW ++ LBr))).
    { eapply Permutation_trans; [apply Permutation_app_head; exact P1|]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
    pose proof (nodup_ids_perm _ _ PX ND) as X. rewrite map_app in X. apply NoDup_app_remove_l in X. exact X. }
  assert (INP : In p (map blk_id OW)) by (apply in_map_iff; exists (p, A, n); split; [reflexivity | exact Hin]).
  (* [comment removed for export] *)
  assert (POW : Permutation OW ((p, A, n) :: lb_remove p OW)).
  { clear - NDl Hin. induction OW as [|b OW IH]; [destruct Hin|]. rewrite lb_remove_cons. cbn [map] in NDl. apply NoDup_cons_iff in NDl as [N1 N2].
    destruct Hin as [->|Hin].
    - cbn [blk_id fst]. rewrite bptr_eqb_refl. rewrite (lb_remove_notin p OW N1). apply Permutation_refl.
    - assert (NE : bptr_eqb (blk_id b) p = false).
      { apply bptr_eqb_neq. intros E. apply N1. rewrite E. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hin]. }
      rewrite NE. eapply Permutation_trans; [apply perm_skip; exact (IH Hin N2)|]. apply perm_swap. }
  rewrite HL'. eapply Permutation_trans; [exact P2|].
  eapply Permutation_trans; [| apply perm_skip; apply live_remove_perm; symmetry; exact P2].
  rewrite (live_remove_map p A _ (fun b Hb => U1 b (SUB b Hb)) (fun b Hb => U2 b (SUB b Hb))), (lb_remove_app_l _ _ _ NDr INP).
  rewrite !map_app. change ((A, n) :: map blk_an (lb_remove p OW) ++ map blk_an LBr) with (map blk_an ((p, A, n) :: lb_remove p OW) ++ map blk_an LBr).
  apply Permutation_app_tail. apply Permutation_map. exact POW.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aclient_write_ok (L : list block) (iv : Z * Z) : Prop :=
  (ACEIL <= fst iv /\ snd iv <= USTACK_TOP)
  \/ (forall x, fst iv <= x < snd iv -> client_static x)
  \/ (exists b, In b L /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

(* [comment removed for export] *)
Lemma pb_shadow_outside : forall Σ OW LB m W b i,
  AHEAP Σ OW LB m -> Forall (aclient_write_ok (OW ++ LB)) W -> pb_in b -> 0 <= i < blk_size b -> outside W (shad (blk_addr b + i)).
Proof.
  intros Σ OW LB m W b i H HW (f & k & Hf & P1 & P2) Hi.
  destruct (AH_fr_range _ _ _ _ f k H Hf) as (R1 & R2 & _). pose proof (AH_ceil _ _ _ _ H) as (C1 & C2 & C3).
  assert (S1 : SHLO <= shad (blk_addr b + i) < SHHI).
  { unfold shad, SHLO, SHHI, SHB. pose proof (Z.div_pos (blk_addr b + i) 8 ltac:(lia) ltac:(lia)).
    assert ((blk_addr b + i) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; unfold USTACK_TOP, STACK_WIN in *; lia). lia. }
  induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
  apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)].
  intros [L1 L2]. destruct H1 as [[X1 X2]|[X|(b' & Hb' & X1 & X2)]]; cbn [fst snd] in *.
  - lia.
  - destruct (X _ (conj L1 L2)) as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    unfold SHLO in S1. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - pose proof (AH_offsh _ _ _ _ b' H Hb') as O. lia.
Qed.

Lemma AH_frame : forall Σ OW LB m m' W,
  AHEAP Σ OW LB m -> munch W m m' -> wmono ctasegs m m' -> Forall (aclient_write_ok (OW ++ LB)) W -> AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' W H MU WM HW. pose proof H as (HA & HS & HFr & SPL & Rest).
  split; [| split; [exact HS | split; [exact HFr | split; [| exact Rest]]]].
  - apply (af_frame RT AF Σ m m' ACEIL HA); [unfold ACEIL; rewrite HS; lia | | exact WM].
    intros a Hna. apply MU. rewrite HFr in Hna.
    clear - H HW Hna. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
    apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)].
    intros [L1 L2]. apply Hna. apply (AH_aclient _ _ _ _ ACEIL _ H).
    destruct H1 as [[C1 C2]|[C|(b & Hb & C1 & C2)]]; cbn [fst snd] in *.
    + left. lia.
    + right; left. apply C. lia.
    + right; right. exists b. split; [exact Hb | lia].
  - destruct SPL as (FW & PB & LBr & P1 & P2 & F & AP). split; [exact (fr_wr_wmono m m' FW WM)|]. exists PB, LBr. split; [exact P1|]. split; [exact P2|]. split; [| exact AP].
    apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) F b Hb) as (PI & Hn & WR & AC).
    split; [exact PI|]. split; [exact Hn|]. split; [exact (wr_at_transport ctasegs m m' _ _ WR WM)|].
    eapply acc_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | exact AC |].
    intros i Hi. exact (pb_shadow_outside _ _ _ _ W b i H HW PI Hi).
Qed.

End WithRT.
