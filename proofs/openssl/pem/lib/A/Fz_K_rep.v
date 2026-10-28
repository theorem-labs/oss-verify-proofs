(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree Fz_kit I_ut Fz_chk Fz_K_hash.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Definition e_property_cmp : Z := 0x20bf8c.
Definition T_HW : Z := 0x20c77c.      (* [comment removed for export] *)
Definition T_CW : Z := 0x20c79c.
Definition T_DAW : Z := 0x20c7bc.
Definition T_DAAW : Z := 0x20c7dc.

Definition pnode : Type := (Z * Z)%type.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint plseg (m : mem) (c : Z) (ns : list pnode) (c' : Z) : Prop :=
  match ns with
  | [] => c = c'
  | (A, h) :: ns' => rw_cells asegs m c [C8 (wz A)] /\ A mod 8 = 0
      /\ (exists d : word, rw_cells asegs m A [C8 d]) /\ rw_cells asegs m (A + 16) [C8 (wz h)] /\ 0 <= h < 2 ^ 64
      /\ plseg m (A + 8) ns' c'
  end.

Definition pchain (m : mem) (c : Z) (ns : list pnode) : Prop :=
  exists c', plseg m c ns c' /\ rw_cells asegs m c' [C8 (wz 0)].

(* [comment removed for export] *)
Fixpoint pend (c : Z) (ns : list pnode) : Z :=
  match ns with [] => c | (A, _) :: ns' => pend (A + 8) ns' end.

Lemma pend_app : forall ns1 ns2 c, pend c (ns1 ++ ns2) = pend (pend c ns1) ns2.
Proof. induction ns1 as [|[A h] ns1 IH]; intros ns2 c; cbn [pend app]; [reflexivity| apply IH]. Qed.

Lemma plseg_end : forall m ns c c', plseg m c ns c' -> c' = pend c ns.
Proof.
  intros m ns. induction ns as [|[A h] ns IH]; intros c c' H; cbn [plseg pend] in *; [symmetry; exact H|].
  destruct H as (_ & _ & _ & _ & _ & R). exact (IH _ _ R).
Qed.

Lemma plseg_app : forall m ns1 ns2 c c1 c2, plseg m c ns1 c1 -> plseg m c1 ns2 c2 -> plseg m c (ns1 ++ ns2) c2.
Proof.
  intros m ns1. induction ns1 as [|[A h] ns1 IH]; intros ns2 c c1 c2 H1 H2; cbn [plseg app] in *.
  - subst c1. exact H2.
  - destruct H1 as (C & AL & D & HH & HR & R). repeat (split; [assumption|]). eapply IH; eassumption.
Qed.

Lemma plseg_split : forall m ns1 ns2 c c2, plseg m c (ns1 ++ ns2) c2 -> exists c1, plseg m c ns1 c1 /\ plseg m c1 ns2 c2.
Proof.
  intros m ns1. induction ns1 as [|[A h] ns1 IH]; intros ns2 c c2 H; cbn [plseg app] in *.
  - exists c. auto.
  - destruct H as (C & AL & D & HH & HR & R). destruct (IH _ _ _ R) as (c1 & R1 & R2). exists c1. split; [| exact R2]. repeat (split; [assumption|]). exact R1.
Qed.

Lemma plseg_aligned : forall m ns c c', plseg m c ns c' -> forall n, In n ns -> fst n mod 8 = 0.
Proof.
  intros m ns. induction ns as [|[B h] ns IH]; intros c c' H n Hin; [destruct Hin|]. cbn [plseg] in H. destruct H as (_ & AL & _ & _ & _ & R).
  destruct Hin as [E|Hin]; [subst n; cbn [fst]; exact AL| exact (IH _ _ R n Hin)].
Qed.

Lemma plseg_hashes : forall m ns c c', plseg m c ns c' -> forall n, In n ns -> 0 <= snd n < 2 ^ 64.
Proof.
  intros m ns. induction ns as [|[B h] ns IH]; intros c c' H n Hin; [destruct Hin|]. cbn [plseg] in H. destruct H as (_ & _ & _ & _ & HR & R).
  destruct Hin as [E|Hin]; [subst n; cbn [snd]; exact HR| exact (IH _ _ R n Hin)].
Qed.

(* [comment removed for export] *)
Lemma pend_where : forall ns c, (ns = [] /\ pend c ns = c) \/ (exists pre A h, ns = pre ++ [(A, h)] /\ pend c ns = A + 8).
Proof.
  induction ns as [|[B h] ns IH]; intros c; cbn [pend]; [left; auto| right].
  destruct (IH (B + 8)) as [[-> E]|(pre & A & h' & -> & E)].
  - exists [], B, h. auto.
  - exists ((B, h) :: pre), A, h'. auto.
Qed.

Lemma pend_aligned : forall ns c, c mod 8 = 0 -> (forall n, In n ns -> fst n mod 8 = 0) -> pend c ns mod 8 = 0.
Proof.
  intros ns c Hc Hn. destruct (pend_where ns c) as [[_ ->]|(pre & A & h & E & ->)]; [exact Hc|].
  pose proof (Hn (A, h) ltac:(rewrite E; apply in_or_app; right; left; reflexivity)) as X. cbn [fst] in X. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Fixpoint plseg_fp (c : Z) (ns : list pnode) (a : Z) : Prop :=
  match ns with
  | [] => False
  | (A, h) :: ns' => (c <= a < c + 8) \/ (A <= a < A + 8) \/ (A + 16 <= a < A + 24) \/ plseg_fp (A + 8) ns' a
  end.

(* [comment removed for export] *)
Definition pns_fp (c : Z) (ns : list pnode) (a : Z) : Prop := (c <= a < c + 8) \/ exists n, In n ns /\ fst n <= a < fst n + 24.

Lemma plseg_fp_where : forall ns c a, plseg_fp c ns a -> pns_fp c ns a.
Proof.
  induction ns as [|[A h] ns IH]; intros c a H; cbn [plseg_fp] in H; [destruct H|]. unfold pns_fp.
  destruct H as [H|[H|[H|H]]]; [left; exact H| right; exists (A, h); split; [left; reflexivity| cbn [fst]; lia]| right; exists (A, h); split; [left; reflexivity| cbn [fst]; lia]|].
  destruct (IH _ _ H) as [H1|(n & Hn & H1)]; [right; exists (A, h); split; [left; reflexivity| cbn [fst]; lia]| right; exists n; split; [right; exact Hn| exact H1]].
Qed.

Tactic Notation "csz" := cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
Tactic Notation "csz" "in" hyp(H) := cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.

Lemma plseg_agree : forall m m' ns c c', plseg m c ns c' -> agree_on (plseg_fp c ns) m m' -> plseg m' c ns c'.
Proof.
  intros m m' ns. induction ns as [|[A h] ns IH]; intros c c' H AG; cbn [plseg] in *; [exact H|].
  destruct H as (C & AL & (d & D) & HH & HR & R).
  split. { eapply rw_cells_agree_nw; [exact C|]. eapply agree_sub; [exact AG|]. csz. intros a Ha. cbn [plseg_fp]. left. lia. }
  split; [exact AL|].
  split. { exists d. eapply rw_cells_agree_nw; [exact D|]. eapply agree_sub; [exact AG|]. csz. intros a Ha. cbn [plseg_fp]. right; left. lia. }
  split. { eapply rw_cells_agree_nw; [exact HH|]. eapply agree_sub; [exact AG|]. csz. intros a Ha. cbn [plseg_fp]. right; right; left. lia. }
  split; [exact HR|].
  apply IH; [exact R|]. eapply agree_sub; [exact AG|]. intros a Ha. cbn [plseg_fp]. do 3 right. exact Ha.
Qed.

Lemma pchain_agree : forall m m' ns c, pchain m c ns -> agree_on (pns_fp c ns) m m' -> pchain m' c ns.
Proof.
  intros m m' ns c (c' & S & Z0) AG. exists c'.
  split; [eapply plseg_agree; [exact S| eapply agree_sub; [exact AG| intros a Ha; exact (plseg_fp_where _ _ _ Ha)]]|].
  eapply rw_cells_agree_nw; [exact Z0|]. eapply agree_sub; [exact AG|]. csz. intros a Ha.
  rewrite (plseg_end _ _ _ _ S) in Ha. destruct (pend_where ns c) as [[E1 E2]|(pre & A & h & E1 & E2)]; rewrite E2 in Ha.
  - left. exact Ha.
  - right. exists (A, h). split; [rewrite E1; apply in_or_app; right; left; reflexivity| cbn [fst]; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition plh_cells (B items : Z) : list cell :=
  [C8 (wz B); C8 (wz e_property_cmp); C8 (wz e_property_hash); C8 (wz T_HW); C8 (wz T_CW); C8 (wz T_DAW); C8 (wz T_DAAW);
   C4 (wz 8); C4 (wz 16); C4 (wz 0); C4 (wz 8); C8 (wz 512); C8 (wz 256); C8 (wz items); C4 (wz 0); CB 4 (repeat (Z_to_bv 8 0) 4)].

Definition plh_rep (m : mem) (lh B items : Z) (bks : list (list pnode)) : Prop :=
     rw_cells asegs m lh (plh_cells B items) /\ lh mod 16 = 0 /\ B mod 16 = 0
  /\ length bks = 16%nat /\ 0 <= items
  /\ (forall i, 0 <= i < 16 -> pchain m (B + 8 * i) (nth (Z.to_nat i) bks []))
  /\ (forall i, 8 <= i < 16 -> nth (Z.to_nat i) bks [] = [])
  /\ List.NoDup (lh :: B :: map fst (concat bks)).

(* [comment removed for export] *)
Definition plh_L (lh B : Z) (bks : list (list pnode)) : list (Z * Z) := (lh, 104) :: (B, 128) :: map (fun n => (fst n, 24)) (concat bks).

Definition plh_fp (lh B : Z) (bks : list (list pnode)) (a : Z) : Prop :=
  (lh <= a < lh + 104) \/ (B <= a < B + 128) \/ exists n, In n (concat bks) /\ fst n <= a < fst n + 24.

Lemma in_concat_nthZ : forall (bks : list (list pnode)) i n, In n (nth (Z.to_nat i) bks []) -> In n (concat bks).
Proof. intros bks i n H. exact (in_nth_concat _ _ _ H). Qed.

Lemma plh_L_node : forall lh B bks n, In n (concat bks) -> In (fst n, 24) (plh_L lh B bks).
Proof. intros lh B bks n Hn. right; right. apply in_map_iff. exists n. auto. Qed.

Lemma plh_rep_agree : forall m m' lh B items bks, plh_rep m lh B items bks -> agree_on (plh_fp lh B bks) m m' -> plh_rep m' lh B items bks.
Proof.
  intros m m' lh B items bks (SC & AL & BL & LEN & IT & CH & EMP & ND) AG.
  split. { eapply rw_cells_agree_nw; [exact SC|]. eapply agree_sub; [exact AG|]. intros a Ha. left. cbn in Ha. lia. }
  split; [exact AL|]. split; [exact BL|]. split; [exact LEN|]. split; [exact IT|].
  split; [| split; [exact EMP| exact ND]].
  intros i Hi. eapply pchain_agree; [exact (CH i Hi)|].
  eapply agree_sub; [exact AG|]. intros a [Ha|(n & Hn & Ha)].
  + right; left. lia.
  + right; right. exists n. split; [exact (in_concat_nthZ _ _ _ Hn)| exact Ha].
Qed.

(* [comment removed for export] *)
Lemma plh_rep_munch : forall W m m' lh B items bks,
  plh_rep m lh B items bks -> munch W m m' -> (forall a, plh_fp lh B bks a -> outside W a) -> plh_rep m' lh B items bks.
Proof. intros W m m' lh B items bks REP MU HW. eapply plh_rep_agree; [exact REP|]. exact (agree_of_munch W m m' _ MU HW). Qed.

Lemma nodup_app_inv : forall {A : Type} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1 /\ List.NoDup l2 /\ (forall a, In a l1 -> ~ In a l2).
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros l2 ND; cbn [app] in ND.
  - split; [constructor|]. split; [exact ND|]. intros a [].
  - inversion ND as [|x' l' NI ND']; subst. destruct (IH _ ND') as (A1 & A2 & A3).
    split; [constructor; [intros X; apply NI; apply in_or_app; left; exact X| exact A1]|]. split; [exact A2|].
    intros a [<-|Ha] Hb; [apply NI; apply in_or_app; right; exact Hb| exact (A3 a Ha Hb)].
Qed.

Lemma plh_bucket_nodup : forall (bks : list (list pnode)) i, List.NoDup (map fst (concat bks)) -> List.NoDup (map fst (nth i bks [])).
Proof.
  induction bks as [|b bks IH]; intros i ND.
  - destruct i; cbn; constructor.
  - cbn [concat] in ND. rewrite map_app in ND. destruct (nodup_app_inv _ _ ND) as (N1 & N2 & _).
    destruct i as [|i]; cbn [nth]; [exact N1| exact (IH i N2)].
Qed.

(* [comment removed for export] *)
Lemma plh_ids_distinct : forall (bks : list (list pnode)) i k j l n1 n2, List.NoDup (map fst (concat bks)) ->
  nth_error (nth i bks []) k = Some n1 -> nth_error (nth j bks []) l = Some n2 -> (i, k) <> (j, l) -> fst n1 <> fst n2.
Proof.
  intros bks i k j l n1 n2 ND E1 E2 NE E. apply NE. clear NE. revert i k j l n1 n2 ND E1 E2 E.
  induction bks as [|b0 bs IH]; intros i k j l a b ND Ea Eb E.
  - destruct i; destruct k; discriminate.
  - cbn [concat] in ND. rewrite map_app in ND.
    destruct (nodup_app_inv _ _ ND) as (NDa & NDb & DISJ).
    destruct i as [|i]; destruct j as [|j]; cbn [nth] in Ea, Eb.
    + f_equal. clear - NDa Ea Eb E. revert k l Ea Eb. induction b0 as [|y b0 IH2]; intros [|k] [|l] Ea Eb; cbn in Ea, Eb; try discriminate.
      * reflexivity.
      * exfalso. inversion NDa as [|y' l' NI _]; subst. apply NI. injection Ea as ->. rewrite E. apply in_map_iff. exists b. split; [reflexivity| eapply nth_error_In; exact Eb].
      * exfalso. inversion NDa as [|y' l' NI _]; subst. apply NI. injection Eb as ->. rewrite <- E. apply in_map_iff. exists a. split; [reflexivity| eapply nth_error_In; exact Ea].
      * f_equal. inversion NDa; subst. eapply IH2; eassumption.
    + exfalso. eapply DISJ; [apply in_map_iff; exists a; split; [reflexivity| eapply nth_error_In; exact Ea]|].
      rewrite E. apply in_map_iff. exists b. split; [reflexivity|]. eapply in_nth_concat. eapply nth_error_In. exact Eb.
    + exfalso. eapply DISJ; [apply in_map_iff; exists b; split; [reflexivity| eapply nth_error_In; exact Eb]|].
      rewrite <- E. apply in_map_iff. exists a. split; [reflexivity|]. eapply in_nth_concat. eapply nth_error_In. exact Ea.
    + pose proof (IH i k j l a b NDb Ea Eb E) as X. injection X as -> ->. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma plseg_fp_not_end : forall m ns c c', plseg m c ns c' ->
  (forall n1 n2, In n1 ns -> In n2 ns -> fst n1 <> fst n2 -> fst n1 + 24 <= fst n2 \/ fst n2 + 24 <= fst n1) ->
  List.NoDup (map fst ns) ->
  (forall n, In n ns -> fst n + 24 <= c \/ c + 8 <= fst n) ->
  ns <> [] ->
  forall a, plseg_fp c ns a -> ~ (c' <= a < c' + 8).
Proof.
  intros m ns. induction ns as [|[A h] ns IH]; intros c c' SEG APN ND APC NE a Ha; [congruence|].
  cbn [plseg] in SEG. destruct SEG as (C & AL & D & HH & HR & R). cbn [plseg_fp] in Ha.
  cbn [map fst] in ND. inversion ND as [|x l NI ND']; subst.
  pose proof (plseg_end _ _ _ _ R) as EC'.
  destruct (pend_where ns (A + 8)) as [[E1 E2]|(pre & Bq & hq & E1 & E2)]; rewrite <- EC' in E2.
  - subst ns. rewrite E2. destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [| lia| lia| destruct Ha].
    pose proof (APC (A, h) ltac:(left; reflexivity)) as X. cbn [fst] in X. lia.
  - assert (INQ : In (Bq, hq) ns) by (rewrite E1; apply in_or_app; right; left; reflexivity).
    assert (NEQ : A <> Bq). { intros E. apply NI. subst Bq. apply in_map_iff. exists (A, hq). auto. }
    pose proof (APN (A, h) (Bq, hq) ltac:(left; reflexivity) ltac:(right; exact INQ) NEQ) as X. cbn [fst] in X.
    destruct Ha as [Ha|[Ha|[Ha|Ha]]].
    + pose proof (APC (Bq, hq) ltac:(right; exact INQ)) as Y. cbn [fst] in Y. rewrite E2. lia.
    + rewrite E2. lia.
    + rewrite E2. lia.
    + eapply (IH (A + 8) c' R); [| exact ND'| | rewrite E1; destruct pre; discriminate| exact Ha].
      * intros n1 n2 H1 H2. apply APN; right; assumption.
      * intros n Hn. assert (NEn : A <> fst n). { intros E. apply NI. rewrite E. apply in_map_iff. exists n. auto. }
        pose proof (APN (A, h) n ltac:(left; reflexivity) ltac:(right; exact Hn) NEn) as Y. cbn [fst] in Y. lia.
Qed.

(* [comment removed for export] *)
Lemma plh_rep_append : forall m2 m3 m4 lh B items bks idx rn An h (d : word) W,
  plh_rep m2 lh B items bks ->
  (lh + 104 <= B \/ B + 128 <= lh) ->
  (forall n, In n (concat bks) -> (fst n + 24 <= lh \/ lh + 104 <= fst n) /\ (fst n + 24 <= B \/ B + 128 <= fst n)) ->
  (forall n1 n2, In n1 (concat bks) -> In n2 (concat bks) -> fst n1 <> fst n2 -> fst n1 + 24 <= fst n2 \/ fst n2 + 24 <= fst n1) ->
  (forall x, In x (plh_L lh B bks) -> An + 24 <= fst x \/ fst x + snd x <= An) ->
  0 <= idx < 8 -> rn = pend (B + 8 * idx) (nth (Z.to_nat idx) bks []) -> 0 <= h < 2 ^ 64 -> An mod 16 = 0 ->
  agree_on (plh_fp lh B bks) m2 m3 ->
  munch W m3 m4 -> (forall a, plh_fp lh B bks a -> ~ (rn <= a < rn + 8) -> ~ (lh + 88 <= a < lh + 104) -> outside W a) ->
  rw_cells asegs m4 rn [C8 (Z_to_bv 64 An)] ->
  rw_cells asegs m4 An [C8 d; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 h)] ->
  rw_cells asegs m4 lh (plh_cells B (items + 1)) ->
  plh_rep m4 lh B (items + 1) (lupd (Z.to_nat idx) (nth (Z.to_nat idx) bks [] ++ [(An, h)]) bks).
Proof.
  intros m2 m3 m4 lh B items bks idx rn An h d W REP APLB APN APNN ANEW IDXR ERN HR AAL AG23 MU34 HW TERM4 NEW SC4.
  pose proof REP as (SC & AL & BL & LEN & IT & CH & EMP & ND).
  inversion ND as [|x l NI1 ND1]; subst x l. inversion ND1 as [|x l NI2 ND2]; subst x l.
  pose proof (agree_of_munch _ _ _ _ MU34 (fun a H => H)) as AG34.
  assert (LI : (Z.to_nat idx < length bks)%nat) by lia.
  pose proof (CH idx ltac:(lia)) as (cend & SEGI & TERMI). pose proof (plseg_end _ _ _ _ SEGI) as EE. rewrite <- ERN in EE. subst cend.
  assert (RNW : (nth (Z.to_nat idx) bks [] = [] /\ rn = B + 8 * idx) \/ (exists pre Ar hr, nth (Z.to_nat idx) bks [] = pre ++ [(Ar, hr)] /\ rn = Ar + 8)).
  { destruct (pend_where (nth (Z.to_nat idx) bks []) (B + 8 * idx)) as [[E1 E2]|(pre & Ar & hr & E1 & E2)]; rewrite <- ERN in E2; [left; auto| right; exists pre, Ar, hr; auto]. }
  assert (NODE_OUT : forall n, In n (concat bks) -> forall a, fst n <= a < fst n + 24 -> ~ (rn <= a < rn + 8) -> outside W a).
  { intros n Hn a Ha NR. apply HW; [right; right; exists n; auto| exact NR|]. destruct (APN n Hn) as [XL _]. lia. }
  assert (CELL_OUT : forall j, 0 <= j < 16 -> j <> idx -> forall a, B + 8 * j <= a < B + 8 * j + 8 -> outside W a).
  { intros j Hj NJ a Ha. apply HW; [right; left; lia| | lia]. destruct RNW as [[_ ->]|(pre & Ar & hr & E1 & ->)]; [lia|].
    assert (INR : In (Ar, hr) (concat bks)) by (eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity).
    destruct (APN _ INR) as [_ X]. cbn [fst] in X. lia. }
  assert (ANEWN : forall n, In n (concat bks) -> An + 24 <= fst n \/ fst n + 24 <= An).
  { intros n Hn. exact (ANEW (fst n, 24) (plh_L_node lh B bks n Hn)). }
  pose proof (ANEW (lh, 104) ltac:(left; reflexivity)) as ANL. pose proof (ANEW (B, 128) ltac:(right; left; reflexivity)) as ANB. cbn [fst snd] in ANL, ANB.
  split; [exact SC4|]. split; [exact AL|]. split; [exact BL|]. split; [rewrite lupd_length; exact LEN|]. split; [lia|].
  split.
  { intros j Hj. destruct (Z.eq_dec j idx) as [->|NJ].
    - (* [comment removed for export] *)
      rewrite nth_lupd_eq by exact LI. exists (An + 8).
      change [C8 d; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 h)] with ([C8 d] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 h)]) in NEW.
      apply (proj1 (rw_cells_app m4 _ _ _)) in NEW. destruct NEW as [ND0 NEW]. apply (proj1 (rw_cells_app m4 _ _ _)) in NEW. destruct NEW as [ND8 ND16].
      csz in ND8. csz in ND16. replace (An + 8 + 8) with (An + 16) in ND16 by lia.
      split; [| exact ND8]. eapply plseg_app.
      + eapply plseg_agree; [eapply plseg_agree; [exact SEGI|]|].
        * eapply agree_sub; [exact AG23|]. intros a Ha. destruct (plseg_fp_where _ _ _ Ha) as [Y|(n & Hn & Y)]; [right; left; lia|].
          right; right. exists n. split; [exact (in_concat_nthZ _ _ _ Hn)| exact Y].
        * eapply agree_sub; [exact AG34|]. intros a Ha.
          destruct RNW as [[E1 ->]|(pre & Ar & hr & E1 & ERN')].
          -- rewrite E1 in Ha. destruct Ha.
          -- assert (NRN : ~ (rn <= a < rn + 8)).
             { eapply (plseg_fp_not_end _ _ _ _ SEGI); [| | | rewrite E1; destruct pre; discriminate| exact Ha].
               - intros n1 n2 H1 H2 NE. apply APNN; [exact (in_concat_nthZ _ _ _ H1)| exact (in_concat_nthZ _ _ _ H2)| exact NE].
               - apply plh_bucket_nodup. exact ND2.
               - intros n Hn. destruct (APN n (in_concat_nthZ _ _ _ Hn)) as [_ X]. lia. }
             destruct (plseg_fp_where _ _ _ Ha) as [Y|(n & Hn & Y)]; [apply HW; [right; left; lia| exact NRN| lia]|].
             exact (NODE_OUT n (in_concat_nthZ _ _ _ Hn) a Y NRN).
      + cbn [plseg]. split; [exact TERM4|]. split; [Z.div_mod_to_equations; lia|]. split; [exists d; exact ND0|]. split; [exact ND16|]. split; [exact HR| reflexivity].
    - rewrite nth_lupd_ne by (clear - NJ Hj IDXR; lia).
      eapply pchain_agree; [exact (CH j Hj)|].
      eapply agree_trans; [eapply agree_sub; [exact AG23|]| eapply agree_sub; [exact AG34|]].
      + intros a [Ha|(n & Hn & Ha)]; [right; left; lia| right; right; exists n; split; [exact (in_concat_nthZ _ _ _ Hn)| exact Ha]].
      + intros a [Ha|(n & Hn & Ha)]; [exact (CELL_OUT j Hj NJ a Ha)|].
        apply (NODE_OUT n (in_concat_nthZ _ _ _ Hn) a Ha).
        destruct RNW as [[_ ->]|(pre & Ar & hr & E1 & ->)].
        * destruct (APN n (in_concat_nthZ _ _ _ Hn)) as [_ X]. lia.
        * (* [comment removed for export] *)
          destruct (In_nth_error _ _ Hn) as [k Hk].
          assert (Hl : nth_error (nth (Z.to_nat idx) bks []) (length pre) = Some (Ar, hr)) by (rewrite E1, nth_error_app2, Nat.sub_diag by lia; reflexivity).
          assert (NEid : fst n <> Ar).
          { pose proof (plh_ids_distinct bks (Z.to_nat j) k (Z.to_nat idx) (length pre) n (Ar, hr) ND2 Hk Hl) as X. cbn [fst] in X. apply X.
            intros EQ. injection EQ as E3 E4. apply NJ. clear - E3 Hj IDXR. apply (f_equal Z.of_nat) in E3. rewrite !Z2Nat.id in E3 by lia. exact E3. }
          assert (INR : In (Ar, hr) (concat bks)) by (eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity).
          pose proof (APNN n (Ar, hr) (in_concat_nthZ _ _ _ Hn) INR NEid) as X. cbn [fst] in X. lia. }
  split. { intros j Hj. rewrite nth_lupd_ne by (clear - Hj IDXR; lia). apply EMP. exact Hj. }
  (* [comment removed for export] *)
  assert (PM : Permutation (concat (lupd (Z.to_nat idx) (nth (Z.to_nat idx) bks [] ++ [(An, h)]) bks)) ((An, h) :: concat bks)).
  { eapply Permutation_trans; [apply concat_lupd; exact LI|].
    eapply Permutation_trans; [| apply perm_skip; apply Permutation_sym; apply (concat_split_perm bks (Z.to_nat idx) LI)].
    rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_cons_app. apply Permutation_refl. }
  eapply Permutation.Permutation_NoDup.
  { apply Permutation_sym. apply perm_skip. apply perm_skip. apply Permutation_map. exact PM. }
  cbn [map fst]. eapply Permutation.Permutation_NoDup; [| constructor; [| exact ND]].
  + eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
  + intros [E|[E|E]]; [lia| lia|].
    apply in_map_iff in E. destruct E as (n & E1 & Hin). pose proof (ANEWN n Hin). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section FromART.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.

(* [comment removed for export] *)
Lemma live_ne_apart2 : forall Σ m x y, ART RT Σ m -> In x (rt_live RT Σ) -> In y (rt_live RT Σ) -> x <> y -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof using AF.
  intros Σ m [p1 n1] [p2 n2] HA I1 I2 NE. cbn [fst snd].
  destruct (in_split _ _ I1) as (l1 & l2 & EL).
  assert (I2' : In (p2, n2) (l1 ++ l2)).
  { rewrite EL in I2. apply in_app_or in I2. apply in_or_app. destruct I2 as [X|[X|X]]; [left; exact X| exfalso; exact (NE X)| right; exact X]. }
  exact (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA EL I2').
Qed.

(* [comment removed for export] *)
Lemma live_head_fresh : forall Σ m x l, ART RT Σ m -> rt_live RT Σ = x :: l -> 0 < snd x -> ~ In x l.
Proof using AF.
  intros Σ m [p n] l HA EL Hn Hin. cbn [snd] in Hn.
  pose proof (af_live_disj RT AF Σ m p n p n [] l HA EL Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma plh_live_facts : forall Σ m lh B items bks lo,
  ART RT Σ m -> plh_rep m lh B items bks -> incl (plh_L lh B bks) (rt_live RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= lo ->
     (acc asegs m lh 104 /\ 0 < lh /\ lh mod 8 = 0 /\ lh + 104 <= lo /\ 0x10007fff8000 <= lh /\ lh + 104 <= 2 ^ 47)
  /\ (acc asegs m B 128 /\ 0 < B /\ B mod 8 = 0 /\ B + 128 <= lo /\ 0x10007fff8000 <= B /\ B + 128 <= 2 ^ 47)
  /\ (forall n, In n (concat bks) -> acc asegs m (fst n) 24 /\ 0 < fst n /\ fst n mod 8 = 0 /\ fst n + 24 <= lo /\ 0x10007fff8000 <= fst n /\ fst n + 24 <= 2 ^ 47)
  /\ (lh + 104 <= B \/ B + 128 <= lh)
  /\ (forall n, In n (concat bks) -> (fst n + 24 <= lh \/ lh + 104 <= fst n) /\ (fst n + 24 <= B \/ B + 128 <= fst n))
  /\ (forall n1 n2, In n1 (concat bks) -> In n2 (concat bks) -> fst n1 <> fst n2 -> fst n1 + 24 <= fst n2 \/ fst n2 + 24 <= fst n1).
Proof using AF AFP.
  intros Σ m lh B items bks lo HA REP HI HLO. pose proof REP as (SC & AL & BL & LEN & IT & CH & EMP & ND).
  assert (INL : In (lh, 104) (rt_live RT Σ)) by (apply HI; left; reflexivity).
  assert (INB : In (B, 128) (rt_live RT Σ)) by (apply HI; right; left; reflexivity).
  assert (INN : forall n, In n (concat bks) -> In (fst n, 24) (rt_live RT Σ)) by (intros n Hn; apply HI; exact (plh_L_node lh B bks n Hn)).
  assert (BLK : forall p n, In (p, n) (rt_live RT Σ) -> 1 <= n <= 64512 -> acc asegs m p n /\ 0 < p /\ p + n <= lo /\ 0x10007fff8000 <= p /\ p + n <= 2 ^ 47).
  { intros p n Hin Hn. pose proof (af_live_range RT AF Σ m p n HA Hin) as (P0 & P1 & _).
    pose proof (afp_live_hi RT GOBJ AFP Σ m p n HA Hin ltac:(lia)) as PH. pose proof (afp_live_mem RT GOBJ AFP Σ m p n HA Hin ltac:(lia)) as [_ PM].
    split; [exact (proj2 (af_acc_live RT AF Σ m p n HA Hin))|]. lia. }
  split. { destruct (BLK lh 104 INL ltac:(lia)) as (A1 & A2 & A3 & A4 & A5). repeat split; try assumption. Z.div_mod_to_equations; lia. }
  split. { destruct (BLK B 128 INB ltac:(lia)) as (A1 & A2 & A3 & A4 & A5). repeat split; try assumption. Z.div_mod_to_equations; lia. }
  split. { intros n Hn. destruct (BLK (fst n) 24 (INN n Hn) ltac:(lia)) as (A1 & A2 & A3 & A4 & A5). repeat split; try assumption.
           destruct (In_nth_error _ _ (proj1 (in_concat _ _) Hn)) as [k Hk] || idtac.
           apply in_concat in Hn. destruct Hn as (b & Hb & Hnb). destruct (In_nth _ _ [] Hb) as (i & Hi & <-).
           pose proof (CH (Z.of_nat i) ltac:(lia)) as (c' & S & _). rewrite Nat2Z.id in S. exact (plseg_aligned _ _ _ _ S n Hnb). }
  split. { exact (live_ne_apart2 Σ m (lh, 104) (B, 128) HA INL INB ltac:(intros E; injection E; lia)). }
  split. { intros n Hn. split.
    - pose proof (live_ne_apart2 Σ m (fst n, 24) (lh, 104) HA (INN n Hn) INL ltac:(intros E; injection E; lia)) as X. cbn [fst snd] in X. exact X.
    - pose proof (live_ne_apart2 Σ m (fst n, 24) (B, 128) HA (INN n Hn) INB ltac:(intros E; injection E; lia)) as X. cbn [fst snd] in X. exact X. }
  intros n1 n2 H1 H2 NE. pose proof (live_ne_apart2 Σ m (fst n1, 24) (fst n2, 24) HA (INN n1 H1) (INN n2 H2) ltac:(intros E; injection E; lia)) as X. cbn [fst snd] in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma plh_fresh_apart : forall Σ m lh B bks An n l,
  ART RT Σ m -> rt_live RT Σ = (An, n) :: l -> 0 < n -> incl (plh_L lh B bks) l ->
  forall x, In x (plh_L lh B bks) -> An + n <= fst x \/ fst x + snd x <= An.
Proof using AF.
  intros Σ m lh B bks An n l HA EL Hn HI x Hx. pose proof (HI x Hx) as INx. destruct x as [p k]. cbn [fst snd].
  pose proof (af_live_disj RT AF Σ m An n p k [] l HA EL INx). lia.
Qed.

End FromART.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_C8_zeros_of_CB : forall m B (k : nat),
  rw_cells asegs m B [CB (8 * k) (repeat (Z_to_bv 8 0) (8 * k))] -> forall i, 0 <= i < Z.of_nat k -> rw_cells asegs m (B + 8 * i) [C8 (wz 0)].
Proof.
  intros m B k H i Hi.
  assert (R : rw_cells asegs m B ([CB (8 * Z.to_nat i) (repeat (Z_to_bv 8 0) (8 * Z.to_nat i))] ++ [CB 8 (repeat (Z_to_bv 8 0) 8)] ++ [CB (8 * (k - Z.to_nat i - 1)) (repeat (Z_to_bv 8 0) (8 * (k - Z.to_nat i - 1)))])).
  { eapply rw_cells_recast; [exact H| cbn; rewrite !repeat_length; repeat split; reflexivity|]. cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- !repeat_app. f_equal. lia. }
  apply (proj1 (rw_cells_app m _ _ _)) in R. destruct R as [_ R]. apply (proj1 (rw_cells_app m _ _ _)) in R. destruct R as [R _].
  cbn [cells_size csize Nat.add] in R. 
  replace (B + Z.of_nat (8 * Z.to_nat i + 0)) with (B + 8 * i) in R by lia.
  eapply rw_cells_recast; [exact R| cbn; repeat split; exact I| reflexivity].
Qed.

Lemma plh_rep_of_cells : forall m lh B,
  rw_cells asegs m lh (plh_cells B 0) -> rw_cells asegs m B [CB 128 (repeat (Z_to_bv 8 0) 128)] -> lh mod 16 = 0 -> B mod 16 = 0 -> lh <> B ->
  plh_rep m lh B 0 (repeat [] 16).
Proof.
  intros m lh B SC HB AL BL NE.
  split; [exact SC|]. split; [exact AL|]. split; [exact BL|]. split; [reflexivity|]. split; [lia|].
  split. { intros i Hi. exists (B + 8 * i). replace (nth (Z.to_nat i) (repeat (@nil pnode) 16) []) with (@nil pnode) by (symmetry; apply nth_repeat).
           split; [reflexivity|]. change 128%nat with (8 * 16)%nat in HB. exact (rw_C8_zeros_of_CB m B 16 HB i Hi). }
  split. { intros i Hi. apply nth_repeat. }
  cbn [concat repeat app map]. constructor; [intros [E|[]]; exact (NE (eq_sym E))|]. constructor; [intros []| constructor].
Qed.
