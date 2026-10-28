(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I1_defs Fz_I1_rep. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_I2_ppi.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation wz := (Z_to_bv 64) (only parsing).

Definition pnode : Type := ((bptr * Z) * Z)%type.
Definition PROP_GEO (items : Z) : lh_geo := mkGeo 8 16 0 8 items.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint plseg (m : mem) (LBall : list block) (L : @clist bptr) (c : Z) (ns : list pnode) (c' : Z) : Prop :=
  match ns with
  | [] => c = c'
  | ((p, A), h) :: ns' => rw_cells usegs m c [C8 (wz A)] /\ cown LBall L p A 24 24 /\ (0 < A /\ A + 24 <= alloc_ceiling)
      /\ (exists d, rw_cells usegs m A [C8 (wz d)]) /\ rw_cells usegs m (A + 16) [C8 (wz h)] /\ 0 <= h < 2 ^ 64
      /\ plseg m LBall L (A + 8) ns' c'
  end.

Definition pchain (m : mem) (LBall : list block) (L : @clist bptr) (c : Z) (ns : list pnode) : Prop :=
  exists c', plseg m LBall L c ns c' /\ rw_cells usegs m c' [C8 (wz 0)].

(* [comment removed for export] *)
Fixpoint pend (c : Z) (ns : list pnode) : Z :=
  match ns with [] => c | ((_, A), _) :: ns' => pend (A + 8) ns' end.

Lemma pend_app : forall ns1 ns2 c, pend c (ns1 ++ ns2) = pend (pend c ns1) ns2.
Proof. induction ns1 as [|[[p A] h] ns1 IH]; intros ns2 c; cbn [pend app]; [reflexivity| apply IH]. Qed.

Lemma plseg_end : forall m LBall L ns c c', plseg m LBall L c ns c' -> c' = pend c ns.
Proof.
  intros m LBall L ns. induction ns as [|[[p A] h] ns IH]; intros c c' H; cbn [plseg pend] in *; [symmetry; exact H|].
  destruct H as (_ & _ & _ & _ & _ & _ & R). exact (IH _ _ R).
Qed.

Lemma plseg_app : forall m LBall L ns1 ns2 c c1 c2, plseg m LBall L c ns1 c1 -> plseg m LBall L c1 ns2 c2 -> plseg m LBall L c (ns1 ++ ns2) c2.
Proof.
  intros m LBall L ns1. induction ns1 as [|[[p A] h] ns1 IH]; intros ns2 c c1 c2 H1 H2; cbn [plseg app] in *.
  - subst c1. exact H2.
  - destruct H1 as (C & O & RG & D & HH & HR & R). repeat (split; [assumption|]). eapply IH; eassumption.
Qed.

Lemma plseg_split : forall m LBall L ns1 ns2 c c2, plseg m LBall L c (ns1 ++ ns2) c2 -> exists c1, plseg m LBall L c ns1 c1 /\ plseg m LBall L c1 ns2 c2.
Proof.
  intros m LBall L ns1. induction ns1 as [|[[p A] h] ns1 IH]; intros ns2 c c2 H; cbn [plseg app] in *.
  - exists c. auto.
  - destruct H as (C & O & RG & D & HH & HR & R). destruct (IH _ _ _ R) as (c1 & R1 & R2). exists c1. split; [| exact R2]. repeat (split; [assumption|]). exact R1.
Qed.

Lemma plseg_ranges : forall m LBall L ns c c', plseg m LBall L c ns c' -> forall n, In n ns -> 0 < snd (fst n) /\ snd (fst n) + 24 <= alloc_ceiling.
Proof.
  intros m LBall L ns. induction ns as [|[[q B] h] ns IH]; intros c c' H n Hin; [destruct Hin|]. cbn [plseg] in H. destruct H as (_ & _ & RG & _ & _ & _ & R).
  destruct Hin as [E|Hin]; [subst n; cbn [fst snd]; exact RG| exact (IH _ _ R n Hin)].
Qed.

Lemma plseg_owns : forall m LBall L ns c c', plseg m LBall L c ns c' -> forall n, In n ns -> cown LBall L (fst (fst n)) (snd (fst n)) 24 24.
Proof.
  intros m LBall L ns. induction ns as [|[[q B] h] ns IH]; intros c c' H n Hin; [destruct Hin|]. cbn [plseg] in H. destruct H as (_ & O & _ & _ & _ & _ & R).
  destruct Hin as [E|Hin]; [subst n; cbn [fst snd]; exact O| exact (IH _ _ R n Hin)].
Qed.

Lemma plseg_hashes : forall m LBall L ns c c', plseg m LBall L c ns c' -> forall n, In n ns -> 0 <= snd n < 2 ^ 64.
Proof.
  intros m LBall L ns. induction ns as [|[[q B] h] ns IH]; intros c c' H n Hin; [destruct Hin|]. cbn [plseg] in H. destruct H as (_ & _ & _ & _ & _ & HR & R).
  destruct Hin as [E|Hin]; [subst n; cbn [snd]; exact HR| exact (IH _ _ R n Hin)].
Qed.

Lemma plseg_end_range : forall m LBall L ns c c', plseg m LBall L c ns c' -> 0 <= c /\ c + 8 <= alloc_ceiling -> 0 <= c' /\ c' + 8 <= alloc_ceiling.
Proof.
  intros m LBall L ns. induction ns as [|[[q B] h] ns IH]; intros c c' H HC; cbn [plseg] in H; [subst; exact HC|].
  destruct H as (_ & _ & RG & _ & _ & _ & R). apply (IH _ _ R). lia.
Qed.

(* [comment removed for export] *)
Lemma pend_where : forall ns c, (ns = [] /\ pend c ns = c) \/ (exists pre p A h, ns = pre ++ [((p, A), h)] /\ pend c ns = A + 8).
Proof.
  induction ns as [|[[q B] h] ns IH]; intros c; cbn [pend]; [left; auto| right].
  destruct (IH (B + 8)) as [[-> E]|(pre & p & A & h' & -> & E)].
  - exists [], q, B, h. auto.
  - exists (((q, B), h) :: pre), p, A, h'. auto.
Qed.

(* [comment removed for export] *)
Fixpoint plseg_fp (c : Z) (ns : list pnode) (a : Z) : Prop :=
  match ns with
  | [] => False
  | ((p, A), h) :: ns' => (c <= a < c + 8) \/ (A <= a < A + 8) \/ (A + 16 <= a < A + 24) \/ plseg_fp (A + 8) ns' a
  end.

(* [comment removed for export] *)
Definition pns_fp (c : Z) (ns : list pnode) (a : Z) : Prop := (c <= a < c + 8) \/ exists n, In n ns /\ snd (fst n) <= a < snd (fst n) + 24.

Lemma plseg_fp_where : forall ns c a, plseg_fp c ns a -> pns_fp c ns a.
Proof.
  induction ns as [|[[p A] h] ns IH]; intros c a H; cbn [plseg_fp] in H; [destruct H|]. unfold pns_fp.
  destruct H as [H|[H|[H|H]]]; [left; exact H| right; exists ((p, A), h); split; [left; reflexivity| cbn [fst snd]; lia]| right; exists ((p, A), h); split; [left; reflexivity| cbn [fst snd]; lia]|].
  destruct (IH _ _ H) as [H1|(n & Hn & H1)]; [right; exists ((p, A), h); split; [left; reflexivity| cbn [fst snd]; lia]| right; exists n; split; [right; exact Hn| exact H1]].
Qed.

Lemma plseg_agree : forall m m' LBall L LBall' L' ns c c',
  plseg m LBall L c ns c' -> agree_on (plseg_fp c ns) m m' ->
  (forall n, In n ns -> cown LBall L (fst (fst n)) (snd (fst n)) 24 24 -> cown LBall' L' (fst (fst n)) (snd (fst n)) 24 24) ->
  plseg m' LBall' L' c ns c'.
Proof.
  intros m m' LBall L LBall' L' ns. induction ns as [|[[p A] h] ns IH]; intros c c' H AG HO; cbn [plseg] in *; [exact H|].
  destruct H as (C & O & RG & (d & D) & HH & HR & R).
  split. { eapply rw_cells_agree; [exact AG| exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. cbn [plseg_fp]. left. lia. }
  split. { apply (HO ((p, A), h)); [left; reflexivity| exact O]. }
  split; [exact RG|].
  split. { exists d. eapply rw_cells_agree; [exact AG| exact D|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. cbn [plseg_fp]. right; left. lia. }
  split. { eapply rw_cells_agree; [exact AG| exact HH|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. cbn [plseg_fp]. right; right; left. lia. }
  split; [exact HR|].
  apply IH; [exact R| | intros n Hn; apply HO; right; exact Hn].
  eapply agree_on_mono; [exact AG|]. intros a Ha. cbn [plseg_fp]. do 3 right. exact Ha.
Qed.

Lemma pchain_agree : forall m m' LBall L LBall' L' ns c,
  pchain m LBall L c ns -> agree_on (pns_fp c ns) m m' ->
  (forall n, In n ns -> cown LBall L (fst (fst n)) (snd (fst n)) 24 24 -> cown LBall' L' (fst (fst n)) (snd (fst n)) 24 24) ->
  pchain m' LBall' L' c ns.
Proof.
  intros m m' LBall L LBall' L' ns c (c' & S & Z0) AG HO. exists c'.
  split; [eapply plseg_agree; [exact S| eapply agree_on_mono; [exact AG| intros a Ha; exact (plseg_fp_where _ _ _ Ha)]| exact HO]|].
  eapply rw_cells_agree; [exact AG| exact Z0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha.
  rewrite (plseg_end _ _ _ _ _ _ S) in Ha. destruct (pend_where ns c) as [[E1 E2]|(pre & p & A & h & E1 & E2)]; rewrite E2 in Ha.
  - left. exact Ha.
  - right. exists ((p, A), h). split; [rewrite E1; apply in_or_app; right; left; reflexivity| cbn [fst snd]; lia].
Qed.

Lemma plseg_munch : forall W m m' LBall L ns c c', plseg m LBall L c ns c' -> munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < alloc_ceiling -> outside W a) -> 0 <= c /\ c + 8 <= alloc_ceiling -> plseg m' LBall L c ns c'.
Proof.
  intros W m m' LBall L ns c c' H MU WM HW HC. eapply plseg_agree; [exact H| | intros n _ X; exact X].
  eapply agree_on_mono; [exact (agree_on_of_munch W m m' MU WM)|]. intros a Ha. apply HW.
  destruct (plseg_fp_where _ _ _ Ha) as [X|(n & Hn & X)]; [lia|]. pose proof (plseg_ranges _ _ _ _ _ _ H n Hn). lia.
Qed.

Lemma pchain_munch : forall W m m' LBall L ns c, pchain m LBall L c ns -> munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < alloc_ceiling -> outside W a) -> 0 <= c /\ c + 8 <= alloc_ceiling -> pchain m' LBall L c ns.
Proof.
  intros W m m' LBall L ns c H MU WM HW HC. eapply pchain_agree; [exact H| | intros n _ X; exact X].
  destruct H as (c' & S & Z0).
  eapply agree_on_mono; [exact (agree_on_of_munch W m m' MU WM)|]. intros a Ha. apply HW.
  destruct Ha as [X|(n & Hn & X)]; [lia|]. pose proof (plseg_ranges _ _ _ _ _ _ S n Hn). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition plh_rep (m : mem) (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B items : Z) (bks : list (list pnode)) : Prop :=
     cown LBall L pl lh 104 104 /\ (0 < lh /\ lh + 104 <= alloc_ceiling)
  /\ (exists x40 x48 err pad, rw_cells usegs m lh (lh_cells PROP_FNS B (PROP_GEO items) x40 x48 err pad))
  /\ cown LBall L pb B 128 128 /\ (0 < B /\ B + 128 <= alloc_ceiling)
  /\ length bks = 16%nat /\ 0 <= items
  /\ (forall i, 0 <= i < 16 -> pchain m LBall L (B + 8 * i) (nth (Z.to_nat i) bks []))
  /\ (forall i, 8 <= i < 16 -> nth (Z.to_nat i) bks [] = [])
  /\ List.NoDup (pl :: pb :: map fst (map fst (concat bks))).

(* [comment removed for export] *)
Definition plh_T (pl pb : bptr) (bks : list (list pnode)) (q : bptr) : Prop := q = pl \/ q = pb \/ In q (map fst (map fst (concat bks))).

Definition plh_fp (lh B : Z) (bks : list (list pnode)) (a : Z) : Prop :=
  (lh <= a < lh + 104) \/ (B <= a < B + 128) \/ exists n, In n (concat bks) /\ snd (fst n) <= a < snd (fst n) + 24.

Lemma in_concat_nthZ : forall (bks : list (list pnode)) i n, In n (nth (Z.to_nat i) bks []) -> In n (concat bks).
Proof. intros bks i n H. exact (in_nth_concat _ _ _ H). Qed.

Lemma plh_rep_agree : forall m m' LBall L LBall' L' lh pl pb B items bks,
  plh_rep m LBall L lh pl pb B items bks -> agree_on (plh_fp lh B bks) m m' ->
  (forall q A n nm, plh_T pl pb bks q -> cown LBall L q A n nm -> cown LBall' L' q A n nm) ->
  plh_rep m' LBall' L' lh pl pb B items bks.
Proof.
  intros m m' LBall L LBall' L' lh pl pb B items bks (OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN & IT & CH & EMP & ND) AG HO.
  split; [apply HO; [left; reflexivity| exact OL]|]. split; [exact RL|].
  split. { exists x40, x48, err, pad. eapply rw_cells_agree; [exact AG| exact SC|]. intros a Ha. left. cbn in Ha. lia. }
  split; [apply HO; [right; left; reflexivity| exact OB]|]. split; [exact RB|]. split; [exact LEN|]. split; [exact IT|].
  split; [| split; [exact EMP| exact ND]].
  intros i Hi. eapply pchain_agree; [exact (CH i Hi)| |].
  - eapply agree_on_mono; [exact AG|]. intros a [Ha|(n & Hn & Ha)].
    + right; left. lia.
    + right; right. exists n. split; [exact (in_concat_nthZ _ _ _ Hn)| exact Ha].
  - intros n Hn. apply HO. right; right. apply in_map_iff. exists (fst n). split; [reflexivity|]. apply in_map_iff. exists n. split; [reflexivity|]. exact (in_concat_nthZ _ _ _ Hn).
Qed.

(* [comment removed for export] *)
Lemma plh_rep_munch : forall W m m' LBall L lh pl pb B items bks,
  plh_rep m LBall L lh pl pb B items bks -> munch W m m' -> wmono usegs m m' -> (forall a, 0 <= a < alloc_ceiling -> outside W a) ->
  plh_rep m' LBall L lh pl pb B items bks.
Proof.
  intros W m m' LBall L lh pl pb B items bks REP MU WM HW. eapply plh_rep_agree; [exact REP| | intros q A n nm _ X; exact X].
  pose proof REP as (OL & RL & _ & OB & RB & LEN & IT & CH & _).
  eapply agree_on_mono; [exact (agree_on_of_munch W m m' MU WM)|]. intros a [Ha|[Ha|(n & Hn & Ha)]]; apply HW; [lia| lia|].
  apply in_concat in Hn. destruct Hn as (ns & Hns & Hn). destruct (In_nth _ _ [] Hns) as (i & Hi & E). subst ns.
  assert (IR : 0 <= Z.of_nat i < 16) by lia. pose proof (CH (Z.of_nat i) IR) as (c' & S & _). rewrite Nat2Z.id in S.
  pose proof (plseg_ranges _ _ _ _ _ _ S n Hn). lia.
Qed.

(* [comment removed for export] *)
Lemma plh_rep_blocks : forall m LBall L lh pl pb B items bks,
  plh_rep m LBall L lh pl pb B items bks ->
  In (pl, lh, 104) LBall /\ In (pb, B, 128) LBall /\ (forall n, In n (concat bks) -> In (fst (fst n), snd (fst n), 24) LBall).
Proof.
  intros m LBall L lh pl pb B items bks (OL & _ & _ & OB & _ & LEN & _ & CH & _).
  split; [exact (proj1 OL)|]. split; [exact (proj1 OB)|].
  intros n Hn. apply in_concat in Hn. destruct Hn as (ns & Hns & Hn). destruct (In_nth _ _ [] Hns) as (i & Hi & E). subst ns.
  assert (IR : 0 <= Z.of_nat i < 16) by lia. pose proof (CH (Z.of_nat i) IR) as (c' & S & _). rewrite Nat2Z.id in S.
  exact (proj1 (plseg_owns _ _ _ _ _ _ S n Hn)).
Qed.

(* [comment removed for export] *)
Lemma plh_rep_cframe : forall (m m' : mem) T W SP s LBall L s' LBall' L' lh pl pb B items bks,
  plh_rep m LBall L lh pl pb B items bks -> cframe T W SP s LBall L m s' LBall' L' m' -> (forall q, plh_T pl pb bks q -> ~ T q) ->
  plh_rep m' LBall' L' lh pl pb B items bks.
Proof.
  intros m m' T W SP s LBall L s' LBall' L' lh pl pb B items bks REP (CFR & [K1 K2] & _) NT.
  destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (IL & IB & IN).
  eapply plh_rep_agree; [exact REP| |].
  - eapply agree_on_mono; [exact CFR|]. intros a [Ha|[Ha|(n & Hn & Ha)]]; right; left.
    + exists (pl, lh, 104). split; [exact IL|]. split; [apply NT; left; reflexivity|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
    + exists (pb, B, 128). split; [exact IB|]. split; [apply NT; right; left; reflexivity|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
    + exists (fst (fst n), snd (fst n), 24). split; [exact (IN n Hn)|]. split; [| unfold blk_addr, blk_size; cbn [fst snd]; lia].
      apply NT. right; right. apply in_map_iff. exists (fst n). split; [reflexivity|]. apply in_map_iff. exists n. auto.
  - intros q A n nm Hq [I1 I2]. split; [apply K1; [exact I1| apply NT; exact Hq]| apply K2; [exact I2| apply NT; exact Hq]].
Qed.

(* [comment removed for export] *)
Lemma plh_sep : forall s m0 m LBall L lh pl pb B items bks, RHEAP s LBall m0 -> plh_rep m LBall L lh pl pb B items bks ->
  (lh + 104 <= B \/ B + 128 <= lh)
  /\ (forall n, In n (concat bks) -> (snd (fst n) + 24 <= lh \/ lh + 104 <= snd (fst n)) /\ (snd (fst n) + 24 <= B \/ B + 128 <= snd (fst n)))
  /\ (forall n1 n2, In n1 (concat bks) -> In n2 (concat bks) -> fst (fst n1) <> fst (fst n2) -> snd (fst n1) + 24 <= snd (fst n2) \/ snd (fst n2) + 24 <= snd (fst n1)).
Proof.
  intros s m0 m LBall L lh pl pb B items bks HP REP. destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (IL & IB & IN).
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ND).
  inversion ND as [|x l NI1 ND1]; subst. inversion ND1 as [|x l NI2 ND2]; subst.
  assert (IDS : forall n, In n (concat bks) -> In (fst (fst n)) (map fst (map fst (concat bks)))).
  { intros n Hn. apply in_map_iff. exists (fst n). split; [reflexivity|]. apply in_map_iff. exists n. auto. }
  split. { eapply (own_apart s LBall m0 pl lh 104 pb B 128 HP IL IB). intros E. apply NI1. left. symmetry. exact E. }
  split. { intros n Hn. split.
    - eapply (own_apart s LBall m0 (fst (fst n)) (snd (fst n)) 24 pl lh 104 HP (IN n Hn) IL). intros E. apply NI1. right. rewrite <- E. exact (IDS n Hn).
    - eapply (own_apart s LBall m0 (fst (fst n)) (snd (fst n)) 24 pb B 128 HP (IN n Hn) IB). intros E. apply NI2. rewrite <- E. exact (IDS n Hn). }
  intros n1 n2 H1 H2 NE. exact (own_apart s LBall m0 _ _ 24 _ _ 24 HP (IN n1 H1) (IN n2 H2) NE).
Qed.

Lemma nodup_app_inv : forall {A : Type} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1 /\ List.NoDup l2 /\ (forall a, In a l1 -> ~ In a l2).
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros l2 ND; cbn [app] in ND.
  - split; [constructor|]. split; [exact ND|]. intros a [].
  - inversion ND as [|x' l' NI ND']; subst. destruct (IH _ ND') as (A1 & A2 & A3).
    split; [constructor; [intros X; apply NI; apply in_or_app; left; exact X| exact A1]|]. split; [exact A2|].
    intros a [<-|Ha] Hb; [apply NI; apply in_or_app; right; exact Hb| exact (A3 a Ha Hb)].
Qed.

Lemma plh_bucket_nodup : forall (bks : list (list pnode)) i, List.NoDup (map fst (map fst (concat bks))) -> List.NoDup (map fst (map fst (nth i bks []))).
Proof.
  induction bks as [|b bks IH]; intros i ND.
  - destruct i; cbn; constructor.
  - cbn [concat] in ND. rewrite !map_app in ND. destruct (nodup_app_inv _ _ ND) as (N1 & N2 & _).
    destruct i as [|i]; cbn [nth]; [exact N1| exact (IH i N2)].
Qed.

(* [comment removed for export] *)
Lemma plseg_fp_not_end : forall m LBall L ns c c', plseg m LBall L c ns c' ->
  (forall n1 n2, In n1 ns -> In n2 ns -> fst (fst n1) <> fst (fst n2) -> snd (fst n1) + 24 <= snd (fst n2) \/ snd (fst n2) + 24 <= snd (fst n1)) ->
  List.NoDup (map fst (map fst ns)) ->
  (forall n, In n ns -> snd (fst n) + 24 <= c \/ c + 8 <= snd (fst n)) ->
  ns <> [] ->
  forall a, plseg_fp c ns a -> ~ (c' <= a < c' + 8).
Proof.
  intros m LBall L ns. induction ns as [|[[p A] h] ns IH]; intros c c' SEG APN ND APC NE a Ha; [congruence|].
  cbn [plseg] in SEG. destruct SEG as (C & O & RG & D & HH & HR & R). cbn [plseg_fp] in Ha.
  cbn [map fst] in ND. inversion ND as [|x l NI ND']; subst.
  pose proof (plseg_end _ _ _ _ _ _ R) as EC'.
  destruct (pend_where ns (A + 8)) as [[E1 E2]|(pre & q & Bq & hq & E1 & E2)]; rewrite <- EC' in E2.
  - subst ns. rewrite E2. destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [| lia| lia| destruct Ha].
    pose proof (APC ((p, A), h) ltac:(left; reflexivity)) as X. cbn [fst snd] in X. lia.
  - assert (INQ : In ((q, Bq), hq) ns) by (rewrite E1; apply in_or_app; right; left; reflexivity).
    assert (NEQ : p <> q). { intros E. apply NI. subst q. apply in_map_iff. exists (p, Bq). split; [reflexivity|]. apply in_map_iff. exists ((p, Bq), hq). auto. }
    pose proof (APN ((p, A), h) ((q, Bq), hq) ltac:(left; reflexivity) ltac:(right; exact INQ) NEQ) as X. cbn [fst snd] in X.
    destruct Ha as [Ha|[Ha|[Ha|Ha]]].
    + pose proof (APC ((q, Bq), hq) ltac:(right; exact INQ)) as Y. cbn [fst snd] in Y. rewrite E2. lia.
    + rewrite E2. lia.
    + rewrite E2. lia.
    + eapply (IH (A + 8) c' R); [| exact ND'| | rewrite E1; destruct pre; discriminate| exact Ha].
      * intros n1 n2 H1 H2. apply APN; right; assumption.
      * intros n Hn. assert (NEn : p <> fst (fst n)). { intros E. apply NI. rewrite E. apply in_map_iff. exists (fst n). split; [reflexivity|]. apply in_map_iff. exists n. auto. }
        pose proof (APN ((p, A), h) n ltac:(left; reflexivity) ltac:(right; exact Hn) NEn) as Y. cbn [fst snd] in Y. lia.
Qed.

(* [comment removed for export] *)
Lemma plh_ids_distinct : forall (bks : list (list pnode)) i k j l n1 n2, List.NoDup (map fst (map fst (concat bks))) ->
  nth_error (nth i bks []) k = Some n1 -> nth_error (nth j bks []) l = Some n2 -> (i, k) <> (j, l) -> fst (fst n1) <> fst (fst n2).
Proof.
  intros bks i k j l n1 n2 ND E1 E2 NE E. apply NE. rewrite map_map in ND. clear NE. revert i k j l n1 n2 ND E1 E2 E.
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

Lemma plh_nodes_apart : forall s m0 m LBall L lh pl pb B items bks i j k l n1 n2, RHEAP s LBall m0 -> plh_rep m LBall L lh pl pb B items bks ->
  nth_error (nth i bks []) k = Some n1 -> nth_error (nth j bks []) l = Some n2 -> (i, k) <> (j, l) ->
  snd (fst n1) + 24 <= snd (fst n2) \/ snd (fst n2) + 24 <= snd (fst n1).
Proof.
  intros s m0 m LBall L lh pl pb B items bks i j k l n1 n2 HP REP E1 E2 NE.
  destruct (plh_sep _ _ _ _ _ _ _ _ _ _ _ HP REP) as (_ & _ & APN).
  pose proof REP as (_ & _ & _ & _ & _ & LEN & _ & _ & _ & ND). inversion ND as [|x l0 _ ND1]; subst x l0. inversion ND1 as [|x l0 _ ND2]; subst x l0.
  apply APN; [eapply in_nth_concat; eapply nth_error_In; exact E1| eapply in_nth_concat; eapply nth_error_In; exact E2|].
  exact (plh_ids_distinct bks i k j l n1 n2 ND2 E1 E2 NE).
Qed.

(* [comment removed for export] *)
Lemma plh_rep_errw : forall s m0 W m mc LBall L lh pl pb B items bks (x40 x48 err' pad' : word),
  RHEAP s LBall m0 -> plh_rep m LBall L lh pl pb B items bks ->
  munch W m mc -> wmono usegs m mc -> (forall a, 0 <= a < alloc_ceiling -> ~ (lh + 96 <= a < lh + 104) -> outside W a) ->
  rw_cells usegs mc lh (lh_cells PROP_FNS B (PROP_GEO items) x40 x48 err' pad') ->
  plh_rep mc LBall L lh pl pb B items bks.
Proof.
  intros s m0 W m mc LBall L lh pl pb B items bks x40 x48 err' pad' HP REP MU WM HW SC.
  destruct (plh_sep _ _ _ _ _ _ _ _ _ _ _ HP REP) as (APLB & APN & _).
  pose proof REP as (OL & RL & _ & OB & RB & LEN & IT & CH & EMP & ND).
  split; [exact OL|]. split; [exact RL|]. split; [exists x40, x48, err', pad'; exact SC|]. split; [exact OB|]. split; [exact RB|]. split; [exact LEN|]. split; [exact IT|].
  split; [| split; [exact EMP| exact ND]].
  intros i Hi. pose proof (CH i Hi) as CHI. eapply pchain_agree; [exact CHI| | intros n _ X; exact X].
  eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. intros a [Ha|(n & Hn & Ha)]; apply HW; try lia.
  - pose proof (in_concat_nthZ _ _ _ Hn) as Hc. destruct (APN n Hc) as [X _]. destruct CHI as (c' & SS & _). pose proof (plseg_ranges _ _ _ _ _ _ SS n Hn). lia.
  - pose proof (in_concat_nthZ _ _ _ Hn) as Hc. destruct (APN n Hc) as [X _]. lia.
Qed.

(* [comment removed for export] *)
Lemma plh_rep_blockw : forall s m0 W m mc LBall L lh pl pb B items bks (q : bptr) (Aq nq : Z),
  RHEAP s LBall m0 -> plh_rep m LBall L lh pl pb B items bks -> In (q, Aq, nq) LBall -> ~ plh_T pl pb bks q ->
  munch W m mc -> wmono usegs m mc -> (forall a, 0 <= a < alloc_ceiling -> ~ (Aq <= a < Aq + nq) -> outside W a) ->
  plh_rep mc LBall L lh pl pb B items bks.
Proof.
  intros s m0 W m mc LBall L lh pl pb B items bks q Aq nq HP REP INQ NT MU WM HW.
  destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (INL & INB & INN).
  pose proof REP as (OL & RL & _ & OB & RB & LEN & IT & CH & EMP & ND).
  assert (APL : lh + 104 <= Aq \/ Aq + nq <= lh) by (eapply (own_apart _ _ _ pl lh 104 q Aq nq HP INL INQ); intros E; apply NT; left; symmetry; exact E).
  assert (APB : B + 128 <= Aq \/ Aq + nq <= B) by (eapply (own_apart _ _ _ pb B 128 q Aq nq HP INB INQ); intros E; apply NT; right; left; symmetry; exact E).
  assert (APN : forall n, In n (concat bks) -> snd (fst n) + 24 <= Aq \/ Aq + nq <= snd (fst n)).
  { intros n Hn. eapply (own_apart _ _ _ (fst (fst n)) (snd (fst n)) 24 q Aq nq HP (INN n Hn) INQ). intros E. apply NT. right; right.
    apply in_map_iff. exists (fst n). split; [exact E|]. apply in_map_iff. exists n. auto. }
  eapply plh_rep_agree; [exact REP| | intros q0 A n nm _ X; exact X].
  eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. intros a [Ha|[Ha|(n & Hn & Ha)]]; apply HW; try lia.
  - pose proof (INN n Hn) as X. pose proof (RHEAP_block_range_proof _ _ _ _ HP X) as (R1 & _ & _ & R2 & _). unfold blk_addr, blk_size in R1, R2. cbn [fst snd] in R1, R2. lia.
  - pose proof (APN n Hn). lia.
Qed.

(* [comment removed for export] *)
Lemma plh_rep_after : forall s m0 W m mc LBall L lh pl pb B items bks (q : bptr) (Aq nq : Z) (x40 x48 err' pad' : word),
  RHEAP s LBall m0 -> plh_rep m LBall L lh pl pb B items bks -> In (q, Aq, nq) LBall -> ~ plh_T pl pb bks q ->
  munch W m mc -> wmono usegs m mc ->
  (forall a, 0 <= a < alloc_ceiling -> ~ (Aq <= a < Aq + nq) -> ~ (lh + 96 <= a < lh + 104) -> outside W a) ->
  rw_cells usegs mc lh (lh_cells PROP_FNS B (PROP_GEO items) x40 x48 err' pad') ->
  plh_rep mc LBall L lh pl pb B items bks.
Proof.
  intros s m0 W m mc LBall L lh pl pb B items bks q Aq nq x40 x48 err' pad' HP REP INQ NT MU WM HW SC.
  destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (INL & INB & INN).
  destruct (plh_sep _ _ _ _ _ _ _ _ _ _ _ HP REP) as (APLB & APN & _).
  pose proof REP as (OL & RL & _ & OB & RB & LEN & IT & CH & EMP & ND).
  assert (APB : B + 128 <= Aq \/ Aq + nq <= B) by (eapply (own_apart _ _ _ pb B 128 q Aq nq HP INB INQ); intros E; apply NT; right; left; symmetry; exact E).
  assert (APQ : forall n, In n (concat bks) -> snd (fst n) + 24 <= Aq \/ Aq + nq <= snd (fst n)).
  { intros n Hn. eapply (own_apart _ _ _ (fst (fst n)) (snd (fst n)) 24 q Aq nq HP (INN n Hn) INQ). intros E. apply NT. right; right.
    apply in_map_iff. exists (fst n). split; [exact E|]. apply in_map_iff. exists n. auto. }
  split; [exact OL|]. split; [exact RL|]. split; [exists x40, x48, err', pad'; exact SC|]. split; [exact OB|]. split; [exact RB|]. split; [exact LEN|]. split; [exact IT|].
  split; [| split; [exact EMP| exact ND]].
  intros i Hi. pose proof (CH i Hi) as CHI. eapply pchain_agree; [exact CHI| | intros n _ X; exact X].
  eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. intros a [Ha|(n & Hn & Ha)]; apply HW; try lia.
  - pose proof (in_concat_nthZ _ _ _ Hn) as Hc. destruct (APN n Hc) as [X _]. pose proof (APQ n Hc). destruct CHI as (c' & SS & _). pose proof (plseg_ranges _ _ _ _ _ _ SS n Hn). lia.
  - pose proof (in_concat_nthZ _ _ _ Hn) as Hc. pose proof (APQ n Hc). lia.
  - pose proof (in_concat_nthZ _ _ _ Hn) as Hc. destruct (APN n Hc) as [X _]. lia.
Qed.

(* [comment removed for export] *)
Lemma plh_rep_append : forall s3 m2 m3 m4 LBall L lh pl pb B items bks idx rn (pn : bptr) An h d (x40 x48 err pad : word),
  plh_rep m2 LBall L lh pl pb B items bks -> RHEAP s3 ((pn, An, 24) :: LBall) m3 ->
  (forall q A0 n0, In (q, A0, n0) LBall -> pn <> q) ->
  0 <= idx < 8 -> rn = pend (B + 8 * idx) (nth (Z.to_nat idx) bks []) -> 0 <= h < 2 ^ 64 -> 0 < An -> An + 24 <= alloc_ceiling ->
  agree_on (plh_fp lh B bks) m2 m3 ->
  munch [(An, An + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z m3 m4 -> wmono usegs m3 m4 ->
  rw_cells usegs m4 rn [C8 (Z_to_bv 64 An)] ->
  rw_cells usegs m4 An [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 h)] ->
  rw_cells usegs m4 lh (lh_cells PROP_FNS B (PROP_GEO (items + 1)) x40 x48 err pad) ->
  plh_rep m4 ((pn, An, 24) :: LBall) ((pn, 24) :: L) lh pl pb B (items + 1) (lupd (Z.to_nat idx) (nth (Z.to_nat idx) bks [] ++ [((pn, An), h)]) bks).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s3 m2 m3 m4 LBall L lh pl pb B items bks idx rn pn An h d x40 x48 err pad REP HP3 PNEW IDXR ERN HR An0 AnC AG23 MU3 WM3 TERM3 NEW SC4.
  pose proof REP as (OL & RL & _ & OB & RB & LEN & IT & CH & EMP & ND).
  destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (INL & INB & INN).
  assert (IDS : forall n, In n (concat bks) -> In (fst (fst n)) (map fst (map fst (concat bks)))).
  { intros n Hn. apply in_map_iff. exists (fst n). split; [reflexivity|]. apply in_map_iff. exists n. auto. }
  pose proof ND as NDc. inversion NDc as [|x l NI1 ND1]; subst x l. inversion ND1 as [|x l NI2 ND2]; subst x l.
  assert (APLB : lh + 104 <= B \/ B + 128 <= lh).
  { eapply (own_apart _ _ _ pl lh 104 pb B 128 HP3); [right; exact INL| right; exact INB|]. intros E. apply NI1. left. symmetry. exact E. }
  assert (APN : forall n, In n (concat bks) -> (snd (fst n) + 24 <= lh \/ lh + 104 <= snd (fst n)) /\ (snd (fst n) + 24 <= B \/ B + 128 <= snd (fst n))).
  { intros n Hn. split.
    - eapply (own_apart _ _ _ (fst (fst n)) (snd (fst n)) 24 pl lh 104 HP3); [right; exact (INN n Hn)| right; exact INL|]. intros E. apply NI1. right. rewrite <- E. exact (IDS n Hn).
    - eapply (own_apart _ _ _ (fst (fst n)) (snd (fst n)) 24 pb B 128 HP3); [right; exact (INN n Hn)| right; exact INB|]. intros E. apply NI2. rewrite <- E. exact (IDS n Hn). }
  assert (APNN : forall n1 n2, In n1 (concat bks) -> In n2 (concat bks) -> fst (fst n1) <> fst (fst n2) -> snd (fst n1) + 24 <= snd (fst n2) \/ snd (fst n2) + 24 <= snd (fst n1)).
  { intros n1 n2 H1 H2 NE. exact (own_apart _ _ _ _ _ 24 _ _ 24 HP3 (or_intror (INN n1 H1)) (or_intror (INN n2 H2)) NE). }
  assert (APA : forall n, In n (concat bks) -> An + 24 <= snd (fst n) \/ snd (fst n) + 24 <= An).
  { intros n Hn. eapply (own_apart _ _ _ pn An 24 (fst (fst n)) (snd (fst n)) 24 HP3); [left; reflexivity| right; exact (INN n Hn)|]. exact (PNEW _ _ _ (INN n Hn)). }
  assert (APAL : An + 24 <= lh \/ lh + 104 <= An) by (eapply (own_apart _ _ _ pn An 24 pl lh 104 HP3); [left; reflexivity| right; exact INL| exact (PNEW _ _ _ INL)]).
  assert (APAB : An + 24 <= B \/ B + 128 <= An) by (eapply (own_apart _ _ _ pn An 24 pb B 128 HP3); [left; reflexivity| right; exact INB| exact (PNEW _ _ _ INB)]).
  pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG34.
  assert (LI : (Z.to_nat idx < length bks)%nat) by lia.
  pose proof (CH idx ltac:(lia)) as (cend & SEGI & TERMI). pose proof (plseg_end _ _ _ _ _ _ SEGI) as EE. rewrite <- ERN in EE. subst cend.
  assert (RNW : (nth (Z.to_nat idx) bks [] = [] /\ rn = B + 8 * idx) \/ (exists pre pr Ar hr, nth (Z.to_nat idx) bks [] = pre ++ [((pr, Ar), hr)] /\ rn = Ar + 8)).
  { destruct (pend_where (nth (Z.to_nat idx) bks []) (B + 8 * idx)) as [[E1 E2]|(pre & pr & Ar & hr & E1 & E2)]; rewrite <- ERN in E2; [left; auto| right; exists pre, pr, Ar, hr; auto]. }
  assert (NODE_OUT : forall n, In n (concat bks) -> forall a, snd (fst n) <= a < snd (fst n) + 24 -> ~ (rn <= a < rn + 8) ->
            outside [(An, An + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z a).
  { intros n Hn a Ha NR. pose proof (APA n Hn). destruct (APN n Hn) as [XL _]. cbn [outside]. lia. }
  assert (CELL_OUT : forall j, 0 <= j < 16 -> j <> idx -> forall a, B + 8 * j <= a < B + 8 * j + 8 -> outside [(An, An + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z a).
  { intros j Hj NJ a Ha. cbn [outside]. destruct RNW as [[_ ->]|(pre & pr & Ar & hr & E1 & ->)]; [lia|].
    assert (INR : In ((pr, Ar), hr) (concat bks)) by (eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity).
    destruct (APN _ INR) as [_ X]. cbn [fst snd] in X. lia. }
  assert (OWNS : forall n : pnode, cown LBall L (fst (fst n)) (snd (fst n)) 24 24 -> cown ((pn, An, 24) :: LBall) ((pn, 24) :: L) (fst (fst n)) (snd (fst n)) 24 24) by (intros; apply cown_cons; assumption).
  split; [apply cown_cons; exact OL|]. split; [exact RL|]. split; [exists x40, x48, err, pad; exact SC4|]. split; [apply cown_cons; exact OB|]. split; [exact RB|].
  split; [rewrite lupd_length; exact LEN|]. split; [lia|].
  split.
  { intros j Hj. destruct (Z.eq_dec j idx) as [->|NJ].
    - (* [comment removed for export] *)
      rewrite nth_lupd_eq by exact LI. exists (An + 8).
      change [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 h)] with ([C8 (Z_to_bv 64 d)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 h)]) in NEW.
      apply (proj1 (rw_cells_app usegs m4 _ _ _)) in NEW. destruct NEW as [ND0 NEW]. apply (proj1 (rw_cells_app usegs m4 _ _ _)) in NEW. destruct NEW as [ND8 ND16].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ND8, ND16. replace (An + 8 + 8) with (An + 16) in ND16 by lia.
      split; [| exact ND8]. eapply plseg_app.
      + eapply plseg_agree; [eapply plseg_agree; [exact SEGI| | intros n _ X; exact X]| | intros n _ X; exact (OWNS n X)].
        * eapply agree_on_mono; [exact AG23|]. intros a Ha. destruct (plseg_fp_where _ _ _ Ha) as [Y|(n & Hn & Y)]; [right; left; lia|].
          right; right. exists n. split; [exact (in_concat_nthZ _ _ _ Hn)| exact Y].
        * eapply agree_on_mono; [exact AG34|]. intros a Ha.
          destruct RNW as [[E1 ->]|(pre & pr & Ar & hr & E1 & ERN')].
          -- rewrite E1 in Ha. destruct Ha.
          -- assert (NRN : ~ (rn <= a < rn + 8)).
             { eapply (plseg_fp_not_end _ _ _ _ _ _ SEGI); [| | | rewrite E1; destruct pre; discriminate| exact Ha].
               - intros n1 n2 H1 H2 NE. apply APNN; [exact (in_concat_nthZ _ _ _ H1)| exact (in_concat_nthZ _ _ _ H2)| exact NE].
               - apply plh_bucket_nodup. exact ND2.
               - intros n Hn. destruct (APN n (in_concat_nthZ _ _ _ Hn)) as [_ X]. lia. }
             destruct (plseg_fp_where _ _ _ Ha) as [Y|(n & Hn & Y)]; [cbn [outside]; lia|].
             exact (NODE_OUT n (in_concat_nthZ _ _ _ Hn) a Y NRN).
      + cbn [plseg]. split; [exact TERM3|]. split; [apply cown_new|]. split; [lia|]. split; [exists d; exact ND0|]. split; [exact ND16|]. split; [exact HR| reflexivity].
    - rewrite nth_lupd_ne by (clear - NJ Hj IDXR; lia).
      eapply pchain_agree; [exact (CH j Hj)| | intros n _ X; exact (OWNS n X)].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AG23|]| eapply agree_on_mono; [exact AG34|]].
      + intros a [Ha|(n & Hn & Ha)]; [right; left; lia| right; right; exists n; split; [exact (in_concat_nthZ _ _ _ Hn)| exact Ha]].
      + intros a [Ha|(n & Hn & Ha)]; [exact (CELL_OUT j Hj NJ a Ha)|].
        apply (NODE_OUT n (in_concat_nthZ _ _ _ Hn) a Ha).
        destruct RNW as [[_ ->]|(pre & pr & Ar & hr & E1 & ->)].
        * destruct (APN n (in_concat_nthZ _ _ _ Hn)) as [_ X]. lia.
        * (* [comment removed for export] *)
          destruct (In_nth_error _ _ Hn) as [k Hk].
          assert (Hl : nth_error (nth (Z.to_nat idx) bks []) (length pre) = Some ((pr, Ar), hr)) by (rewrite E1, nth_error_app2, Nat.sub_diag by lia; reflexivity).
          assert (NEid : fst (fst n) <> pr).
          { pose proof (plh_ids_distinct bks (Z.to_nat j) k (Z.to_nat idx) (length pre) n ((pr, Ar), hr) ND2 Hk Hl) as X. cbn [fst] in X. apply X.
            intros EQ. injection EQ as E3 E4. apply NJ. clear - E3 Hj IDXR. apply (f_equal Z.of_nat) in E3. rewrite !Z2Nat.id in E3 by lia. exact E3. }
          assert (INR : In ((pr, Ar), hr) (concat bks)) by (eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity).
          pose proof (APNN n ((pr, Ar), hr) (in_concat_nthZ _ _ _ Hn) INR NEid) as X. cbn [fst snd] in X. lia. }
  split. { intros j Hj. rewrite nth_lupd_ne by (clear - Hj IDXR; lia). apply EMP. exact Hj. }
  (* [comment removed for export] *)
  assert (PM : Permutation (concat (lupd (Z.to_nat idx) (nth (Z.to_nat idx) bks [] ++ [((pn, An), h)]) bks)) (((pn, An), h) :: concat bks)).
  { eapply Permutation_trans; [apply concat_lupd; exact LI|].
    eapply Permutation_trans; [| apply perm_skip; apply Permutation_sym; apply (concat_split_perm bks (Z.to_nat idx) LI)].
    rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_cons_app. apply Permutation_refl. }
  eapply Permutation.Permutation_NoDup.
  { apply Permutation_sym. apply perm_skip. apply perm_skip. apply Permutation_map. apply Permutation_map. exact PM. }
  cbn [map fst]. eapply Permutation.Permutation_NoDup; [| constructor; [| exact ND]].
  + eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
  + intros [E|[E|E]].
    * exact (PNEW _ _ _ INL (eq_sym E)).
    * exact (PNEW _ _ _ INB (eq_sym E)).
    * apply in_map_iff in E. destruct E as ([p0 X] & E1 & Hin). cbn [fst] in E1. subst p0.
      apply in_map_iff in Hin. destruct Hin as (n & E2 & Hin).
      pose proof (INN n Hin) as Y. rewrite E2 in Y. cbn [fst snd] in Y. exact (PNEW _ _ _ Y eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma plh_rep_of_empty : forall m LBall L lh pl pb B,
  lh_rep (fun _ => True) m LBall L PROP_FNS lh pl pb B 128 (mkGeo 8 16 0 8 0) (repeat [] 16) -> plh_rep m LBall L lh pl pb B 0 (repeat [] 16).
Proof.
  intros m LBall L lh pl pb B (G & OL & RL & SC & OB & RB & LEN & CH & EMP & ND). cbn [g_nn g_na g_p g_pmax g_items] in *.
  split; [exact OL|]. split; [exact RL|]. split; [exact SC|]. split; [exact OB|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
  split. { intros i Hi. pose proof (CH i Hi) as (c' & S & Z0). exists c'.
           replace (nth (Z.to_nat i) (repeat (@nil pnode) 16) []) with (@nil pnode) by (symmetry; apply nth_repeat).
           replace (nth (Z.to_nat i) (repeat (@nil (bptr * Z)) 16) []) with (@nil (bptr * Z)) in S by (symmetry; apply nth_repeat).
           cbn [lseg] in S. cbn [plseg]. split; [exact S| exact Z0]. }
  split. { intros i Hi. apply nth_repeat. }
  cbn [concat map app]. rewrite concat_repeat_nil. cbn [map app]. cbn [concat map] in ND.
  replace (concat (repeat (@nil (bptr * Z)) 16)) with (@nil (bptr * Z)) in ND by reflexivity. cbn [map app] in ND. exact ND.
Qed.

End WithCeiling0.
