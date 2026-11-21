(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffHeap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import HuffFib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import HuffBuild.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.


Lemma in_map_ziota : forall (g : Z -> Z) a n x,
  In x (map g (ziota a n)) <-> exists p, a <= p < a + Z.of_nat n /\ g p = x.
Proof.
  intros. rewrite in_map_iff. split.
  - intros (p & <- & Hp). apply in_ziota in Hp. exists p. auto.
  - intros (p & Hp & <-). exists p. split; [reflexivity| apply in_ziota; lia].
Qed.

Lemma NoDup_map_ziota : forall (g : Z -> Z) a n,
  (forall p q, a <= p < a + Z.of_nat n -> a <= q < a + Z.of_nat n -> g p = g q -> p = q) ->
  NoDup (map g (ziota a n)).
Proof.
  intros g a n. revert a. induction n as [|n IH]; intros a Hinj; cbn; constructor.
  - rewrite in_map_ziota. intros (p & Hp & E). rewrite Nat2Z.inj_succ in Hinj.
    assert (p = a) by (apply Hinj; lia). lia.
  - apply IH. intros p q Hp Hq. apply Hinj; lia.
Qed.


Lemma ziota_split1 : forall a n, ziota a (S n) = a :: ziota (a + 1) n.
Proof. reflexivity. Qed.


Section Loop4.
Variables (s : deflate_state) (t : tree_id) (FC0 : arr) (BC : arr) (OL SL MC : Z).
Hypothesis LFC : arr_len FC0 = tsize t.
Hypothesis Fnn : forall j, 0 <= j < sd_elems t -> 0 <= arr_get FC0 j.

Local Set Warnings "-notation-for-abbreviation".
Local Notation elems := (sd_elems t).
Local Notation UPl := (UP FC0 t).
Local Notation FPf := (FP FC0 t).
Local Notation W6 FC DL HP HL HM0 DP := (bt_upd s t FC DL HP HL HM0 DP BC OL SL MC).

Definition Ftot : Z := zsum (map FPf UPl).
Definition u : Z := zlen UPl.
Definition F0 : list htree := map (fun j => HuffTree.HL (FPf j) j) UPl.

Hypothesis Ftot_bound : Ftot < 2 ^ 16.

Lemma FP_pos : forall j, In j UPl -> 1 <= FPf j.
Proof.
  intros j Hj. pose proof (pads_facts t FC0) as (ND & RNG & U2 & PD & MX1 & MX2).
  unfold FP. destruct (existsb (Z.eqb j) (pads FC0 t)) eqn:E; [lia|].
  unfold UP in Hj. apply in_app_iff in Hj. destruct Hj as [Hj|Hj].
  - unfold Ulist in Hj. pose proof (elems_tsize t). apply Ul_in in Hj; [|lia]. specialize (Fnn j ltac:(lia)). lia.
  - exfalso. assert (existsb (Z.eqb j) (pads FC0 t) = true); [|congruence].
    apply existsb_exists. exists j. split; [exact Hj| apply Z.eqb_refl].
Qed.

Definition PP (hl hm p : Z) : Prop := (1 <= p <= hl) \/ (hm <= p <= 572).

Definition SubOK (FC DL HP : arr) (hm x : Z) (T : htree) : Prop :=
  hw T = arr_get FC x /\ hwmin 1 T
  /\ (x < elems -> T = HuffTree.HL (FPf x) x)
  /\ (elems <= x -> exists l r, T = HN l r)
  /\ forall e, In e (hprof 0 T) ->
       In (ea e) UPl /\ 0 <= ed e /\ up DL (Z.to_nat (ed e)) (ea e) = x
       /\ forall i, (i < Z.to_nat (ed e))%nat ->
            up DL i (ea e) < up DL (S i) (ea e) /\ exists h, hm <= h <= 572 /\ arr_get HP h = up DL i (ea e).

Record Inv4 (k : Z) (FC DL HP : arr) (hl hm : Z) (DP : arr) (sub : Z -> htree) : Prop := INV4 {
  i_len : arr_len FC = tsize t /\ arr_len DL = tsize t /\ arr_len HP = 573 /\ arr_len DP = 573;
  i_k : 0 <= k <= u - 1 /\ hl = u - k /\ hm = 573 - 2 * k;
  i_heap : heap_ok FC DP HP 1 0 hl;
  i_inj : forall p q, PP hl hm p -> PP hl hm q -> arr_get HP p = arr_get HP q -> p = q;
  i_rng : forall p, PP hl hm p -> (In (arr_get HP p) UPl /\ 0 <= arr_get HP p < elems) \/ (elems <= arr_get HP p < elems + k);
  i_leaf : forall j, In j UPl -> exists p, PP hl hm p /\ arr_get HP p = j;
  i_int : forall i, 1 <= i <= k -> exists p, (1 <= p <= hl \/ hm <= p <= 572 - 2 * i) /\ arr_get HP p = elems + i - 1;
  i_dad : forall h, hm <= h <= 572 -> arr_get DL (arr_get HP h) = elems + (572 - h) / 2;
  i_fc : forall j, 0 <= j < elems -> arr_get FC j = FPf j;
  i_wsum : zsum (map (fun p => arr_get FC (arr_get HP p)) (ziota 1 (Z.to_nat hl))) = Ftot;
  i_word : forall h, hm <= h < 572 -> arr_get FC (arr_get HP (h + 1)) <= arr_get FC (arr_get HP h);
  i_wheap : forall p h, 1 <= p <= hl -> hm <= h <= 572 -> arr_get FC (arr_get HP h) <= arr_get FC (arr_get HP p);
  i_sub : forall p, PP hl hm p -> SubOK FC DL HP hm (arr_get HP p) (sub (arr_get HP p));
  i_hb : forall T, hbuild (map sub (map (arr_get HP) (ziota 1 (Z.to_nat hl)))) T -> hbuild F0 T;
  i_dl0 : forall j, 0 <= j < elems -> ~ In j UPl -> arr_get DL j = 0 }.


Lemma UP_len_elems : u <= elems.
Proof.
  pose proof (pads_facts t FC0) as (ND & RNG & _).
  unfold u, zlen.
  assert (incl UPl (ziota 0 (Z.to_nat elems))).
  { intros j Hj. apply in_ziota. specialize (RNG j Hj). lia. }
  pose proof (NoDup_incl_length ND H) as L. rewrite ziota_length in L. pose proof (elems_tsize t). lia.
Qed.

Lemma lex_ext : forall FC DP FC' DP' x y,
  arr_get FC' x = arr_get FC x -> arr_get FC' y = arr_get FC y ->
  arr_get DP' x = arr_get DP x -> arr_get DP' y = arr_get DP y ->
  lex FC DP x y -> lex FC' DP' x y.
Proof. intros. unfold lex in *. lia. Qed.


Theorem trip_inv : forall k FC DL HP hl hm DP sub,
  Inv4 k FC DL HP hl hm DP sub -> 2 <= hl ->
  exists FC' DL' HP' DP' sub',
    trip s t BC OL SL MC FC DL HP hl hm DP (elems + k) = W6 FC' DL' HP' (hl - 1) (hm - 2) DP'
    /\ Inv4 (k + 1) FC' DL' HP' (hl - 1) (hm - 2) DP' sub'.
Proof.
  intros k FC DL HP hl hm DP sub INV Hhl.
  destruct INV as [(LFC1 & LDL & LHP & LDP) (Hk & Hhl' & Hhm) OK INJ RNG LEAF INT DAD IFC WSUM WORD WHEAP SUB HB DL0].
  pose proof UP_len_elems as UE. pose proof (elems_tsize t) as ET. fold u in UE.
  pose proof (pads_facts t FC0) as (NDU & RNGU & U2 & PD & MX1 & MX2). fold u in U2.
  assert (Hgap : hl + 2 <= hm - 1 /\ hm <= 573) by lia.
  set (node := elems + k).
  assert (IDS : forall p, PP hl hm p -> 0 <= arr_get HP p < node).
  { intros p Hp. destruct (RNG p Hp); lia. }
  set (n := arr_get HP 1).
  set (HP1 := arr_set HP 1 (arr_get HP hl)).
  assert (LHP1 : arr_len HP1 = 573) by (subst HP1; rewrite arr_len_set; exact LHP).
  assert (HP1v : forall p, arr_get HP1 p = if p =? 1 then arr_get HP hl else arr_get HP p).
  { intros p. subst HP1. rewrite arr_get_set, (Z.eqb_sym 1 p). destruct (Z.eqb_spec p 1); cbn [andb]; [|reflexivity].
    rewrite inb_true by lia. reflexivity. }
  destruct (pqdownheap_flat s t FC DL (hl - 1) hm DP BC OL SL MC HP1 1 LHP1 ltac:(lia) ltac:(lia)) as (HPa & EA & LHPa & RRa & OKa).
  { intros c Hc H1 H2. rewrite !HP1v. destruct (Z.eqb_spec (c / 2) 1); [lia|]. destruct (Z.eqb_spec c 1); [lia|]. apply OK; lia. }
  set (m := arr_get HPa 1).
  destruct RRa as (_ & HPa_out & fa & ga & Ba).
  set (phi := fun p => if fa p =? 1 then hl else fa p).
  assert (PHI : forall p, 1 <= p <= hl - 1 -> 2 <= phi p <= hl /\ arr_get HPa p = arr_get HP (phi p)).
  { intros p Hp. destruct (Ba p Hp) as (R1 & R2 & R3 & R4 & R5). subst phi. cbn beta.
    rewrite R5, HP1v. destruct (Z.eqb_spec (fa p) 1); lia || (split; [lia|reflexivity]). }
  assert (PHIinj : forall p q, 1 <= p <= hl - 1 -> 1 <= q <= hl - 1 -> phi p = phi q -> p = q).
  { intros p q Hp Hq E. destruct (Ba p Hp) as (R1 & R2 & R3 & R4 & R5). destruct (Ba q Hq) as (Q1 & Q2 & Q3 & Q4 & Q5).
    subst phi. cbn beta in E.
    destruct (Z.eqb_spec (fa p) 1), (Z.eqb_spec (fa q) 1); first [lia | congruence]. }
  assert (PHIsur : forall q, 2 <= q <= hl -> exists p, 1 <= p <= hl - 1 /\ phi p = q).
  { intros q Hq. destruct (Z.eq_dec q hl).
    - exists (ga 1). destruct (Ba 1 ltac:(lia)) as (R1 & R2 & R3 & R4 & R5). split; [lia|]. subst phi. cbn beta. rewrite R4. rewrite Z.eqb_refl. lia.
    - exists (ga q). destruct (Ba q ltac:(lia)) as (R1 & R2 & R3 & R4 & R5). split; [lia|]. subst phi. cbn beta. rewrite R4.
      destruct (Z.eqb_spec q 1); lia. }
  clearbody phi. clear fa ga Ba.
  assert (HPa_hi : forall p, hl <= p -> arr_get HPa p = arr_get HP p).
  { intros p Hp. rewrite HPa_out by lia. rewrite HP1v. destruct (Z.eqb_spec p 1); [lia| reflexivity]. }
  assert (Hm : 2 <= phi 1 <= hl /\ m = arr_get HP (phi 1)) by (subst m; apply PHI; lia).
  assert (Hnm : n <> m).
  { intros E. subst n. destruct Hm as [Hm1 Hm2]. rewrite Hm2 in E. apply INJ in E; unfold PP; lia. }
  assert (MINn : forall p, 1 <= p <= hl -> arr_get FC n <= arr_get FC (arr_get HP p)).
  { intros p Hp. subst n. apply (lex_freq FC DP). apply (heap_root_min FC DP HP hl OK). lia. }
  assert (MINm : forall p, 1 <= p <= hl - 1 -> arr_get FC m <= arr_get FC (arr_get HPa p)).
  { intros p Hp. subst m. apply (lex_freq FC DP). apply (heap_root_min FC DP HPa (hl - 1) OKa). lia. }
  set (L0 := map (arr_get HP) (ziota 1 (Z.to_nat hl))) in *.
  set (La := map (arr_get HPa) (ziota 2 (Z.to_nat (hl - 2)))).
  assert (P0 : Permutation L0 (n :: m :: La)).
  { apply NoDup_Permutation.
    - subst L0. apply NoDup_map_ziota. intros p q Hp Hq E. apply INJ in E; unfold PP; lia.
    - constructor.
      + intros [E|Hin]; [exact (Hnm (eq_sym E))|]. subst La. apply in_map_ziota in Hin. destruct Hin as (p & Hp & E).
        destruct (PHI p ltac:(lia)) as [P1 P2]. rewrite P2 in E. subst n. apply INJ in E; unfold PP; lia.
      + constructor.
        * intros Hin. subst La. apply in_map_ziota in Hin. destruct Hin as (p & Hp & E).
          destruct (PHI p ltac:(lia)) as [P1 P2]. destruct Hm as [M1 M2]. rewrite P2, M2 in E.
          apply INJ in E; [|unfold PP; lia|unfold PP; lia]. apply PHIinj in E; lia.
        * subst La. apply NoDup_map_ziota. intros p q Hp Hq E.
          destruct (PHI p ltac:(lia)) as [P1 P2]. destruct (PHI q ltac:(lia)) as [Q1 Q2]. rewrite P2, Q2 in E.
          apply INJ in E; [|unfold PP; lia|unfold PP; lia]. apply PHIinj in E; lia.
    - intros x. subst L0 La. rewrite in_map_ziota. cbn [In]. rewrite in_map_ziota. split.
      + intros (q & Hq & <-). destruct (Z.eq_dec q 1) as [->|]; [left; reflexivity|].
        destruct (PHIsur q ltac:(lia)) as (p & Hp & Hpq).
        destruct (Z.eq_dec p 1) as [->|].
        * right; left. destruct Hm as [M1 M2]. rewrite M2, Hpq. reflexivity.
        * right; right. exists p. split; [lia|]. destruct (PHI p ltac:(lia)) as [P1 P2]. rewrite P2, Hpq. reflexivity.
      + intros [<-|[<-|(p & Hp & <-)]].
        * exists 1. split; [lia| reflexivity].
        * exists (phi 1). destruct Hm as [M1 M2]. split; [lia| symmetry; exact M2].
        * exists (phi p). destruct (PHI p ltac:(lia)) as [P1 P2]. split; [lia| symmetry; exact P2]. }
  assert (Wn : 1 <= arr_get FC n) by (subst n; destruct (SUB 1 ltac:(unfold PP; lia)) as (W & M & _); rewrite <- W; apply hwmin_hw; [lia|exact M]).
  assert (Wm : 1 <= arr_get FC m) by (destruct Hm as [Hm1 ->]; destruct (SUB (phi 1) ltac:(unfold PP; lia)) as (W & M & _); rewrite <- W; apply hwmin_hw; [lia|exact M]).
  assert (WLa : 0 <= zsum (map (arr_get FC) La)).
  { apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & Hy). subst La.
    apply in_map_ziota in Hy. destruct Hy as (p & Hp & <-). destruct (PHI p ltac:(lia)) as [P1 ->].
    destruct (SUB (phi p) ltac:(unfold PP; lia)) as (W & M & _). rewrite <- W. pose proof (hwmin_hw 1 _ ltac:(lia) M). lia. }
  assert (Wsum : arr_get FC n + arr_get FC m + zsum (map (arr_get FC) La) = Ftot).
  { rewrite <- WSUM. change (zsum (map (arr_get FC) L0) = _ -> _) || idtac.
    replace (zsum (map (fun p : Z => arr_get FC (arr_get HP p)) (ziota 1 (Z.to_nat hl)))) with (zsum (map (arr_get FC) L0))
      by (subst L0; rewrite map_map; reflexivity).
    rewrite (zsum_map_perm _ _ _ P0). cbn [map zsum]. lia. }
  set (FC' := arr_set FC node (wrap16 (arr_get FC n + arr_get FC m))).
  set (DL' := arr_set (arr_set DL m (wrap16 node)) n (wrap16 node)).
  set (HPd := arr_set (arr_set (arr_set HPa (hm - 1) n) (hm - 2) m) 1 node).
  set (DP' := arr_set DP node (wrap8 (dmax DP n m + 1))).
  assert (Hnode : elems <= node < tsize t /\ node < 65536) by (subst node; lia).
  assert (Hn_r : 0 <= n < node) by (subst n; apply (IDS 1); unfold PP; lia).
  assert (Hm_r : 0 <= m < node) by (destruct Hm as [M1 ->]; apply IDS; unfold PP; lia).
  assert (FC'v : forall x, arr_get FC' x = if x =? node then arr_get FC n + arr_get FC m else arr_get FC x).
  { intros x. subst FC'. rewrite arr_get_set, (Z.eqb_sym node x). destruct (Z.eqb_spec x node); cbn [andb]; [|reflexivity].
    rewrite inb_true by lia. apply wrap16_id. pose proof Ftot_bound. lia. }
  assert (DP'v : forall x, x <> node -> arr_get DP' x = arr_get DP x).
  { intros x Hx. subst DP'. rewrite arr_get_set_other by lia. reflexivity. }
  assert (DL'v : forall x, arr_get DL' x = if (x =? n) || (x =? m) then node else arr_get DL x).
  { intros x. subst DL'. rewrite !arr_get_set, (Z.eqb_sym n x), (Z.eqb_sym m x). unfold arr_inb. rewrite arr_len_set, LDL.
    rewrite !wrap16_id by lia.
    destruct (Z.eqb_spec x n); [subst x; cbn [andb orb]; rewrite (proj2 (Z.leb_le 0 n)), (proj2 (Z.ltb_lt n (tsize t))) by lia; reflexivity|].
    destruct (Z.eqb_spec x m); [subst x; cbn [andb orb]; rewrite (proj2 (Z.leb_le 0 m)), (proj2 (Z.ltb_lt m (tsize t))) by lia; reflexivity|].
    reflexivity. }
  assert (LHPd : arr_len HPd = 573) by (subst HPd; rewrite !arr_len_set; exact LHPa).
  assert (HPdv : forall p, arr_get HPd p = if p =? 1 then node else if p =? hm - 2 then m else if p =? hm - 1 then n else arr_get HPa p).
  { intros p. subst HPd. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, LHPa.
    rewrite (Z.eqb_sym 1 p), (Z.eqb_sym (hm - 2) p), (Z.eqb_sym (hm - 1) p).
    destruct (Z.eqb_spec p 1); [subst p; reflexivity|].
    destruct (Z.eqb_spec p (hm - 2)); [subst p; cbn [andb]; rewrite (proj2 (Z.leb_le 0 _)), (proj2 (Z.ltb_lt _ 573)) by lia; reflexivity|].
    destruct (Z.eqb_spec p (hm - 1)); [subst p; cbn [andb]; rewrite (proj2 (Z.leb_le 0 _)), (proj2 (Z.ltb_lt _ 573)) by lia; reflexivity|].
    reflexivity. }
  destruct (pqdownheap_flat s t FC' DL' (hl - 1) (hm - 2) DP' BC OL SL MC HPd 1 LHPd ltac:(lia) ltac:(lia)) as (HPe & EB & LHPe & RRe & OKe).
  { intros c Hc H1 H2. rewrite !HPdv.
    destruct (Z.eqb_spec (c / 2) 1); [lia|]. destruct (Z.eqb_spec (c / 2) (hm - 2)); [lia|]. destruct (Z.eqb_spec (c / 2) (hm - 1)); [lia|].
    destruct (Z.eqb_spec c 1); [lia|]. destruct (Z.eqb_spec c (hm - 2)); [lia|]. destruct (Z.eqb_spec c (hm - 1)); [lia|].
    destruct (PHI (c / 2) ltac:(lia)) as [A1 A2]. destruct (PHI c ltac:(lia)) as [C1 C2].
    pose proof (IDS (phi (c / 2)) ltac:(unfold PP; lia)) as X1. pose proof (IDS (phi c) ltac:(unfold PP; lia)) as X2.
    rewrite <- A2 in X1. rewrite <- C2 in X2.
    apply (lex_ext FC DP).
    - rewrite FC'v. destruct (Z.eqb_spec (arr_get HPa (c / 2)) node); [lia| reflexivity].
    - rewrite FC'v. destruct (Z.eqb_spec (arr_get HPa c) node); [lia| reflexivity].
    - apply DP'v. lia.
    - apply DP'v. lia.
    - apply OKa; lia. }
  exists FC', DL', HPe, DP', (fun x => if x =? node then HN (sub n) (sub m) else sub x).
  split.
  { subst FC' DL' HPd DP' m HP1 n node. unfold trip. rewrite EA. rewrite !bt_heap. exact EB. }
  destruct RRe as (_ & HPe_out & fe & ge & Be).
  set (old := fun p => if p <=? hl - 1 then (if fe p =? 1 then 0 else phi (fe p))
                       else if p =? hm - 1 then 1 else if p =? hm - 2 then phi 1 else p).
  assert (VALS : forall p, PP (hl - 1) (hm - 2) p ->
            (old p = 0 /\ 1 <= p <= hl - 1 /\ arr_get HPe p = node)
            \/ (PP hl hm (old p) /\ old p <> 0 /\ arr_get HPe p = arr_get HP (old p))).
  { intros p Hp. subst old. cbn beta. unfold PP in Hp |- *. destruct (Z.leb_spec p (hl - 1)).
    - destruct (Be p ltac:(lia)) as (R1 & R2 & R3 & R4 & R5). rewrite R5, HPdv.
      destruct (Z.eqb_spec (fe p) 1); [left; repeat split; lia|].
      right. destruct (Z.eqb_spec (fe p) (hm - 2)); [lia|]. destruct (Z.eqb_spec (fe p) (hm - 1)); [lia|].
      destruct (PHI (fe p) ltac:(lia)) as [A1 A2]. rewrite A2. repeat split; lia.
    - right. rewrite HPe_out by lia. rewrite HPdv. destruct (Z.eqb_spec p 1); [lia|].
      destruct (Z.eqb_spec p (hm - 1)).
      + destruct (Z.eqb_spec p (hm - 2)); [lia|]. subst n. repeat split; lia.
      + destruct (Z.eqb_spec p (hm - 2)).
        * destruct Hm as [M1 M2]. rewrite <- M2. repeat split; lia.
        * rewrite HPa_hi by lia. repeat split; lia. }
  assert (OLDinj : forall p q, PP (hl - 1) (hm - 2) p -> PP (hl - 1) (hm - 2) q -> old p = old q -> p = q).
  { intros p q Hp Hq E. subst old. cbn beta in E. unfold PP in Hp, Hq.
    destruct (Z.leb_spec p (hl - 1)); destruct (Z.leb_spec q (hl - 1)).
    - destruct (Be p ltac:(lia)) as (R1 & R2 & R3 & R4 & R5). destruct (Be q ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5).
      destruct (Z.eqb_spec (fe p) 1), (Z.eqb_spec (fe q) 1).
      + rewrite <- R3, <- Q3. congruence.
      + destruct (PHI (fe q) ltac:(lia)). lia.
      + destruct (PHI (fe p) ltac:(lia)). lia.
      + apply PHIinj in E; [|lia|lia]. rewrite <- R3, <- Q3. congruence.
    - exfalso. destruct (Be p ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
      destruct (Z.eqb_spec (fe p) 1); [destruct (Z.eqb_spec q (hm - 1)); [lia|]; destruct (Z.eqb_spec q (hm - 2)); [destruct (PHI 1 ltac:(lia)); lia|lia]|].
      destruct (PHI (fe p) ltac:(lia)).
      destruct (Z.eqb_spec q (hm - 1)); [lia|]. destruct (Z.eqb_spec q (hm - 2)); [|lia].
      apply PHIinj in E; lia.
    - exfalso. destruct (Be q ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
      destruct (Z.eqb_spec (fe q) 1); [destruct (Z.eqb_spec p (hm - 1)); [lia|]; destruct (Z.eqb_spec p (hm - 2)); [destruct (PHI 1 ltac:(lia)); lia|lia]|].
      destruct (PHI (fe q) ltac:(lia)).
      destruct (Z.eqb_spec p (hm - 1)); [lia|]. destruct (Z.eqb_spec p (hm - 2)); [|lia].
      apply PHIinj in E; lia.
    - destruct (PHI 1 ltac:(lia)).
      destruct (Z.eqb_spec p (hm - 1)), (Z.eqb_spec q (hm - 1)); try lia;
      destruct (Z.eqb_spec p (hm - 2)), (Z.eqb_spec q (hm - 2)); lia. }
  assert (OLDsur : forall q, PP hl hm q -> exists p, PP (hl - 1) (hm - 2) p /\ old p = q).
  { intros q Hq. subst old. unfold PP in Hq |- *. cbn beta.
    destruct (Z.eq_dec q 1) as [->|].
    { exists (hm - 1). rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite Z.eqb_refl. split; lia. }
    destruct (Z_le_gt_dec hm q).
    { exists q. rewrite (proj2 (Z.leb_gt _ _)) by lia.
      destruct (Z.eqb_spec q (hm - 1)); [lia|]. destruct (Z.eqb_spec q (hm - 2)); [lia|]. split; lia. }
    destruct (PHIsur q ltac:(lia)) as (p & Hp & Hpq).
    destruct (Z.eq_dec p 1) as [->|].
    { exists (hm - 2). rewrite (proj2 (Z.leb_gt _ _)) by lia.
      destruct (Z.eqb_spec (hm - 2) (hm - 1)); [lia|]. rewrite Z.eqb_refl. split; [lia| exact Hpq]. }
    exists (ge p). destruct (Be p ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite R4. destruct (Z.eqb_spec p 1); [lia|]. split; [lia| exact Hpq]. }
  assert (NEWpos : exists p0, 1 <= p0 <= hl - 1 /\ old p0 = 0 /\ arr_get HPe p0 = node).
  { exists (ge 1). destruct (Be 1 ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
    destruct (Be (ge 1) ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    subst old. cbn beta. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite R4, Z.eqb_refl.
    split; [lia|]. split; [reflexivity|]. rewrite Q5, R4, HPdv, Z.eqb_refl. reflexivity. }
  clearbody old.
  set (Le := map (arr_get HPe) (ziota 1 (Z.to_nat (hl - 1)))).
  assert (Pe : Permutation Le (node :: La)).
  { apply NoDup_Permutation.
    - subst Le. apply NoDup_map_ziota. intros p q Hp Hq E.
      destruct (VALS p ltac:(unfold PP; lia)) as [(O1 & _ & V1)|(O1 & O1' & V1)];
      destruct (VALS q ltac:(unfold PP; lia)) as [(O2 & _ & V2)|(O2 & O2' & V2)].
      + apply OLDinj; unfold PP; lia || congruence.
      + exfalso. rewrite V1, V2 in E. pose proof (IDS (old q) O2). lia.
      + exfalso. rewrite V1, V2 in E. pose proof (IDS (old p) O1). lia.
      + rewrite V1, V2 in E. apply INJ in E; [|exact O1|exact O2]. apply OLDinj; unfold PP; lia || congruence.
    - constructor.
      + intros Hin. subst La. apply in_map_ziota in Hin. destruct Hin as (p & Hp & E).
        destruct (PHI p ltac:(lia)) as [P1 P2]. pose proof (IDS (phi p) ltac:(unfold PP; lia)). rewrite P2 in E. lia.
      + pose proof (Permutation_NoDup P0) as ND0. 
        assert (NL0 : NoDup L0) by (subst L0; apply NoDup_map_ziota; intros p q Hp Hq E; apply INJ in E; unfold PP; lia).
        specialize (ND0 NL0). inversion ND0; subst. inversion H2; subst. assumption.
    - intros x. subst Le La. rewrite in_map_ziota. cbn [In]. rewrite in_map_ziota. split.
      + intros (p & Hp & <-). destruct (Be p ltac:(lia)) as (R1 & R2 & R3 & R4 & R5). rewrite R5, HPdv.
        destruct (Z.eqb_spec (fe p) 1); [left; reflexivity|]. right.
        destruct (Z.eqb_spec (fe p) (hm - 2)); [lia|]. destruct (Z.eqb_spec (fe p) (hm - 1)); [lia|].
        exists (fe p). split; [lia| reflexivity].
      + intros [E|(q & Hq & E)].
        * destruct NEWpos as (p0 & H0 & _ & V0). exists p0. split; [lia| congruence].
        * exists (ge q). destruct (Be q ltac:(lia)) as (R1 & R2 & R3 & R4 & R5). split; [lia|].
          destruct (Be (ge q) ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5). rewrite Q5, R4, HPdv.
          destruct (Z.eqb_spec q 1); [lia|]. destruct (Z.eqb_spec q (hm - 2)); [lia|]. destruct (Z.eqb_spec q (hm - 1)); [lia|]. exact E. }
  assert (EXTR : forall h, hm <= h <= 572 -> arr_get HP h <> n /\ arr_get HP h <> m).
  { intros h Hh. destruct Hm as [M1 M2]. subst n. rewrite M2. split; intros E; apply INJ in E; unfold PP; lia. }
  assert (UPX : forall x T, (exists p, PP hl hm p /\ arr_get HP p = x) -> SubOK FC DL HP hm x T ->
            forall e, In e (hprof 0 T) -> forall i, (i <= Z.to_nat (ed e))%nat -> up DL' i (ea e) = up DL i (ea e)).
  { intros x T _ (W & M & FL & FN & CH) e He i Hi. apply up_ext. intros s0 Hs0.
    destruct (CH e He) as (A1 & A2 & A3 & A4). destruct (A4 s0 ltac:(lia)) as (_ & h & Hh & Eh).
    rewrite DL'v. rewrite <- Eh. destruct (EXTR h Hh) as [E1 E2].
    destruct (Z.eqb_spec (arr_get HP h) n); [congruence|]. destruct (Z.eqb_spec (arr_get HP h) m); [congruence|]. reflexivity. }
  assert (HPe_hi : forall h, hm <= h <= 572 -> arr_get HPe h = arr_get HP h).
  { intros h Hh. rewrite HPe_out by lia. rewrite HPdv. destruct (Z.eqb_spec h 1); [lia|].
    destruct (Z.eqb_spec h (hm - 2)); [lia|]. destruct (Z.eqb_spec h (hm - 1)); [lia|]. apply HPa_hi. lia. }
  assert (HPe_n : arr_get HPe (hm - 1) = n).
  { rewrite HPe_out by lia. rewrite HPdv. destruct (Z.eqb_spec (hm - 1) 1); [lia|].
    destruct (Z.eqb_spec (hm - 1) (hm - 2)); [lia|]. rewrite Z.eqb_refl. reflexivity. }
  assert (HPe_m : arr_get HPe (hm - 2) = m).
  { rewrite HPe_out by lia. rewrite HPdv. destruct (Z.eqb_spec (hm - 2) 1); [lia|]. rewrite Z.eqb_refl. reflexivity. }
  assert (SUBX : forall p, PP hl hm p -> SubOK FC' DL' HPe (hm - 2) (arr_get HP p) (sub (arr_get HP p))).
  { intros p Hp. pose proof (SUB p Hp) as SK. pose proof (IDS p Hp) as Ip. destruct SK as (W & M & FL & FN & CH).
    split; [rewrite FC'v; destruct (Z.eqb_spec (arr_get HP p) node); [lia| exact W]|].
    split; [exact M|]. split; [exact FL|]. split; [exact FN|].
    intros e He. destruct (CH e He) as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [exact A2|].
    assert (UQ : forall i, (i <= Z.to_nat (ed e))%nat -> up DL' i (ea e) = up DL i (ea e)).
    { intros i Hi. eapply (UPX (arr_get HP p) (sub (arr_get HP p))); eauto. }
    split; [rewrite UQ by lia; exact A3|].
    intros i Hi. rewrite !UQ by lia. destruct (A4 i Hi) as (B1 & h & Hh & Eh). split; [exact B1|].
    exists h. split; [lia|]. rewrite HPe_hi by lia. exact Eh. }
  split.
  - subst FC' DL' DP'. rewrite !arr_len_set. repeat split; assumption.
  - lia.
  - exact OKe.
  -
    intros p q Hp Hq E.
    destruct (VALS p Hp) as [(O1 & R1 & V1)|(O1 & O1' & V1)]; destruct (VALS q Hq) as [(O2 & R2 & V2)|(O2 & O2' & V2)].
    + apply OLDinj; [exact Hp| exact Hq| lia].
    + exfalso. pose proof (IDS (old q) O2). rewrite V1, V2 in E. lia.
    + exfalso. pose proof (IDS (old p) O1). rewrite V1, V2 in E. lia.
    + apply OLDinj; [exact Hp| exact Hq|]. apply INJ; [exact O1| exact O2|]. rewrite <- V1, <- V2. exact E.
  -
    intros p Hp. destruct (VALS p Hp) as [(O1 & R1 & V1)|(O1 & O1' & V1)]; rewrite V1.
    + right. subst node. lia.
    + destruct (RNG (old p) O1); [left; assumption| right; lia].
  -
    intros j Hj. destruct (LEAF j Hj) as (q & Hq & E). destruct (OLDsur q Hq) as (p & Hp & Hpq).
    exists p. split; [exact Hp|]. destruct (VALS p Hp) as [(O1 & R1 & V1)|(O1 & O1' & V1)]; [unfold PP in Hq; lia|]. rewrite V1, Hpq. exact E.
  -
    intros i Hi. destruct (Z.eq_dec i (k + 1)) as [->|].
    + destruct NEWpos as (p0 & H0 & O0 & V0). exists p0. split; [left; lia|]. rewrite V0. subst node. lia.
    + destruct (INT i ltac:(lia)) as (q & Hq & E).
      destruct (OLDsur q ltac:(unfold PP; lia)) as (p & Hp & Hpq).
      exists p. destruct (VALS p Hp) as [(O1 & R1 & V1)|(O1 & O1' & V1)]; [lia|].
      rewrite V1, Hpq. split; [|exact E].
      unfold PP in Hp. destruct Hp as [Hp|Hp]; [left; exact Hp|]. right.
      destruct (Z.eq_dec p (hm - 1)) as [->|]; [lia|].
      destruct (Z.eq_dec p (hm - 2)) as [->|]; [lia|].
      rewrite <- Hpq in Hq. 
      assert (old p = p).
      { destruct (VALS p ltac:(unfold PP; lia)) as [(X1 & _)|(X1 & X2 & X3)]; [lia|].
        rewrite HPe_hi in X3 by lia. apply INJ; [exact O1| unfold PP; lia| symmetry; exact X3]. }
      lia.
  -
    intros h Hh. destruct (Z.eq_dec h (hm - 1)) as [->|].
    { rewrite HPe_n, DL'v, Z.eqb_refl. cbn [orb]. subst node. lia. }
    destruct (Z.eq_dec h (hm - 2)) as [->|].
    { rewrite HPe_m, DL'v, Z.eqb_refl, Bool.orb_true_r. subst node. lia. }
    rewrite HPe_hi by lia. rewrite DL'v. destruct (EXTR h ltac:(lia)) as [E1 E2].
    destruct (Z.eqb_spec (arr_get HP h) n); [congruence|]. destruct (Z.eqb_spec (arr_get HP h) m); [congruence|]. cbn [orb].
    apply DAD. lia.
  -
    intros j Hj. rewrite FC'v. destruct (Z.eqb_spec j node); [lia|]. apply IFC. exact Hj.
  -
    replace (zsum (map (fun p : Z => arr_get FC' (arr_get HPe p)) (ziota 1 (Z.to_nat (hl - 1))))) with (zsum (map (arr_get FC') Le))
      by (subst Le; rewrite map_map; reflexivity).
    rewrite (zsum_map_perm _ _ _ Pe). cbn [map zsum]. rewrite FC'v, Z.eqb_refl.
    rewrite (zsum_map_ext (arr_get FC') (arr_get FC) La); [lia|].
    intros x Hx. rewrite FC'v. destruct (Z.eqb_spec x node); [|reflexivity]. exfalso.
    subst La. apply in_map_ziota in Hx. destruct Hx as (p & Hp & E). destruct (PHI p ltac:(lia)) as [P1 P2].
    pose proof (IDS (phi p) ltac:(unfold PP; lia)). rewrite P2 in E. lia.
  -
    intros h Hh.
    assert (FCX : forall h', hm <= h' <= 572 -> arr_get FC' (arr_get HPe h') = arr_get FC (arr_get HP h')).
    { intros h' Hh'. rewrite HPe_hi by lia. rewrite FC'v. pose proof (IDS h' ltac:(unfold PP; lia)).
      destruct (Z.eqb_spec (arr_get HP h') node); [lia| reflexivity]. }
    assert (FCn : arr_get FC' n = arr_get FC n) by (rewrite FC'v; destruct (Z.eqb_spec n node); [lia| reflexivity]).
    assert (FCm : arr_get FC' m = arr_get FC m) by (rewrite FC'v; destruct (Z.eqb_spec m node); [lia| reflexivity]).
    destruct (Z.eq_dec h (hm - 2)) as [->|].
    { replace (hm - 2 + 1) with (hm - 1) by lia. rewrite HPe_n, HPe_m, FCn, FCm. destruct Hm as [M1 M2]. rewrite M2. apply MINn. lia. }
    destruct (Z.eq_dec h (hm - 1)) as [->|].
    { replace (hm - 1 + 1) with hm by lia. rewrite HPe_n, FCn, FCX by lia. subst n. apply WHEAP; lia. }
    rewrite !FCX by lia. apply WORD. lia.
  -
    intros p h Hp Hh.
    assert (FCn : arr_get FC' n = arr_get FC n) by (rewrite FC'v; destruct (Z.eqb_spec n node); [lia| reflexivity]).
    assert (FCm : arr_get FC' m = arr_get FC m) by (rewrite FC'v; destruct (Z.eqb_spec m node); [lia| reflexivity]).
    assert (LOW : arr_get FC m <= arr_get FC' (arr_get HPe p)).
    { destruct (Be p ltac:(lia)) as (R1 & R2 & R3 & R4 & R5). rewrite R5, HPdv.
      destruct (Z.eqb_spec (fe p) 1); [rewrite FC'v, Z.eqb_refl; lia|].
      destruct (Z.eqb_spec (fe p) (hm - 2)); [lia|]. destruct (Z.eqb_spec (fe p) (hm - 1)); [lia|].
      destruct (PHI (fe p) ltac:(lia)) as [P1 P2]. pose proof (IDS (phi (fe p)) ltac:(unfold PP; lia)).
      rewrite FC'v. rewrite P2 in *. destruct (Z.eqb_spec (arr_get HP (phi (fe p))) node); [lia|].
      rewrite <- P2. apply MINm. lia. }
    assert (NM : arr_get FC n <= arr_get FC m) by (destruct Hm as [M1 M2]; rewrite M2; apply MINn; lia).
    destruct (Z.eq_dec h (hm - 2)) as [->|]; [rewrite HPe_m, FCm; exact LOW|].
    destruct (Z.eq_dec h (hm - 1)) as [->|]; [rewrite HPe_n, FCn; lia|].
    rewrite HPe_hi by lia. rewrite FC'v. pose proof (IDS h ltac:(unfold PP; lia)).
    destruct (Z.eqb_spec (arr_get HP h) node); [lia|].
    pose proof (WHEAP 1 h ltac:(lia) ltac:(lia)). fold n in H0. lia.
  -
    intros p Hp. destruct (VALS p Hp) as [(O1 & R1 & V1)|(O1 & O1' & V1)]; rewrite V1.
    +
      rewrite Z.eqb_refl.
      pose proof (SUB 1 ltac:(unfold PP; lia)) as Sn. fold n in Sn.
      pose proof (SUB (phi 1) ltac:(unfold PP; lia)) as Sm. destruct Hm as [M1 M2]. rewrite <- M2 in Sm.
      destruct Sn as (Wn' & Mn & FLn & FNn & CHn). destruct Sm as (Wm' & Mm & FLm & FNm & CHm).
      split; [cbn [hw]; rewrite FC'v, Z.eqb_refl; lia|].
      split; [cbn; auto|]. split; [intros; lia|]. split; [intros; eexists _, _; reflexivity|].
      assert (G : forall x T (CHx : forall e, In e (hprof 0 T) ->
                     In (ea e) UPl /\ 0 <= ed e /\ up DL (Z.to_nat (ed e)) (ea e) = x /\
                     (forall i, (i < Z.to_nat (ed e))%nat -> up DL i (ea e) < up DL (S i) (ea e) /\ exists h, hm <= h <= 572 /\ arr_get HP h = up DL i (ea e)))
                     (hx : Z), hm - 2 <= hx <= 572 -> arr_get HPe hx = x -> x < node -> arr_get DL' x = node ->
                     (x = n \/ x = m) ->
                     forall e, In e (hprof 1 T) ->
                     In (ea e) UPl /\ 0 <= ed e /\ up DL' (Z.to_nat (ed e)) (ea e) = node /\
                     (forall i, (i < Z.to_nat (ed e))%nat -> up DL' i (ea e) < up DL' (S i) (ea e) /\
                        exists h, hm - 2 <= h <= 572 /\ arr_get HPe h = up DL' i (ea e))).
      { intros x T CHx hx Hhx Ehx Xn DLx Xnm e He.
        destruct (in_hprof1 T e He) as (e0 & He0 & Ew & Ed).
        rewrite hprof_shift in He. apply in_map_iff in He. destruct He as (e0' & Ee & He0').
        assert (Ea : ea e = ea e0') by (rewrite <- Ee; reflexivity).
        assert (Ed' : ed e = ed e0' + 1) by (rewrite <- Ee; reflexivity). clear e0 He0 Ew Ed.
        destruct (CHx e0' He0') as (A1 & A2 & A3 & A4). rewrite Ea.
        assert (UQ : forall i, (i <= Z.to_nat (ed e0'))%nat -> up DL' i (ea e0') = up DL i (ea e0')).
        { intros i Hi. apply up_ext. intros s0 Hs0. destruct (A4 s0 ltac:(lia)) as (_ & h & Hh & Eh).
          rewrite DL'v, <- Eh. destruct (EXTR h Hh) as [E1 E2].
          destruct (Z.eqb_spec (arr_get HP h) n); [congruence|]. destruct (Z.eqb_spec (arr_get HP h) m); [congruence|]. reflexivity. }
        split; [exact A1|]. split; [lia|].
        replace (Z.to_nat (ed e)) with (S (Z.to_nat (ed e0'))) by lia. cbn [up].
        rewrite UQ, A3 by lia. split; [exact DLx|].
        intros i Hi. destruct (Nat.eq_dec i (Z.to_nat (ed e0'))) as [->|].
        - cbn [up]. rewrite UQ, A3, DLx by lia. split; [lia|]. exists hx. split; [lia|]. exact Ehx.
        - change (up DL' (S i) (ea e0')) with (arr_get DL' (up DL' i (ea e0'))).
          rewrite UQ by lia. destruct (A4 i ltac:(lia)) as (B1 & h & Hh & Eh).
          change (arr_get DL' (up DL i (ea e0'))) with (up DL' (S i) (ea e0')) || idtac.
          split.
          + cbn [up] in B1. rewrite DL'v. rewrite <- Eh at 1. destruct (EXTR h Hh) as [E1 E2].
            rewrite <- Eh in B1 |- *.
            destruct (Z.eqb_spec (arr_get HP h) n); [congruence|]. destruct (Z.eqb_spec (arr_get HP h) m); [congruence|]. cbn [orb]. exact B1.
          + exists h. split; [lia|]. rewrite HPe_hi by lia. exact Eh. }
      intros e He. cbn [hprof] in He. rewrite Z.add_0_l in He. apply in_app_iff in He.
      destruct He as [He|He].
      * eapply (G n (sub n) CHn (hm - 1)); try lia; auto. rewrite DL'v, Z.eqb_refl. reflexivity.
      * eapply (G m (sub m) CHm (hm - 2)); try lia; auto. rewrite DL'v, Z.eqb_refl, Bool.orb_true_r. reflexivity.
    +
      pose proof (IDS (old p) O1). destruct (Z.eqb_spec (arr_get HP (old p)) node); [lia|].
      apply SUBX. exact O1.
  -
    intros T HT. apply HB.
    apply HB_step with (F' := HN (sub n) (sub m) :: map sub La).
    + apply HStep. { rewrite (Permutation_map sub P0). cbn. apply Permutation_refl. }
      intros T' HT'. apply in_map_iff in HT'. destruct HT' as (x & <- & Hx).
      subst La. apply in_map_ziota in Hx. destruct Hx as (p & Hp & <-).
      destruct (PHI p ltac:(lia)) as [P1 P2].
      destruct (SUB 1 ltac:(unfold PP; lia)) as (W1 & _). fold n in W1.
      destruct Hm as [M1 M2].
      destruct (SUB (phi 1) ltac:(unfold PP; lia)) as (W2 & _). rewrite <- M2 in W2.
      destruct (SUB (phi p) ltac:(unfold PP; lia)) as (W3 & _). rewrite <- P2 in W3.
      rewrite W1, W2, W3. split; [rewrite P2; apply MINn; lia| apply MINm; lia].
    + eapply hbuild_perm; [|exact HT].
      change (map (fun x => if x =? node then HN (sub n) (sub m) else sub x) (map (arr_get HPe) (ziota 1 (Z.to_nat (hl - 1)))))
        with (map (fun x => if x =? node then HN (sub n) (sub m) else sub x) Le).
      rewrite (Permutation_map _ Pe). cbn [map]. rewrite Z.eqb_refl. apply perm_skip.
      erewrite map_ext_in; [apply Permutation_refl|].
      intros x Hx. cbn beta. destruct (Z.eqb_spec x node); [|reflexivity]. exfalso.
      subst La. apply in_map_ziota in Hx. destruct Hx as (p & Hp & E). destruct (PHI p ltac:(lia)) as [P1 P2].
      pose proof (IDS (phi p) ltac:(unfold PP; lia)). rewrite P2 in E. lia.
  -
    intros j Hj Hnj. rewrite DL'v.
    destruct (Z.eqb_spec j n).
    { exfalso. pose proof (RNG 1 ltac:(unfold PP; lia)) as R1. fold n in R1. destruct R1 as [[A B]|A]; [apply Hnj; congruence| lia]. }
    destruct (Z.eqb_spec j m).
    { exfalso. destruct Hm as [M1 M2]. pose proof (RNG (phi 1) ltac:(unfold PP; lia)) as R1. rewrite <- M2 in R1.
      destruct R1 as [[A B]|A]; [apply Hnj; congruence| lia]. }
    cbn [orb]. apply DL0; assumption.
Qed.


Theorem loop4_inv : forall f k FC DL HP hl hm DP sub node,
  Inv4 k FC DL HP hl hm DP sub -> 2 <= hl -> (Z.to_nat (hl - 1) <= f)%nat -> node = elems + k ->
  exists FC' DL' HP' DP' sub',
    build_tree_loop4 f (W6 FC DL HP hl hm DP) t node = W6 FC' DL' HP' 1 (hm - 2 * (hl - 1)) DP'
    /\ Inv4 (k + (hl - 1)) FC' DL' HP' 1 (hm - 2 * (hl - 1)) DP' sub'.
Proof.
  induction f as [|f IH]; intros k FC DL HP hl hm DP sub node INV Hhl Hf Hnode; [lia|].
  rewrite L4_step. subst node.
  destruct (trip_inv k FC DL HP hl hm DP sub INV Hhl) as (FC1 & DL1 & HP1 & DP1 & sub1 & E1 & INV1).
  rewrite E1. destruct (Z.leb_spec 2 (hl - 1)).
  - destruct (IH (k + 1) FC1 DL1 HP1 (hl - 1) (hm - 2) DP1 sub1 (elems + k + 1) INV1 ltac:(lia) ltac:(lia) ltac:(lia))
      as (FC' & DL' & HP' & DP' & sub' & E' & INV').
    exists FC', DL', HP', DP', sub'. rewrite E'.
    replace (hm - 2 - 2 * (hl - 1 - 1)) with (hm - 2 * (hl - 1)) in * by lia.
    replace (k + 1 + (hl - 1 - 1)) with (k + (hl - 1)) in INV' by lia.
    split; [reflexivity| exact INV'].
  - exists FC1, DL1, HP1, DP1, sub1.
    replace (hl - 1) with 1 in * by lia. replace (hm - 2 * 1) with (hm - 2) by lia.
    split; [reflexivity| exact INV1].
Qed.

Theorem inv4_start : forall FC DL HP DP,
  arr_len FC = tsize t -> arr_len DL = tsize t -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall j, arr_get FC j = FPf j) ->
  (forall j, 0 <= j < elems -> arr_get FC0 j = 0 -> arr_get DL j = 0) ->
  (exists HP2, rearr HP2 HP 1 u /\ forall i, 1 <= i <= u -> arr_get HP2 i = nth (Z.to_nat (i - 1)) UPl 0) ->
  heap_ok FC DP HP 1 0 u ->
  Inv4 0 FC DL HP u 573 DP (fun j => HuffTree.HL (FPf j) j).
Proof.
  intros FC DL HP DP LFC1 LDL LHP LDP HFC HDL (HP2 & RR & HHP2) OK.
  pose proof (pads_facts t FC0) as (NDU & RNGU & U2 & PD & MX1 & MX2). fold u in U2.
  pose proof UP_len_elems as UE. pose proof (elems_tsize t) as ET.
  destruct RR as (_ & HPout & f & g & B).
  assert (CELL : forall p, 1 <= p <= u -> arr_get HP p = nth (Z.to_nat (f p - 1)) UPl 0 /\ 1 <= f p <= u).
  { intros p Hp. destruct (B p Hp) as (R1 & R2 & R3 & R4 & R5). rewrite R5, HHP2 by lia. split; [reflexivity| lia]. }
  assert (INU : forall p, 1 <= p <= u -> In (arr_get HP p) UPl).
  { intros p Hp. destruct (CELL p Hp) as [-> Fp]. apply nth_In. unfold u, zlen in *. lia. }
  assert (PP0 : forall p, PP u 573 p <-> 1 <= p <= u) by (intros; unfold PP; lia).
  split.
  - repeat split; assumption.
  - lia.
  - exact OK.
  - intros p q Hp Hq E. apply PP0 in Hp. apply PP0 in Hq.
    destruct (CELL p Hp) as [Ep Fp]. destruct (CELL q Hq) as [Eq Fq]. rewrite Ep, Eq in E.
    pose proof (proj1 (NoDup_nth UPl 0) NDU (Z.to_nat (f p - 1)) (Z.to_nat (f q - 1)) ltac:(unfold u, zlen in *; lia) ltac:(unfold u, zlen in *; lia) E).
    destruct (B p Hp) as (R1 & R2 & R3 & R4 & R5). destruct (B q Hq) as (Q1 & Q2 & Q3 & Q4 & Q5).
    rewrite <- R3, <- Q3. f_equal. lia.
  - intros p Hp. apply PP0 in Hp. left. split; [apply INU; lia|]. apply RNGU. apply INU. lia.
  - intros j Hj. apply In_nth with (d := 0) in Hj. destruct Hj as (i & Hi & <-).
    exists (g (Z.of_nat i + 1)). destruct (B (Z.of_nat i + 1) ltac:(unfold u, zlen in *; lia)) as (R1 & R2 & R3 & R4 & R5).
    split; [apply PP0; lia|]. destruct (CELL (g (Z.of_nat i + 1)) ltac:(lia)) as [-> _]. rewrite R4. f_equal. lia.
  - intros; lia.
  - intros; lia.
  - intros j Hj. apply HFC.
  - unfold Ftot.
    replace (zsum (map (fun p : Z => arr_get FC (arr_get HP p)) (ziota 1 (Z.to_nat u)))) with (zsum (map FPf (map (arr_get HP) (ziota 1 (Z.to_nat u))))).
    2:{ rewrite map_map. apply (f_equal zsum). apply map_ext. intros; symmetry; apply HFC. }
    apply zsum_map_perm. apply NoDup_Permutation.
    + apply NoDup_map_ziota. intros p q Hp Hq E.
      destruct (CELL p ltac:(lia)) as [Ep Fp]. destruct (CELL q ltac:(lia)) as [Eq Fq]. rewrite Ep, Eq in E.
      pose proof (proj1 (NoDup_nth UPl 0) NDU (Z.to_nat (f p - 1)) (Z.to_nat (f q - 1)) ltac:(unfold u, zlen in *; lia) ltac:(unfold u, zlen in *; lia) E).
      destruct (B p ltac:(lia)) as (R1 & R2 & R3 & R4 & R5). destruct (B q ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5).
      rewrite <- R3, <- Q3. f_equal. lia.
    + exact NDU.
    + intros x. rewrite in_map_ziota. split.
      * intros (p & Hp & <-). apply INU. lia.
      * intros Hx. apply In_nth with (d := 0) in Hx. destruct Hx as (i & Hi & <-).
        exists (g (Z.of_nat i + 1)). destruct (B (Z.of_nat i + 1) ltac:(unfold u, zlen in *; lia)) as (R1 & R2 & R3 & R4 & R5).
        split; [lia|]. destruct (CELL (g (Z.of_nat i + 1)) ltac:(lia)) as [-> _]. rewrite R4. f_equal. lia.
  - intros; lia.
  - intros; lia.
  - intros p Hp. apply PP0 in Hp. pose proof (INU p Hp) as IN. pose proof (RNGU _ IN) as R.
    split; [cbn; symmetry; apply HFC|]. split; [cbn; apply FP_pos; exact IN|].
    split; [reflexivity|]. split; [intros; lia|].
    intros e [<-|[]]. cbn. split; [exact IN|]. split; [lia|]. split; [reflexivity|]. intros; lia.
  - intros T HT. unfold F0. eapply hbuild_perm; [|exact HT]. apply Permutation_map.
    apply NoDup_Permutation.
    + apply NoDup_map_ziota. intros p q Hp Hq E.
      destruct (CELL p ltac:(lia)) as [Ep Fp]. destruct (CELL q ltac:(lia)) as [Eq Fq]. rewrite Ep, Eq in E.
      pose proof (proj1 (NoDup_nth UPl 0) NDU (Z.to_nat (f p - 1)) (Z.to_nat (f q - 1)) ltac:(unfold u, zlen in *; lia) ltac:(unfold u, zlen in *; lia) E).
      destruct (B p ltac:(lia)) as (R1 & R2 & R3 & R4 & R5). destruct (B q ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5).
      rewrite <- R3, <- Q3. f_equal. lia.
    + exact NDU.
    + intros x. rewrite in_map_ziota. split.
      * intros (p & Hp & <-). apply INU. lia.
      * intros Hx. apply In_nth with (d := 0) in Hx. destruct Hx as (i & Hi & <-).
        exists (g (Z.of_nat i + 1)). destruct (B (Z.of_nat i + 1) ltac:(unfold u, zlen in *; lia)) as (R1 & R2 & R3 & R4 & R5).
        split; [lia|]. destruct (CELL (g (Z.of_nat i + 1)) ltac:(lia)) as [-> _]. rewrite R4. f_equal. lia.
  - intros j Hj Hnj. apply HDL; [exact Hj|].
    destruct (Z.eq_dec (arr_get FC0 j) 0); [assumption|]. exfalso. apply Hnj.
    unfold UP. apply in_app_iff. left. unfold Ulist. apply Ul_in; lia.
Qed.

End Loop4.



Theorem build_tree_front : forall s t,
  tree_lens s ->
  (forall j, 0 <= j < sd_elems t -> 0 <= Freq s t j) ->
  Ftot t (tree_fc s t) < 2 ^ 16 ->
  0 <= ds_opt_len s < 2 ^ 64 -> 0 <= ds_static_len s < 2 ^ 64 ->
  exists FC DL HP DP sub,
    build_tree s t =
      gen_codes (gen_bitlen
        (bt_upd s t FC DL (arr_set HP (575 - 2 * u t (tree_fc s t) - 1) (arr_get HP 1)) 1 (575 - 2 * u t (tree_fc s t) - 1) DP
                (ds_bl_count s) (wrap64 (ds_opt_len s - zlen (pads (tree_fc s t) t)))
                (if stree_has t then wrap64 (ds_static_len s - sl_pad t (tree_fc s t)) else ds_static_len s)
                (MCP (tree_fc s t) t)) t) t (MCP (tree_fc s t) t)
    /\ Inv4 t (tree_fc s t) (u t (tree_fc s t) - 1) FC DL HP 1 (575 - 2 * u t (tree_fc s t)) DP sub.
Proof.
  intros s t TL Fnn FB OLr SLr.
  pose proof (tree_lens_fc s t TL) as LFC. pose proof (tree_lens_dl s t TL) as LDL.
  assert (LHP : arr_len (ds_heap s) = 573) by (unfold tree_lens in TL; tauto).
  assert (LDP : arr_len (ds_depth s) = 573) by (unfold tree_lens in TL; tauto).
  pose proof (elems_tsize t) as ET.
  pose proof (pads_facts t (tree_fc s t)) as (NDU & RNGU & U2 & _).
  pose proof (UP_len_elems t (tree_fc s t)) as UE.
  set (FC0 := tree_fc s t) in *.
  destruct (loop1_flat s t FC0 HEAP_SIZE (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t)
              (Z.to_nat (sd_elems t)) 0 (tree_dl s t) (ds_heap s) 0 (ds_depth s) (-1)
              ltac:(lia) ltac:(lia) LHP LDP LDL ltac:(reflexivity) ltac:(intros; lia) ltac:(intros; lia) ltac:(reflexivity))
    as (DL1 & HP1 & DP1 & E1 & LHP1 & LDP1 & LDL1 & HHP1 & HDL1).
  destruct (loop2_flat s t FC0 HEAP_SIZE (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t) LFC
              DL1 HP1 DP1 OLr SLr LHP1 LDP1 HHP1)
    as (FC2 & HP2 & DP2 & E2 & LFC2 & LHP2 & LDP2 & HFC2 & HHP2).
  destruct (heapify_flat0 s t FC2 DL1 (zlen (UP FC0 t)) HEAP_SIZE DP2 (ds_bl_count s)
              (wrap64 (ds_opt_len s - zlen (pads FC0 t)))
              (if stree_has t then wrap64 (ds_static_len s - sl_pad t FC0) else ds_static_len s)
              (MCP FC0 t) HP2 LHP2 ltac:(unfold u in UE; lia))
    as (HP3 & E3 & LHP3 & RR3 & OK3).
  pose proof (inv4_start t FC0 ltac:(intros j Hj; unfold Freq in Fnn; apply Fnn; exact Hj)
                FC2 DL1 HP3 DP2 LFC2 LDL1 LHP3 LDP2 HFC2 HDL1
                ltac:(exists HP2; split; [exact RR3| exact HHP2]) OK3) as I0.
  destruct (loop4_inv s t FC0 (ds_bl_count s) (wrap64 (ds_opt_len s - zlen (pads FC0 t)))
              (if stree_has t then wrap64 (ds_static_len s - sl_pad t FC0) else ds_static_len s)
              (MCP FC0 t) FB
              573%nat 0 FC2 DL1 HP3 (u t FC0) 573 DP2 _ (sd_elems t) I0 ltac:(unfold u in *; lia) ltac:(unfold u in *; lia) ltac:(lia))
    as (FC & DL & HP & DP & sub & E4 & INV).
  exists FC, DL, HP, DP, sub. split.
  - rewrite <- (bt_upd_self s t) at 1. unfold build_tree. fold FC0. autorewrite with btupd.
    change HEAP_SIZE with 573 in *. rewrite E1. cbv beta iota.
    rewrite E2. cbv beta iota. autorewrite with btupd. rewrite E3.
    unfold u in E4 |- *. rewrite E4. unfold SMALLEST. autorewrite with btupd.
    replace (573 - 2 * (zlen (UP FC0 t) - 1) - 1) with (575 - 2 * zlen (UP FC0 t) - 1) by lia. reflexivity.
  - replace (575 - 2 * u t FC0) with (573 - 2 * (u t FC0 - 1)) by lia.
    replace (u t FC0 - 1) with (0 + (u t FC0 - 1)) at 1 by lia. exact INV.
Qed.

Ltac Zify.zify_post_hook ::= idtac.
