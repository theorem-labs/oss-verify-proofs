(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac inb_true k HP :=
  replace ((0 <=? k) && (k <? arr_len HP)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).

Lemma zone_pop : forall HP hl hm V,
  zone_ok HP hl hm V -> 2 <= hl -> hl < hm -> hl < arr_len HP ->
  zone_ok (arr_set HP 1 (arr_get HP hl)) (hl - 1) hm (fun u => V u /\ u <> arr_get HP 1).
Proof.
  intros HP hl hm V [pos [A B]] Hhl Hlm HL.
  assert (L1 : live hl hm 1) by (left; lia). assert (Lh : live hl hm hl) by (left; lia).
  destruct (A 1 L1) as [V1 P1]. destruct (A hl Lh) as [Vh Ph].
  exists (fun u => if Z.eq_dec u (arr_get HP hl) then 1 else pos u). split.
  - intros i Hi. rewrite arr_get_set. unfold arr_inb.
    destruct (Z.eqb_spec 1 i) as [<-|N1].
    + inb_true 1 HP. cbn [andb]. split.
      * split; [exact Vh|]. intros E. rewrite E, P1 in Ph. lia.
      * destruct (Z.eq_dec _ _); [reflexivity | congruence].
    + cbn [andb]. assert (Li : live hl hm i) by (unfold live in *; lia).
      destruct (A i Li) as [Vi Pi]. split.
      * split; [exact Vi|]. intros E. rewrite E, P1 in Pi. exact (N1 Pi).
      * destruct (Z.eq_dec (arr_get HP i) (arr_get HP hl)) as [E|NE]; [|exact Pi].
        exfalso. rewrite E, Ph in Pi. unfold live in Hi. lia.
  - intros u [Hu Nu]. destruct (B u Hu) as [Lu Eu].
    destruct (Z.eq_dec u (arr_get HP hl)) as [->|NE].
    + split; [left; lia|]. rewrite arr_get_set. unfold arr_inb. rewrite Z.eqb_refl. inb_true 1 HP. reflexivity.
    + assert (pos u <> hl) by (intros E; apply NE; rewrite <- Eu, E; reflexivity).
      assert (pos u <> 1) by (intros E; apply Nu; rewrite <- Eu, E; reflexivity).
      split; [unfold live in *; lia|].
      rewrite arr_get_set. unfold arr_inb. destruct (Z.eqb_spec 1 (pos u)); [lia|]. cbn [andb]. exact Eu.
Qed.

Lemma zone_round : forall HP hl hm W n node,
  zone_ok HP hl hm W -> 1 <= hl -> hl + 3 <= hm -> hm <= 573 -> arr_len HP = 573 ->
  ~ W n -> ~ W node -> n <> node ->
  let m := arr_get HP 1 in
  zone_ok (arr_set (arr_set (arr_set HP (hm - 1) n) (hm - 2) m) 1 node) hl (hm - 2)
          (fun u => W u \/ u = n \/ u = node)
  /\ W m.
Proof.
  intros HP hl hm W n node [pos [A B]] Hhl Hhm Hhm' HL Nn Nnode Nnn. cbv zeta.
  assert (L1 : live hl hm 1) by (left; lia). destruct (A 1 L1) as [Vm Pm].
  set (m := arr_get HP 1) in *.
  split; [|exact Vm].
  exists (fun u => if Z.eq_dec u node then 1 else if Z.eq_dec u n then hm - 1 else if Z.eq_dec u m then hm - 2 else pos u).
  assert (G : forall i, arr_get (arr_set (arr_set (arr_set HP (hm - 1) n) (hm - 2) m) 1 node) i
                      = if 1 =? i then node else if hm - 2 =? i then m else if hm - 1 =? i then n else arr_get HP i).
  { intros i. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, HL.
    replace ((0 <=? 1) && (1 <? 573)) with true by reflexivity.
    replace ((0 <=? hm - 2) && (hm - 2 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace ((0 <=? hm - 1) && (hm - 1 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite !Bool.andb_true_r. reflexivity. }
  assert (Nmn : m <> n) by (intros E; apply Nn; rewrite <- E; exact Vm).
  assert (Nmnode : m <> node) by (intros E; apply Nnode; rewrite <- E; exact Vm).
  split.
  - intros i Hi. rewrite G.
    destruct (Z.eqb_spec 1 i) as [<-|N1].
    { split; [right; right; reflexivity|]. destruct (Z.eq_dec node node); [reflexivity | congruence]. }
    destruct (Z.eqb_spec (hm - 2) i) as [<-|N2].
    { split; [left; exact Vm|]. destruct (Z.eq_dec m node); [congruence|]. destruct (Z.eq_dec m n); [congruence|]. destruct (Z.eq_dec m m); [reflexivity | congruence]. }
    destruct (Z.eqb_spec (hm - 1) i) as [<-|N3].
    { split; [right; left; reflexivity|]. destruct (Z.eq_dec n node); [congruence|]. destruct (Z.eq_dec n n); [reflexivity | congruence]. }
    assert (Li : live hl hm i) by (unfold live in *; lia).
    destruct (A i Li) as [Vi Pi]. split; [left; exact Vi|].
    destruct (Z.eq_dec (arr_get HP i) node) as [E|_]; [exfalso; apply Nnode; rewrite <- E; exact Vi|].
    destruct (Z.eq_dec (arr_get HP i) n) as [E|_]; [exfalso; apply Nn; rewrite <- E; exact Vi|].
    destruct (Z.eq_dec (arr_get HP i) m) as [E|_]; [| exact Pi].
    exfalso. rewrite E, Pm in Pi. exact (N1 Pi).
  - intros u Hu.
    destruct (Z.eq_dec u node) as [->|Nu1].
    { split; [left; lia|]. rewrite G. rewrite Z.eqb_refl. reflexivity. }
    destruct (Z.eq_dec u n) as [->|Nu2].
    { split; [right; lia|]. rewrite G. replace (1 =? hm - 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (hm - 2 =? hm - 1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. reflexivity. }
    destruct (Z.eq_dec u m) as [->|Nu3].
    { split; [right; lia|]. rewrite G. replace (1 =? hm - 2) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. reflexivity. }
    destruct Hu as [Hu | [Hu | Hu]]; [| congruence | congruence].
    destruct (B u Hu) as [Lu Eu].
    assert (pos u <> 1) by (intros E; apply Nu3; unfold m; rewrite <- E, Eu; reflexivity).
    split; [unfold live in *; lia|].
    rewrite G. replace (1 =? pos u) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (hm - 2 =? pos u) with false by (symmetry; apply Z.eqb_neq; unfold live in Lu; lia).
    replace (hm - 1 =? pos u) with false by (symmetry; apply Z.eqb_neq; unfold live in Lu; lia).
    exact Eu.
Qed.

Section Loop4.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation U := (bt_upd s t).
Local Notation E := (sd_elems t).

Lemma loop4_unfold : forall f X node,
  build_tree_loop4 (S f) X t node =
  (let n := heap_get X SMALLEST in
   let X1 := pqdownheap (set_heap_len (heap_set X SMALLEST (heap_get X (ds_heap_len X))) (ds_heap_len X - 1)) t SMALLEST in
   let m := heap_get X1 SMALLEST in
   let X2 := heap_set (set_heap_max X1 (ds_heap_max X1 - 1)) (ds_heap_max X1 - 1) n in
   let X3 := heap_set (set_heap_max X2 (ds_heap_max X2 - 1)) (ds_heap_max X2 - 1) m in
   let X4 := set_Freq X3 t node (Freq X3 t n + Freq X3 t m) in
   let X5 := depth_set X4 node ((if depth_get X4 m <=? depth_get X4 n then depth_get X4 n else depth_get X4 m) + 1) in
   let X6 := heap_set (set_Dad (set_Dad X5 t m node) t n node) SMALLEST node in
   let X7 := pqdownheap X6 t SMALLEST in
   if 2 <=? ds_heap_len X7 then build_tree_loop4 f X7 t (node + 1) else X7).
Proof.

  intros f X node. cbv fix beta iota delta [build_tree_loop4]. fold build_tree_loop4.
  generalize pqdownheap. intros pq. cbv zeta. dsred. reflexivity.
Qed.

Lemma loop4_round : forall FC DL HP HL HM DP BC OL SL MC node V,
  zone_ok HP HL HM V -> 2 <= HL -> HL + 2 <= HM -> HM <= 573 ->
  arr_len HP = 573 -> arr_len FC = tsize t -> arr_len DL = tsize t -> arr_len DP = 573 ->
  ~ V node -> 0 <= node < tsize t -> (forall u, V u -> 0 <= u < node) ->
  exists HP4 n m,
    n = arr_get HP 1 /\ V n /\ V m /\ n <> m
    /\ (forall f, build_tree_loop4 (S f) (U FC DL HP HL HM DP BC OL SL MC) t node
         = let s4 := U (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m)))
                       (arr_set (arr_set DL m (wrap16 node)) n (wrap16 node))
                       HP4 (HL - 1) (HM - 2)
                       (arr_set DP node (wrap8 ((if arr_get DP m <=? arr_get DP n then arr_get DP n else arr_get DP m) + 1)))
                       BC OL SL MC in
           if 2 <=? HL - 1 then build_tree_loop4 f s4 t (node + 1) else s4)
    /\ zone_ok HP4 (HL - 1) (HM - 2) (fun u => V u \/ u = node)
    /\ arr_get HP4 (HM - 1) = n /\ arr_get HP4 (HM - 2) = m
    /\ (forall i, HM <= i -> arr_get HP4 i = arr_get HP i)
    /\ arr_len HP4 = 573
    /\ (forall i, HM <= i < 573 -> arr_get HP i <> n /\ arr_get HP i <> m).
Proof.
  intros FC DL HP HL HM DP BC OL SL MC node V HZ HHL HHM H573 LHP LFC LDL LDP Nnode Hnode Hlt.

  set (n := arr_get HP 1).
  pose proof (zone_pop HP HL HM V HZ HHL ltac:(lia) ltac:(lia)) as HZa. fold n in HZa.
  set (HPa := arr_set HP 1 (arr_get HP HL)) in HZa.
  set (Xa := U FC DL HPa (HL - 1) HM DP BC OL SL MC).
  destruct (pqdownheap_zone Xa t 1 HM (fun u => V u /\ u <> n)) as (Zb & Ob & Lb & Ab & Sb);
    [subst Xa; autorewrite with btupd; first [exact HZa | lia | (subst HPa; rewrite arr_len_set; exact LHP)] ..|].
  subst Xa. autorewrite with btupd in Zb. autorewrite with btupd in Ob. rewrite bt_heap_len in Lb.
  set (HPb := ds_heap (pqdownheap (U FC DL HPa (HL - 1) HM DP BC OL SL MC) t 1)) in *.

  assert (Vn : V n) by (apply (zone_ok_mem _ _ _ _ 1 HZ); left; lia).
  destruct (zone_round HPb (HL - 1) HM (fun u => V u /\ u <> n) n node Zb ltac:(lia) ltac:(lia) H573 Ab
              ltac:(intros [_ X]; exact (X eq_refl)) ltac:(intros [X _]; exact (Nnode X)) ltac:(pose proof (Hlt n Vn); lia))
    as [Zc [Vm Nmn]].
  set (m := arr_get HPb 1) in *.
  set (HPc := arr_set (arr_set (arr_set HPb (HM - 1) n) (HM - 2) m) 1 node) in *.
  set (FC' := arr_set FC node (wrap16 (arr_get FC n + arr_get FC m))).
  set (DL' := arr_set (arr_set DL m (wrap16 node)) n (wrap16 node)).
  set (DP' := arr_set DP node (wrap8 ((if arr_get DP m <=? arr_get DP n then arr_get DP n else arr_get DP m) + 1))).
  set (Xc := U FC' DL' HPc (HL - 1) (HM - 2) DP' BC OL SL MC).
  assert (LHPc : arr_len HPc = 573) by (subst HPc; rewrite !arr_len_set; exact Ab).
  destruct (pqdownheap_zone Xc t 1 (HM - 2) (fun u => (V u /\ u <> n) \/ u = n \/ u = node)) as (Zd & Od & Ld & Ad & Sd);
    [subst Xc; autorewrite with btupd; first [exact Zc | lia | exact LHPc] ..|].
  subst Xc. autorewrite with btupd in Zd. autorewrite with btupd in Od. rewrite bt_heap_len in Ld.
  set (HPd := ds_heap (pqdownheap (U FC' DL' HPc (HL - 1) (HM - 2) DP' BC OL SL MC) t 1)) in *.
  exists HPd, n, m.
  split; [reflexivity|]. split; [exact Vn|]. split; [exact Vm|]. split; [intros Emn; exact (Nmn (eq_sym Emn))|].
  split.
  { intros f. rewrite loop4_unfold. unfold SMALLEST. cbv zeta. autorewrite with btupd.
    fold n. fold HPa. rewrite Sb. autorewrite with btupd. fold m.
    replace (HM - 1 - 1) with (HM - 2) by lia.
    fold FC'. fold DP'. fold DL'. fold HPc.
    rewrite Sd. autorewrite with btupd. reflexivity. }
  split.
  { apply (zone_ok_ext _ _ _ (fun u => (V u /\ u <> n) \/ u = n \/ u = node)); [|exact Zd].
    intros u. split.
    - intros [[X _]|[->| ->]]; [left; exact X | left; exact Vn | right; reflexivity].
    - intros [X| ->]; [|right; right; reflexivity]. destruct (Z.eq_dec u n) as [->|]; [right; left; reflexivity | left; split; assumption]. }
  assert (G1 : arr_get HPc (HM - 1) = n).
  { subst HPc. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, Ab.
    replace (1 =? HM - 1) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (HM - 2 =? HM - 1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
    replace ((0 <=? HM - 1) && (HM - 1 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
  assert (G2 : arr_get HPc (HM - 2) = m).
  { subst HPc. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, Ab.
    replace (1 =? HM - 2) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
    replace ((0 <=? HM - 2) && (HM - 2 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
  split; [rewrite (Od (HM - 1)) by lia; exact G1|].
  split; [rewrite (Od (HM - 2)) by lia; exact G2|].
  split.
  { intros i Hi. rewrite (Od i) by lia. subst HPc. rewrite !arr_get_set.
    replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (HM - 2 =? i) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (HM - 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
    rewrite (Ob i) by lia. subst HPa. rewrite arr_get_set. replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  split; [exact Ad|].
  intros i Hi. split.
  - intros En. pose proof (zone_ok_inj _ _ _ _ i 1 HZ ltac:(right; lia) ltac:(left; lia) En). lia.
  - intros Em. assert (Ei : arr_get HPb i = arr_get HP i).
    { rewrite (Ob i) by lia. subst HPa. rewrite arr_get_set. replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    rewrite <- Ei in Em. pose proof (zone_ok_inj _ _ _ _ i 1 Zb ltac:(right; lia) ltac:(left; lia) Em). lia.
Qed.

Section WholeLoop.

Variable FC2 : arr.
Variable DL2 : arr.
Variable L : Z.
Variable BC : arr.
Variable OL : Z.
Variable SL : Z.
Variable MC : Z.

Definition V0 : Z -> Prop := Vscan FC2 E.

Definition Vj (j : Z) : Z -> Prop := fun u => V0 u \/ (E <= u < E + j).

Record INV4 (j : Z) (FCj DLj HPj DPj : arr) : Prop := {
  i4_zone : zone_ok HPj (L - j) (573 - 2 * j) (Vj j);
  i4_dad : forall i, 573 - 2 * j <= i < 573 -> arr_get DLj (arr_get HPj i) = E + (572 - i) / 2;
  i4_old : forall i, 573 - 2 * j <= i < 573 -> E <= arr_get HPj i -> arr_get HPj i < E + (572 - i) / 2;
  i4_fc : forall u, 0 <= u < E -> arr_get FCj u = arr_get FC2 u;
  i4_dl : forall u, 0 <= u < E -> arr_get FC2 u = 0 -> arr_get DLj u = arr_get DL2 u;
  i4_lhp : arr_len HPj = 573;
  i4_lfc : arr_len FCj = tsize t;
  i4_ldl : arr_len DLj = tsize t;
  i4_ldp : arr_len DPj = 573;
  i4_fcr : forall i, 0 <= arr_get FCj i < 65536;
  i4_dpr : forall i, 0 <= arr_get DPj i < 256;
  i4_dlr : forall i, 0 <= arr_get DLj i < 65536 }.

Hypothesis HL : 2 <= L <= E.

Lemma loop4_inv_step : forall j FCj DLj HPj DPj,
  0 <= j -> 2 <= L - j -> INV4 j FCj DLj HPj DPj ->
  exists FC' DL' HP' DP',
    (forall f, build_tree_loop4 (S f) (U FCj DLj HPj (L - j) (573 - 2 * j) DPj BC OL SL MC) t (E + j)
       = let s4 := U FC' DL' HP' (L - (j + 1)) (573 - 2 * (j + 1)) DP' BC OL SL MC in
         if 2 <=? L - (j + 1) then build_tree_loop4 f s4 t (E + (j + 1)) else s4)
    /\ INV4 (j + 1) FC' DL' HP' DP'.
Proof.
  intros j FCj DLj HPj DPj Hj Hr INV. pose proof (elems_range t) as HE.
  destruct INV as [Z0 D0 O0 F0 L0 LHP LFC LDL LDP RFC RDP RDL].
  destruct (loop4_round FCj DLj HPj (L - j) (573 - 2 * j) DPj BC OL SL MC (E + j) (Vj j) Z0
              ltac:(lia) ltac:(lia) ltac:(lia) LHP LFC LDL LDP)
    as (HP4 & n & m & En & Vn & Vm & Nnm & EQ & Z4 & G1 & G2 & O4 & L4 & D4).
  { unfold Vj, V0, Vscan. lia. } { lia. } { unfold Vj, V0, Vscan. intros u Hu. lia. }
  exists (arr_set FCj (E + j) (wrap16 (arr_get FCj n + arr_get FCj m))),
         (arr_set (arr_set DLj m (wrap16 (E + j))) n (wrap16 (E + j))), HP4,
         (arr_set DPj (E + j) (wrap8 ((if arr_get DPj m <=? arr_get DPj n then arr_get DPj n else arr_get DPj m) + 1))).
  split.
  { intros f. rewrite (EQ f). replace (L - j - 1) with (L - (j + 1)) by lia.
    replace (573 - 2 * j - 2) with (573 - 2 * (j + 1)) by lia. replace (E + j + 1) with (E + (j + 1)) by lia. reflexivity. }
  assert (Vlt : forall u, Vj j u -> 0 <= u < E + j) by (unfold Vj, V0, Vscan; intros u Hu; lia).
  pose proof (Vlt n Vn) as Rn. pose proof (Vlt m Vm) as Rm.
  assert (W16 : wrap16 (E + j) = E + j) by (apply wrap16_id; lia).
  constructor.
  - replace (L - (j + 1)) with (L - j - 1) by lia. replace (573 - 2 * (j + 1)) with (573 - 2 * j - 2) by lia.
    apply (zone_ok_ext _ _ _ (fun u => Vj j u \/ u = E + j)); [|exact Z4].
    unfold Vj. intros u. split; intros HH.
    + destruct HH as [[A|A]|A]; [left; exact A | right; lia | right; lia].
    + destruct HH as [A|A]; [left; left; exact A|]. destruct (Z.eq_dec u (E + j)); [right; lia | left; right; lia].
  - intros i Hi. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, LDL. rewrite W16.
    destruct (Z.eq_dec i (573 - 2 * j - 1)) as [->|N1].
    { rewrite G1. rewrite Z.eqb_refl. replace ((0 <=? n) && (n <? tsize t)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. replace (572 - (573 - 2 * j - 1)) with (j * 2) by lia. rewrite Z.div_mul by lia. reflexivity. }
    destruct (Z.eq_dec i (573 - 2 * j - 2)) as [->|N2].
    { rewrite G2. destruct (Z.eqb_spec n m); [exfalso; exact (Nnm ltac:(assumption))|]. cbn [andb]. rewrite Z.eqb_refl.
      replace ((0 <=? m) && (m <? tsize t)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. replace (572 - (573 - 2 * j - 2)) with (1 + j * 2) by lia. rewrite Z.div_add by lia. reflexivity. }
    rewrite O4 by lia. destruct (D4 i ltac:(lia)) as [Nin Nim].
    replace (n =? arr_get HPj i) with false by (symmetry; apply Z.eqb_neq; congruence).
    replace (m =? arr_get HPj i) with false by (symmetry; apply Z.eqb_neq; congruence). cbn [andb].
    apply D0. lia.
  - intros i Hi Hge.
    destruct (Z.eq_dec i (573 - 2 * j - 1)) as [->|N1]; [rewrite G1 in Hge |- *; replace (572 - (573 - 2 * j - 1)) with (j * 2) by lia; rewrite Z.div_mul by lia; lia|].
    destruct (Z.eq_dec i (573 - 2 * j - 2)) as [->|N2]; [rewrite G2 in Hge |- *; replace (572 - (573 - 2 * j - 2)) with (1 + j * 2) by lia; rewrite Z.div_add by lia; change (1 / 2) with 0; lia|].
    rewrite O4 in Hge |- * by lia. apply O0; lia.
  - intros u Hu. rewrite arr_get_set. replace (E + j =? u) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. apply F0. exact Hu.
  - intros u Hu Hz. rewrite !arr_get_set.
    assert (~ Vj j u) by (unfold Vj, V0, Vscan; lia).
    replace (n =? u) with false by (symmetry; apply Z.eqb_neq; congruence).
    replace (m =? u) with false by (symmetry; apply Z.eqb_neq; congruence). cbn [andb]. apply L0; assumption.
  - exact L4.
  - rewrite arr_len_set. exact LFC.
  - rewrite !arr_len_set. exact LDL.
  - rewrite arr_len_set. exact LDP.
  - intros i. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply RFC].
  - intros i. rewrite arr_get_set. destruct (_ && _); [apply wrap8_range | apply RDP].
  - intros i. rewrite !arr_get_set. destruct (_ && _); [apply wrap16_range|]. destruct (_ && _); [apply wrap16_range | apply RDL].
Qed.

Lemma loop4_spec : forall f j FCj DLj HPj DPj,
  0 <= j -> 2 <= L - j -> (Z.of_nat f >= L - j - 1) -> INV4 j FCj DLj HPj DPj ->
  exists FC' DL' HP' DP',
    build_tree_loop4 f (U FCj DLj HPj (L - j) (573 - 2 * j) DPj BC OL SL MC) t (E + j)
    = U FC' DL' HP' 1 (573 - 2 * (L - 1)) DP' BC OL SL MC
    /\ INV4 (L - 1) FC' DL' HP' DP'.
Proof.
  induction f as [|f IH]; intros j FCj DLj HPj DPj Hj Hr Hf INV; [lia|].
  destruct (loop4_inv_step j FCj DLj HPj DPj Hj Hr INV) as (FC' & DL' & HP' & DP' & EQ & INV').
  rewrite (EQ f). cbv zeta.
  destruct (Z.leb_spec 2 (L - (j + 1))) as [C|C].
  - apply (IH (j + 1)); [lia | lia | lia | exact INV'].
  - exists FC', DL', HP', DP'. replace (L - 1) with (j + 1) by lia. split; [| exact INV'].
    replace (L - (j + 1)) with 1 by lia. reflexivity.
Qed.
End WholeLoop.

Record heap_result (FC2 DL2 : arr) (L mc : Z) (FCf DLf HPf DPf : arr) : Prop := {
  hr_L : 2 <= L <= E;
  hr_mc : 0 <= mc < E;
  hr_mc_max : forall u, 0 <= u < E -> arr_get FC2 u <> 0 -> u <= mc;
  hr_mc_in : arr_get FC2 mc <> 0;
  hr_root : arr_get HPf (574 - 2 * L) = E + L - 2;
  hr_top : arr_get HPf 1 = E + L - 2;
  hr_tail : forall i, 574 - 2 * L < i < 573 -> Vj FC2 (L - 1) (arr_get HPf i);
  hr_dad : forall i, 574 - 2 * L < i < 573 -> arr_get DLf (arr_get HPf i) = E + (572 - i) / 2;
  hr_old : forall i, 574 - 2 * L < i < 573 -> E <= arr_get HPf i -> arr_get HPf i < E + (572 - i) / 2;
  hr_inj : forall i k, 574 - 2 * L <= i < 573 -> 574 - 2 * L <= k < 573 -> arr_get HPf i = arr_get HPf k -> i = k;
  hr_cov : forall u, Vj FC2 (L - 1) u -> exists i, 574 - 2 * L <= i < 573 /\ arr_get HPf i = u;
  hr_fc : forall u, 0 <= u < E -> arr_get FCf u = arr_get FC2 u;
  hr_dl0 : forall u, 0 <= u < E -> arr_get FC2 u = 0 -> arr_get DLf u = 0;
  hr_lhp : arr_len HPf = 573;
  hr_lfc : arr_len FCf = tsize t;
  hr_ldl : arr_len DLf = tsize t;
  hr_ldp : arr_len DPf = 573;
  hr_fcr : forall i, 0 <= arr_get FCf i < 65536;
  hr_dpr : forall i, 0 <= arr_get DPf i < 256;
  hr_dlr : forall i, 0 <= arr_get DLf i < 65536 }.

Theorem heap_phase : forall FC DL HP0 HL0 HM0 DP BC OL SL MC0,
  arr_len FC = tsize t -> arr_len DL = tsize t -> arr_len HP0 = 573 -> arr_len DP = 573 ->
  (forall i, 0 <= arr_get FC i < 65536) ->
  (forall i, 0 <= arr_get DL i < 65536) ->
  (forall i, 0 <= arr_get DP i < 256) ->
  let s0 := set_heap_max (set_heap_len (U FC DL HP0 HL0 HM0 DP BC OL SL MC0) 0) HEAP_SIZE in
  let '(s1, mc1) := build_tree_loop1 (Z.to_nat E) s0 t E 0 (-1) in
  let '(s2, mc) := build_tree_loop2 2%nat s1 t mc1 in
  let s3 := set_max_code s2 t mc in
  let s4 := build_tree_loop3 (Z.to_nat (ds_heap_len s3 / 2)) s3 t (ds_heap_len s3 / 2) in
  let s5 := build_tree_loop4 573%nat s4 t E in
  let s6 := set_heap_max s5 (ds_heap_max s5 - 1) in
  let s7 := heap_set s6 (ds_heap_max s6) (heap_get s6 SMALLEST) in
  exists Fl DL2 HP2 DP2 L FCf DLf HPf DPf,
    let FC2 := fc_forced Fl FC in
    s3 = U FC2 DL2 HP2 L 573 DP2 BC (ol_forced Fl OL) (sl_forced t Fl SL) mc
    /\ s7 = U FCf DLf HPf 1 (574 - 2 * L) DPf BC (ol_forced Fl OL) (sl_forced t Fl SL) mc
    /\ heap_result FC2 DL2 L mc FCf DLf HPf DPf
    /\ zone_ok HP2 L 573 (Vscan FC2 E) /\ arr_len HP2 = 573 /\ arr_len DP2 = 573 /\ arr_len DL2 = tsize t
    /\ (forall i, 0 <= arr_get DP2 i < 256) /\ (forall i, 0 <= arr_get FC2 i < 65536) /\ (forall i, 0 <= arr_get DL2 i < 65536)
    /\ (length Fl <= 2)%nat /\ NoDup Fl /\ (forall f, In f Fl -> 0 <= f < E /\ arr_get FC f = 0 /\ f <= 2)
    /\ (forall i, arr_get FC2 i = if existsb (Z.eqb i) Fl then 1 else arr_get FC i)
    /\ (forall i, arr_get DL2 i = if (0 <=? i) && (i <? E) && (arr_get FC i =? 0) then 0 else arr_get DL i).
Proof.
  intros FC DL HP0 HL0 HM0 DP BC OL SL MC0 LFC LDL LHP LDP RFC RDL RDP. pose proof (elems_range t) as HE.
  cbv zeta. autorewrite with btupd. unfold HEAP_SIZE.

  destruct (loop1_spec s t (Z.to_nat E) 0 (-1) FC DL HP0 0 DP BC OL SL MC0 ltac:(lia) ltac:(lia) ltac:(lia) LHP LDL)
    as (HP1 & HL1 & DL1 & DP1 & mc1 & E1 & B1 & B1' & LHP1 & LDL1 & Z1 & M1 & M1' & M1'' & I1 & DLE1 & HPE1 & DPR1 & LDP1).
  { apply (zone_ok_ext _ _ _ (fun _ => False)); [| apply zone_ok_empty]. unfold Vscan. intros u. lia. }
  { lia. } { intros; lia. } { intros; lia. } { lia. }
  rewrite E1.

  destruct (loop2_spec s t FC DL1 HP1 HL1 DP1 BC OL SL MC0 mc1
              ltac:(lia) LHP1 LFC Z1 M1 M1' M1'' I1)
    as (Fl & HP2 & HL2 & DP2 & mc2 & E2 & B2 & B2' & B2'' & LF & ND & FF & LHP2 & LFC2 & Z2 & M2 & M2' & M2'' & FCE2 & HPE2 & DPR2 & LDP2).
  rewrite E2. autorewrite with btupd.
  set (FC2 := fc_forced Fl FC) in *.

  assert (HL2h : 0 <= HL2 / 2 <= HL2) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  destruct (loop3_spec s t (Z.to_nat (HL2 / 2)) (HL2 / 2) FC2 DL1 HP2 HL2 573 DP2 BC
              (ol_forced Fl OL) (sl_forced t Fl SL) mc2 (Vscan FC2 E) HL2h ltac:(lia) ltac:(lia) LHP2 Z2)
    as (HP3 & E3 & Z3 & LHP3 & HPE3).
  rewrite E3.

  assert (DPR2' : forall i, 0 <= arr_get DP2 i < 256) by (intros i; apply DPR2; apply DPR1; apply RDP).
  assert (FCR2 : forall i, 0 <= arr_get FC2 i < 65536) by (intros i; rewrite FCE2; destruct (existsb _ _); [lia | apply RFC]).
  assert (DLR1 : forall i, 0 <= arr_get DL1 i < 65536) by (intros i; rewrite DLE1; destruct (_ && _); [lia | apply RDL]).
  assert (INV0 : INV4 FC2 DL1 HL2 0 FC2 DL1 HP3 DP2).
  { constructor; try assumption; try (intros; lia); try (intros; reflexivity); try (rewrite LDP2, LDP1; exact LDP).
    replace (HL2 - 0) with HL2 by lia. replace (573 - 2 * 0) with 573 by lia.
    apply (zone_ok_ext _ _ _ (Vscan FC2 E)); [|exact Z3]. unfold Vj, V0. intros u. split; [intros A; left; exact A | intros [A|A]; [exact A | lia]]. }
  destruct (loop4_spec FC2 DL1 HL2 BC (ol_forced Fl OL) (sl_forced t Fl SL) mc2 ltac:(lia)
              573 0 FC2 DL1 HP3 DP2 ltac:(lia) ltac:(lia) ltac:(lia) INV0)
    as (FCf & DLf & HPf & DPf & E4 & INVf).
  replace (HL2 - 0) with HL2 in E4 by lia. replace (573 - 2 * 0) with 573 in E4 by lia. replace (E + 0) with E in E4 by lia.
  rewrite E4. autorewrite with btupd. unfold SMALLEST.
  destruct INVf as [Zf Df Of Ff Lf LHPf LFCf LDLf LDPf RFCf RDPf RDLf].

  assert (TOP : arr_get HPf 1 = E + HL2 - 2).
  { destruct Zf as [pos [A B]].
    destruct (B (E + HL2 - 2) ltac:(unfold Vj; right; lia)) as [Lr Er]. unfold live in Lr.
    destruct Lr as [Lr|Lr]; [replace (pos (E + HL2 - 2)) with 1 in Er by lia; exact Er|].
    exfalso. pose proof (Of (pos (E + HL2 - 2)) ltac:(lia) ltac:(rewrite Er; lia)) as X. rewrite Er in X.
    assert ((572 - pos (E + HL2 - 2)) / 2 < HL2 - 1) by (apply Z.div_lt_upper_bound; lia). lia. }
  exists Fl, DL1, HP2, DP2, HL2, FCf, DLf, (arr_set HPf (573 - 2 * (HL2 - 1) - 1) (arr_get HPf 1)), DPf.
  split; [reflexivity|].
  split. { replace (574 - 2 * HL2) with (573 - 2 * (HL2 - 1) - 1) by lia. reflexivity. }
  split.
  { assert (G : forall i, arr_get (arr_set HPf (573 - 2 * (HL2 - 1) - 1) (arr_get HPf 1)) i = if i =? 574 - 2 * HL2 then E + HL2 - 2 else arr_get HPf i).
    { intros i. rewrite arr_get_set. unfold arr_inb. rewrite LHPf, TOP.
      replace (573 - 2 * (HL2 - 1) - 1) with (574 - 2 * HL2) by lia. rewrite (Z.eqb_sym (574 - 2 * HL2) i).
      destruct (Z.eqb_spec i (574 - 2 * HL2)); cbn [andb]; [|reflexivity].
      replace ((0 <=? 574 - 2 * HL2) && (574 - 2 * HL2 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
    constructor; try assumption; try lia.
    - rewrite G, Z.eqb_refl. reflexivity.
    - rewrite G. replace (1 =? 574 - 2 * HL2) with false by (symmetry; apply Z.eqb_neq; lia). exact TOP.
    - intros i Hi. rewrite G. replace (i =? 574 - 2 * HL2) with false by (symmetry; apply Z.eqb_neq; lia).
      apply (zone_ok_mem _ _ _ _ i Zf). right. lia.
    - intros i Hi. rewrite G. replace (i =? 574 - 2 * HL2) with false by (symmetry; apply Z.eqb_neq; lia). apply Df. lia.
    - intros i Hi. rewrite G. replace (i =? 574 - 2 * HL2) with false by (symmetry; apply Z.eqb_neq; lia). apply Of. lia.
    - intros i k Hi Hk. rewrite !G.
      destruct (Z.eqb_spec i (574 - 2 * HL2)) as [->|Ni]; destruct (Z.eqb_spec k (574 - 2 * HL2)) as [->|Nk]; intros EQ; try lia.
      + exfalso. pose proof (Of k ltac:(lia) ltac:(rewrite <- EQ; lia)) as X. rewrite <- EQ in X.
        assert ((572 - k) / 2 < HL2 - 1) by (apply Z.div_lt_upper_bound; lia). lia.
      + exfalso. pose proof (Of i ltac:(lia) ltac:(rewrite EQ; lia)) as X. rewrite EQ in X.
        assert ((572 - i) / 2 < HL2 - 1) by (apply Z.div_lt_upper_bound; lia). lia.
      + exact (zone_ok_inj _ _ _ _ i k Zf ltac:(right; lia) ltac:(right; lia) EQ).
    - intros u Hu. destruct Zf as [pos [A B]]. destruct (B u Hu) as [Lu Eu]. unfold live in Lu.
      destruct Lu as [Lu|Lu].
      + exists (574 - 2 * HL2). split; [lia|]. rewrite G, Z.eqb_refl. rewrite <- TOP. replace 1 with (pos u) by lia. exact Eu.
      + exists (pos u). split; [lia|]. rewrite G. replace (pos u =? 574 - 2 * HL2) with false by (symmetry; apply Z.eqb_neq; lia). exact Eu.
    - intros u Hu Hz. rewrite (Lf u Hu Hz). rewrite DLE1.
      replace (0 <=? u) with true by (symmetry; apply Z.leb_le; lia). replace (u <? E) with true by (symmetry; apply Z.ltb_lt; lia).
      assert (Fz : arr_get FC u = 0).
      { subst FC2. rewrite FCE2 in Hz. destruct (existsb _ _); [lia | exact Hz]. }
      rewrite Fz. reflexivity.
    - rewrite arr_len_set. exact LHPf. }
  split; [exact Z2|]. split; [exact LHP2|]. split; [rewrite LDP2, LDP1; exact LDP|]. split; [exact LDL1|].
  split; [exact DPR2'|]. split; [exact FCR2|]. split; [exact DLR1|].
  split; [exact LF|]. split; [exact ND|]. split; [exact FF|]. split; [exact FCE2 | exact DLE1].
Qed.

End Loop4.
