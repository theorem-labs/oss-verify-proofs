(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeO1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac inb_t i HP := replace ((0 <=? i) && (i <? arr_len HP)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).

Section Loop4o.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation U := (bt_upd s t).
Local Notation E := (sd_elems t).

(* [comment removed for export] *)
Lemma round_o : forall FC DL HP HL HM DP BC OL SL MC node V (Wg : Z -> Z),
  zone_ok HP HL HM V -> 2 <= HL -> HL + 2 <= HM -> HM <= 573 ->
  arr_len HP = 573 -> arr_len FC = tsize t -> arr_len DL = tsize t -> arr_len DP = 573 ->
  ~ V node -> 0 <= node < tsize t -> (forall u, V u -> 0 <= u < node) ->
  heap_prop FC DP HP HL 0 ->
  (forall u, V u -> arr_get FC u = Wg u) -> (forall u, 0 <= Wg u) ->
  zsum (fun i => Wg (arr_get HP i)) 1 (Z.to_nat HL) < 2 ^ 16 ->
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
    /\ (forall i, HM <= i < 573 -> arr_get HP i <> n /\ arr_get HP i <> m)
    (* [comment removed for export] *)
    /\ heap_prop (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m)))
                 (arr_set DP node (wrap8 ((if arr_get DP m <=? arr_get DP n then arr_get DP n else arr_get DP m) + 1)))
                 HP4 (HL - 1) 0
    /\ (forall i, 1 <= i <= HL -> lek FC DP n (arr_get HP i))
    /\ (forall i, 1 <= i <= HL -> arr_get HP i <> n -> lek FC DP m (arr_get HP i))
    (* [comment removed for export] *)
    /\ wrap16 (arr_get FC n + arr_get FC m) = Wg n + Wg m
    /\ zsum (fun i => Wg (arr_get HP4 i)) 1 (Z.to_nat (HL - 1)) + Wg n + Wg m
       = zsum (fun i => Wg (arr_get HP i)) 1 (Z.to_nat HL) + Wg node
    (* [comment removed for export] *)
    /\ (forall i, 1 <= i <= HL - 1 -> arr_get HP4 i = node \/ (exists p, 1 <= p <= HL /\ arr_get HP p = arr_get HP4 i /\ arr_get HP4 i <> n /\ arr_get HP4 i <> m))
    /\ (exists pm, 2 <= pm <= HL /\ arr_get HP pm = m)
    /\ (exists pn, 1 <= pn <= HL - 1 /\ arr_get HP4 pn = node /\ forall i, 1 <= i <= HL - 1 -> i <> pn -> arr_get HP4 i <> node).
Proof.
  intros FC DL HP HL HM DP BC OL SL MC node V Wg HZ HHL HHM H573 LHP LFC LDL LDP Nnode Hnode Hlt HORD HWg HWn HS.
  (* [comment removed for export] *)
  set (n := arr_get HP 1).
  pose proof (zone_pop HP HL HM V HZ HHL ltac:(lia) ltac:(lia)) as HZa. fold n in HZa.
  set (HPa := arr_set HP 1 (arr_get HP HL)) in HZa.
  assert (LHPa : arr_len HPa = 573) by (subst HPa; rewrite arr_len_set; exact LHP).
  set (Xa := U FC DL HPa (HL - 1) HM DP BC OL SL MC).
  destruct (pqdownheap_zone Xa t 1 HM (fun u => V u /\ u <> n)) as (Zb & Ob & Lb & Ab & Sb);
    [subst Xa; autorewrite with btupd; first [exact HZa | lia | exact LHPa] ..|].
  subst Xa. autorewrite with btupd in Zb. autorewrite with btupd in Ob. rewrite bt_heap_len in Lb.
  (* [comment removed for export] *)
  assert (ORDa : heap_prop FC DP HPa (HL - 1) 1).
  { intros i Hi Hki. pose proof (div2_facts i ltac:(lia)) as [D1 D2]. subst HPa. rewrite !arr_get_set.
    replace (1 =? i / 2) with false by (symmetry; apply Z.eqb_neq; lia). replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
    apply HORD; lia. }
  pose proof (pqdownheap_order FC DP (U FC DL HPa (HL - 1) HM DP BC OL SL MC) t 1 (bt_tree_fc _ _ _ _ _ _ _ _ _ _ _ _) (bt_depth _ _ _ _ _ _ _ _ _ _ _ _)) as ORDb.
  rewrite bt_heap_len, bt_heap in ORDb. specialize (ORDb ltac:(lia) ltac:(rewrite LHPa; lia) ltac:(lia) ORDa). replace (1 - 1) with 0 in ORDb by lia.
  pose proof (pqdownheap_sum Wg (U FC DL HPa (HL - 1) HM DP BC OL SL MC) t 1) as SUMb.
  rewrite bt_heap_len, bt_heap in SUMb. specialize (SUMb ltac:(lia) ltac:(rewrite LHPa; lia)).
  set (HPb := ds_heap (pqdownheap (U FC DL HPa (HL - 1) HM DP BC OL SL MC) t 1)) in *.
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  assert (Gc : forall i, 2 <= i <= HL - 1 -> arr_get HPc i = arr_get HPb i).
  { intros i Hi. subst HPc. rewrite !arr_get_set. replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (HM - 2 =? i) with false by (symmetry; apply Z.eqb_neq; lia). replace (HM - 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (Gc1 : arr_get HPc 1 = node).
  { subst HPc. rewrite arr_get_set. rewrite Z.eqb_refl. unfold arr_inb. rewrite !arr_len_set. inb_t 1 HPb. reflexivity. }
  assert (Qb : forall i, 1 <= i <= HL - 1 -> V (arr_get HPb i) /\ arr_get HPb i <> n).
  { intros i Hi. exact (zone_ok_mem _ _ _ _ i Zb ltac:(left; lia)). }
  assert (LEK' : forall a b, a <> node -> b <> node -> lek FC DP a b -> lek FC' DP' a b).
  { intros a b Na Nb Hab. unfold lek in *. subst FC' DP'. rewrite !arr_get_set.
    replace (node =? a) with false by (symmetry; apply Z.eqb_neq; congruence). replace (node =? b) with false by (symmetry; apply Z.eqb_neq; congruence). cbn [andb]. exact Hab. }
  assert (ORDc : heap_prop FC' DP' HPc (HL - 1) 1).
  { intros i Hi Hki. pose proof (div2_facts i ltac:(lia)) as [D1 D2]. rewrite !Gc by lia.
    destruct (Qb i ltac:(lia)) as [Vi _]. destruct (Qb (i / 2) ltac:(lia)) as [Vi2 _].
    apply LEK'; [intros X; rewrite X in Vi2; exact (Nnode Vi2) | intros X; rewrite X in Vi; exact (Nnode Vi) |]. apply ORDb; lia. }
  pose proof (pqdownheap_order FC' DP' (U FC' DL' HPc (HL - 1) (HM - 2) DP' BC OL SL MC) t 1 (bt_tree_fc _ _ _ _ _ _ _ _ _ _ _ _) (bt_depth _ _ _ _ _ _ _ _ _ _ _ _)) as ORDd.
  rewrite bt_heap_len, bt_heap in ORDd. specialize (ORDd ltac:(lia) ltac:(rewrite LHPc; lia) ltac:(lia) ORDc). replace (1 - 1) with 0 in ORDd by lia.
  pose proof (pqdownheap_sum Wg (U FC' DL' HPc (HL - 1) (HM - 2) DP' BC OL SL MC) t 1) as SUMd.
  rewrite bt_heap_len, bt_heap in SUMd. specialize (SUMd ltac:(lia) ltac:(rewrite LHPc; lia)).
  set (HPd := ds_heap (pqdownheap (U FC' DL' HPc (HL - 1) (HM - 2) DP' BC OL SL MC) t 1)) in *.
  exists HPd, n, m.
  split; [reflexivity|]. split; [exact Vn|]. split; [exact Vm|]. split; [intros Emn; exact (Nmn (eq_sym Emn))|].
  split.
  { intros f. rewrite loop4_unfold. unfold SMALLEST. cbv zeta. autorewrite with btupd.
    fold n. fold HPa. rewrite Sb. autorewrite with btupd. fold m.
    replace (HM - 1 - 1) with (HM - 2) by lia. fold FC'. fold DP'. fold DL'. fold HPc.
    rewrite Sd. autorewrite with btupd. reflexivity. }
  split.
  { apply (zone_ok_ext _ _ _ (fun u => (V u /\ u <> n) \/ u = n \/ u = node)); [|exact Zd].
    intros u. split.
    - intros [[X _]|[->| ->]]; [left; exact X | left; exact Vn | right; reflexivity].
    - intros [X| ->]; [|right; right; reflexivity]. destruct (Z.eq_dec u n) as [->|]; [right; left; reflexivity | left; split; assumption]. }
  assert (G1 : arr_get HPc (HM - 1) = n).
  { subst HPc. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, Ab.
    replace (1 =? HM - 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (HM - 2 =? HM - 1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
    replace ((0 <=? HM - 1) && (HM - 1 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
  assert (G2 : arr_get HPc (HM - 2) = m).
  { subst HPc. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, Ab.
    replace (1 =? HM - 2) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
    replace ((0 <=? HM - 2) && (HM - 2 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
  split; [rewrite (Od (HM - 1)) by lia; exact G1|].
  split; [rewrite (Od (HM - 2)) by lia; exact G2|].
  assert (Otail : forall i, HM <= i -> arr_get HPd i = arr_get HP i).
  { intros i Hi. rewrite (Od i) by lia. subst HPc. rewrite !arr_get_set.
    replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). replace (HM - 2 =? i) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (HM - 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
    rewrite (Ob i) by lia. subst HPa. rewrite arr_get_set. replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  split; [exact Otail|]. split; [exact Ad|].
  split.
  { intros i Hi. split.
    - intros En. pose proof (zone_ok_inj _ _ _ _ i 1 HZ ltac:(right; lia) ltac:(left; lia) En). lia.
    - intros Em. assert (Ei : arr_get HPb i = arr_get HP i).
      { rewrite (Ob i) by lia. subst HPa. rewrite arr_get_set. replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      rewrite <- Ei in Em. pose proof (zone_ok_inj _ _ _ _ i 1 Zb ltac:(right; lia) ltac:(left; lia) Em). lia. }
  split; [exact ORDd|].
  (* [comment removed for export] *)
  split; [intros i Hi; subst n; apply (heap_root_min FC DP HP HL HORD i Hi)|].
  (* [comment removed for export] *)
  assert (Mm : forall i, 1 <= i <= HL -> arr_get HP i <> n -> lek FC DP m (arr_get HP i)).
  { intros i Hi Nin. pose proof (zone_ok_mem _ _ _ _ i HZ ltac:(left; lia)) as Vi.
    destruct Zb as [posb [Ab' Bb']]. destruct (Bb' (arr_get HP i) (conj Vi Nin)) as [Lp Ep].
    destruct Lp as [Lp|Lp].
    - rewrite <- Ep. subst m. apply (heap_root_min FC DP HPb (HL - 1) ORDb). exact Lp.
    - exfalso. assert (Eo : arr_get HPb (posb (arr_get HP i)) = arr_get HP (posb (arr_get HP i))).
      { rewrite (Ob (posb (arr_get HP i))) by lia. subst HPa. rewrite arr_get_set. replace (1 =? posb (arr_get HP i)) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      rewrite Eo in Ep. pose proof (zone_ok_inj _ _ _ _ (posb (arr_get HP i)) i HZ ltac:(right; lia) ltac:(left; lia) Ep). lia. }
  split; [exact Mm|].
  (* [comment removed for export] *)
  assert (Sa : zsum (fun i => Wg (arr_get HPa i)) 1 (Z.to_nat (HL - 1)) + Wg n = zsum (fun i => Wg (arr_get HP i)) 1 (Z.to_nat HL)).
  { replace (Z.to_nat HL) with (S (Z.to_nat (HL - 1))) by lia. rewrite zsum_snoc. replace (1 + Z.of_nat (Z.to_nat (HL - 1))) with HL by lia.
    rewrite (zsum_balance1 (fun i => Wg (arr_get HPa i)) (fun i => Wg (arr_get HP i) + (if i =? 1 then Wg (arr_get HP HL) - Wg (arr_get HP 1) else 0)) 1 (Z.to_nat (HL - 1)) 1); try lia.
    - rewrite zsum_add. rewrite (zsum_single (fun i => if i =? 1 then Wg (arr_get HP HL) - Wg (arr_get HP 1) else 0) 1 (Z.to_nat (HL - 1)) 1) by (try lia; intros i Hi Ni; replace (i =? 1) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
      rewrite Z.eqb_refl. subst n. lia.
    - intros i Hi Ni. subst HPa. rewrite arr_get_set. replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). replace (i =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. lia.
    - subst HPa. rewrite arr_get_set. unfold arr_inb. rewrite Z.eqb_refl. inb_t 1 HP. cbn [andb]. lia. }
  assert (Sc : zsum (fun i => Wg (arr_get HPc i)) 1 (Z.to_nat (HL - 1)) + Wg m = zsum (fun i => Wg (arr_get HPb i)) 1 (Z.to_nat (HL - 1)) + Wg node).
  { rewrite (zsum_balance1 (fun i => Wg (arr_get HPc i)) (fun i => Wg (arr_get HPb i) + (if i =? 1 then Wg node - Wg m else 0)) 1 (Z.to_nat (HL - 1)) 1); try lia.
    - rewrite zsum_add. rewrite (zsum_single (fun i => if i =? 1 then Wg node - Wg m else 0) 1 (Z.to_nat (HL - 1)) 1) by (try lia; intros i Hi Ni; replace (i =? 1) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
      rewrite Z.eqb_refl. lia.
    - intros i Hi Ni. rewrite Gc by lia. replace (i =? 1) with false by (symmetry; apply Z.eqb_neq; exact Ni). lia.
    - rewrite Gc1, Z.eqb_refl. subst m. lia. }
  (* [comment removed for export] *)
  pose proof HZ as HZ'. destruct HZ' as [pos [A B]]. destruct (A 1 ltac:(left; lia)) as [_ P1]. fold n in P1. destruct (B m Vm) as [Lm Em].
  assert (Pm : 1 <= pos m <= HL).
  { destruct Lm as [Lm|Lm]; [exact Lm | exfalso].
    assert (Eo : arr_get HPb (pos m) = arr_get HP (pos m)).
    { rewrite (Ob (pos m)) by lia. subst HPa. rewrite arr_get_set. replace (1 =? pos m) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    pose proof (zone_ok_inj _ _ _ _ 1 (pos m) Zb ltac:(left; lia) ltac:(right; lia)) as INJ. rewrite Eo, Em in INJ. specialize (INJ eq_refl). lia. }
  assert (Pn : 1 <= pos n <= HL) by (rewrite P1; lia). assert (En : arr_get HP (pos n) = n) by (rewrite P1; reflexivity).
  assert (Npm : pos n <> pos m) by (intros X; apply Nmn; rewrite <- En, <- Em, X; reflexivity).
  assert (NW : wrap16 (arr_get FC n + arr_get FC m) = Wg n + Wg m).
  { rewrite (HWg n Vn), (HWg m Vm). apply wrap16_id.
    assert (PW : forall i, 1 <= i < 1 + Z.of_nat (Z.to_nat HL) -> (if i =? pos n then Wg n else 0) + (if i =? pos m then Wg m else 0) <= Wg (arr_get HP i)).
    { intros i Hi. pose proof (HWn (arr_get HP i)). destruct (Z.eqb_spec i (pos n)) as [E1|N1].
      - subst i. rewrite En. replace (pos n =? pos m) with false by (symmetry; apply Z.eqb_neq; exact Npm). lia.
      - destruct (Z.eqb_spec i (pos m)) as [E2|N2]; [subst i; rewrite Em; lia | lia]. }
    pose proof (zsum_mono _ _ 1 (Z.to_nat HL) PW) as M.
    rewrite zsum_add in M.
    rewrite (zsum_single (fun i => if i =? pos n then Wg n else 0) 1 (Z.to_nat HL) (pos n)) in M by (try lia; intros i Hi Ni; replace (i =? pos n) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
    rewrite (zsum_single (fun i => if i =? pos m then Wg m else 0) 1 (Z.to_nat HL) (pos m)) in M by (try lia; intros i Hi Ni; replace (i =? pos m) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
    rewrite !Z.eqb_refl in M. pose proof (HWn n). pose proof (HWn m). lia. }
  split; [exact NW|].
  split; [rewrite SUMd; lia|].
  split; [| split; [exists (pos m); split; [lia | exact Em] |]].
  2:{ pose proof Zd as Zd'. destruct Zd' as [posd [AdZ BdZ]]. destruct (BdZ node ltac:(right; right; reflexivity)) as [Ln' En'].
      assert (Pn' : 1 <= posd node <= HL - 1).
      { unfold live in Ln'. destruct Ln' as [X|X]; [exact X | exfalso].
        destruct (Z.eq_dec (posd node) (HM - 2)) as [E2|N2]; [rewrite E2, (Od (HM - 2)), G2 in En' by lia; apply Nnode; rewrite <- En'; exact Vm|].
        destruct (Z.eq_dec (posd node) (HM - 1)) as [E1|N1]; [rewrite E1, (Od (HM - 1)), G1 in En' by lia; apply Nnode; rewrite <- En'; exact Vn|].
        rewrite (Otail (posd node)) in En' by lia. apply Nnode. rewrite <- En'. apply (zone_ok_mem _ _ _ _ (posd node) HZ). right; lia. }
      exists (posd node). split; [exact Pn'|]. split; [exact En'|].
      intros i Hi Ni X. destruct (AdZ i ltac:(left; lia)) as [_ Pi]. rewrite X in Pi. lia. }
  (* [comment removed for export] *)
  intros i Hi. pose proof (zone_ok_mem _ _ _ _ i Zd ltac:(left; lia)) as Vi.
  destruct (Z.eq_dec (arr_get HPd i) node) as [Eno|Nno]; [left; exact Eno | right].
  assert (Vi' : V (arr_get HPd i)) by (destruct Vi as [[X _]|[X|X]]; [exact X | rewrite X; exact Vn | congruence]).
  destruct (B _ Vi') as [Lp Ep].
  destruct Lp as [Lp|Lp].
  - exists (pos (arr_get HPd i)). split; [exact Lp|]. split; [exact Ep|].
    split; [| intros X].
    + intros X. pose proof (zone_ok_inj _ _ _ _ i (HM - 1) Zd ltac:(left; lia) ltac:(right; lia)) as IJ. rewrite (Od (HM - 1)), G1 in IJ by lia. specialize (IJ X). lia.
    + pose proof (zone_ok_inj _ _ _ _ i (HM - 2) Zd ltac:(left; lia) ltac:(right; lia)) as IJ. rewrite (Od (HM - 2)), G2 in IJ by lia. specialize (IJ X). lia.
  - exfalso. pose proof (zone_ok_inj _ _ _ _ i (pos (arr_get HPd i)) Zd ltac:(left; lia) ltac:(right; lia)) as INJ.
    rewrite (Otail (pos (arr_get HPd i))) in INJ by lia. specialize (INJ (eq_sym Ep)). lia.
Qed.
End Loop4o.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zone_sum : forall HP hl V (Vb : Z -> bool) (f : Z -> Z) B,
  zone_ok HP hl 573 V -> 0 <= hl -> (forall u, V u <-> Vb u = true) -> (forall u, V u -> 0 <= u < B) ->
  (forall u, 0 <= u < B -> Vb u = false -> f u = 0) ->
  zsum (fun i => f (arr_get HP i)) 1 (Z.to_nat hl) = zsum f 0 (Z.to_nat B).
Proof.
  intros HP hl V Vb f B HZ Hhl HVb HB Hf. pose proof HZ as [pos [A Bz]].
  assert (MEM : forall i, 1 <= i <= hl -> V (arr_get HP i) /\ pos (arr_get HP i) = i) by (intros i Hi; apply A; left; lia).
  transitivity (zsum (fun i => zsum (fun u => zind (u =? arr_get HP i) * f u) 0 (Z.to_nat B)) 1 (Z.to_nat hl)).
  - apply zsum_ext. intros i Hi. destruct (MEM i ltac:(lia)) as [Vi _]. pose proof (HB _ Vi).
    rewrite (zsum_single (fun u => zind (u =? arr_get HP i) * f u) 0 (Z.to_nat B) (arr_get HP i)); [| lia |].
    + rewrite Z.eqb_refl. cbn [zind]. lia.
    + intros u Hu Nu. replace (u =? arr_get HP i) with false by (symmetry; apply Z.eqb_neq; exact Nu). reflexivity.
  - rewrite (zsum_swap (fun i u => zind (u =? arr_get HP i) * f u)). apply zsum_ext. intros u Hu.
    transitivity (zsum (fun i => zind (u =? arr_get HP i)) 1 (Z.to_nat hl) * f u).
    { rewrite Z.mul_comm, <- zsum_scale. apply zsum_ext. intros; lia. }
    destruct (Vb u) eqn:EV.
    + assert (Vu : V u) by (apply HVb; exact EV). destruct (Bz u Vu) as [Lu Eu]. unfold live in Lu.
      assert (Pu : 1 <= pos u <= hl) by lia.
      rewrite (zsum_single (fun i => zind (u =? arr_get HP i)) 1 (Z.to_nat hl) (pos u)); [| lia |].
      * rewrite Eu, Z.eqb_refl. cbn [zind]. lia.
      * intros i Hi Ni. destruct (Z.eqb_spec u (arr_get HP i)) as [Eq|Nq]; [|reflexivity]. exfalso.
        destruct (MEM i ltac:(lia)) as [_ Pi]. rewrite <- Eq in Pi. lia.
    + rewrite (Hf u ltac:(lia) EV). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WholeLoopO.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation U := (bt_upd s t).
Local Notation E := (sd_elems t).
Variable FC2 : arr.
Variable DL2 : arr.
Variable L : Z.
Variable BC : arr.
Variable OL : Z.
Variable SL : Z.
Variable MC : Z.
Let V0 : Z -> Prop := Vscan FC2 E.
Let Vj (j : Z) : Z -> Prop := fun u => V0 u \/ (E <= u < E + j).

(* [comment removed for export] *)
Variable Wtot : Z.
Hypothesis HWtot : Wtot < 2 ^ 16.

Record INV4o (j : Z) (FCj DLj HPj DPj : arr) (Wg : Z -> Z) : Prop := {
  io_inv : INV4 t FC2 DL2 L j FCj DLj HPj DPj;
  io_ord : heap_prop FCj DPj HPj (L - j) 0;
  io_wgl : forall u, 0 <= u < E -> Wg u = arr_get FC2 u;
  io_wgf : forall u, Vj j u -> arr_get FCj u = Wg u;
  io_wgn : forall u, 0 <= Wg u;
  io_sum : zsum (fun i => Wg (arr_get HPj i)) 1 (Z.to_nat (L - j)) <= Wtot;
  io_node : forall k, 1 <= k <= j -> Wg (E + k - 1) = Wg (arr_get HPj (574 - 2 * k)) + Wg (arr_get HPj (573 - 2 * k));
  io_greedy : forall k, 1 <= k <= j ->
      Wg (arr_get HPj (574 - 2 * k)) <= Wg (arr_get HPj (573 - 2 * k))
      /\ (forall i, 1 <= i <= L - j -> arr_get HPj i < E + k - 1 ->
            Wg (arr_get HPj (574 - 2 * k)) <= Wg (arr_get HPj i) /\ Wg (arr_get HPj (573 - 2 * k)) <= Wg (arr_get HPj i))
      /\ (forall a, 573 - 2 * j <= a < 573 - 2 * k -> arr_get HPj a < E + k - 1 ->
            Wg (arr_get HPj (574 - 2 * k)) <= Wg (arr_get HPj a) /\ Wg (arr_get HPj (573 - 2 * k)) <= Wg (arr_get HPj a)) }.

Hypothesis HL : 2 <= L <= E.

Lemma loop4o_inv_step : forall j FCj DLj HPj DPj Wg,
  0 <= j -> 2 <= L - j -> INV4o j FCj DLj HPj DPj Wg ->
  exists FC' DL' HP' DP' Wg',
    (forall f, build_tree_loop4 (S f) (U FCj DLj HPj (L - j) (573 - 2 * j) DPj BC OL SL MC) t (E + j)
       = let s4 := U FC' DL' HP' (L - (j + 1)) (573 - 2 * (j + 1)) DP' BC OL SL MC in
         if 2 <=? L - (j + 1) then build_tree_loop4 f s4 t (E + (j + 1)) else s4)
    /\ INV4o (j + 1) FC' DL' HP' DP' Wg'.
Proof.
  intros j FCj DLj HPj DPj Wg Hj Hr INV. pose proof (elems_range t) as HE.
  destruct INV as [INVb ORD WGL WGF WGN SUM NODE GR]. pose proof INVb as [Z0 D0 O0 F0 L0 LHP LFC LDL LDP RFC RDP RDL].
  destruct (round_o s t FCj DLj HPj (L - j) (573 - 2 * j) DPj BC OL SL MC (E + j) (Vj j) Wg Z0
              ltac:(lia) ltac:(lia) ltac:(lia) LHP LFC LDL LDP
              ltac:(unfold Vj, V0, Vscan; lia) ltac:(lia) ltac:(unfold Vj, V0, Vscan; intros u Hu; lia)
              ORD WGF WGN ltac:(lia))
    as (HP4 & n & m & En & Vn & Vm & Nnm & EQ & Z4 & G1 & G2 & O4 & L4 & D4 & ORD4 & MINn & MINm & NW & SUM4 & PROV & (pm & Hpm & Epm) & (pn & Hpn & Epn & Upn)).
  set (Wg' := fun u => if u =? E + j then Wg n + Wg m else Wg u).
  exists (arr_set FCj (E + j) (wrap16 (arr_get FCj n + arr_get FCj m))),
         (arr_set (arr_set DLj m (wrap16 (E + j))) n (wrap16 (E + j))), HP4,
         (arr_set DPj (E + j) (wrap8 ((if arr_get DPj m <=? arr_get DPj n then arr_get DPj n else arr_get DPj m) + 1))), Wg'.
  split.
  { intros f. rewrite (EQ f). replace (L - j - 1) with (L - (j + 1)) by lia.
    replace (573 - 2 * j - 2) with (573 - 2 * (j + 1)) by lia. replace (E + j + 1) with (E + (j + 1)) by lia. reflexivity. }
  assert (Vlt : forall u, Vj j u -> 0 <= u < E + j) by (unfold Vj, V0, Vscan; intros u Hu; lia).
  pose proof (Vlt n Vn) as Rn. pose proof (Vlt m Vm) as Rm.
  assert (WgE : forall u, u <> E + j -> Wg' u = Wg u) by (intros u Hu; subst Wg'; cbv beta; replace (u =? E + j) with false by (symmetry; apply Z.eqb_neq; exact Hu); reflexivity).
  assert (WgN : Wg' (E + j) = Wg n + Wg m) by (subst Wg'; cbv beta; rewrite Z.eqb_refl; reflexivity).
  assert (W16 : wrap16 (E + j) = E + j) by (apply wrap16_id; lia).
  assert (INV'' : INV4 t FC2 DL2 L (j + 1) (arr_set FCj (E + j) (wrap16 (arr_get FCj n + arr_get FCj m)))
                    (arr_set (arr_set DLj m (wrap16 (E + j))) n (wrap16 (E + j))) HP4
                    (arr_set DPj (E + j) (wrap8 ((if arr_get DPj m <=? arr_get DPj n then arr_get DPj n else arr_get DPj m) + 1)))).
  { constructor.
  - replace (L - (j + 1)) with (L - j - 1) by lia. replace (573 - 2 * (j + 1)) with (573 - 2 * j - 2) by lia.
    apply (zone_ok_ext _ _ _ (fun u => Vj j u \/ u = E + j)); [|exact Z4].
    unfold Vj, RefDeflSafeB2.Vj, RefDeflSafeB2.V0. intros u. split; intros HH.
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
  - intros i. rewrite !arr_get_set. destruct (_ && _); [apply wrap16_range|]. destruct (_ && _); [apply wrap16_range | apply RDL]. }
  constructor; [exact INV'' | replace (L - (j + 1)) with (L - j - 1) by lia; exact ORD4 | | | | | |].
  all: try (intros u Hu; rewrite WgE by lia; apply WGL; exact Hu).
  all: try (intros u; subst Wg'; cbv beta; destruct (u =? E + j); [pose proof (WGN n); pose proof (WGN m); lia | apply WGN]).
  all: try (intros u Hu; rewrite arr_get_set; unfold arr_inb; rewrite LFC; destruct (Z.eqb_spec (E + j) u) as [<-|Nu];
            [replace ((0 <=? E + j) && (E + j <? tsize t)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia); cbn [andb]; rewrite WgN; exact NW
            | cbn [andb]; rewrite WgE by exact (not_eq_sym Nu); apply WGF; unfold Vj in Hu |- *; destruct Hu as [A|A]; [left; exact A | right; lia]]).
  (* [comment removed for export] *)
  all: assert (SUMQ : zsum (fun i => Wg' (arr_get HP4 i)) 1 (Z.to_nat (L - j - 1)) = zsum (fun i => Wg (arr_get HPj i)) 1 (Z.to_nat (L - j)))
    by (rewrite (zsum_ext (fun i => Wg' (arr_get HP4 i)) (fun i => Wg (arr_get HP4 i) + (if i =? pn then Wg n + Wg m - Wg (E + j) else 0))) by
          (intros i Hi; destruct (Z.eqb_spec i pn) as [->|Ni]; [rewrite Epn, WgN; lia | rewrite WgE by (apply Upn; lia); lia]);
        rewrite zsum_add; rewrite (zsum_single (fun i => if i =? pn then Wg n + Wg m - Wg (E + j) else 0) 1 (Z.to_nat (L - j - 1)) pn) by
          (try lia; intros i Hi Ni; replace (i =? pn) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity);
        rewrite Z.eqb_refl; lia).
  all: assert (Wq : forall u, Vj j u -> Wg' u = Wg u) by (intros u Hu; apply WgE; pose proof (Vlt u Hu); lia).
  all: assert (Wn : Wg' n = Wg n) by (apply Wq; exact Vn).
  all: assert (Wm : Wg' m = Wg m) by (apply Wq; exact Vm).
  all: assert (Hnm : Wg n <= Wg m) by (pose proof (MINn pm ltac:(lia)) as X; rewrite Epm in X; apply lek_freq in X; rewrite (WGF n Vn), (WGF m Vm) in X; exact X).
  - replace (L - (j + 1)) with (L - j - 1) by lia. rewrite SUMQ. exact SUM.
  - intros k Hk. destruct (Z.eq_dec k (j + 1)) as [->|Nk].
    + replace (E + (j + 1) - 1) with (E + j) by lia. replace (574 - 2 * (j + 1)) with (573 - 2 * j - 1) by lia. replace (573 - 2 * (j + 1)) with (573 - 2 * j - 2) by lia.
      rewrite G1, G2, WgN, Wn, Wm. reflexivity.
    + rewrite !O4 by lia. pose proof (zone_ok_mem _ _ _ _ (574 - 2 * k) Z0 ltac:(right; lia)) as V1. pose proof (zone_ok_mem _ _ _ _ (573 - 2 * k) Z0 ltac:(right; lia)) as V2.
      rewrite (Wq _ V1), (Wq _ V2), WgE by lia. apply NODE. lia.
  - intros k Hk. destruct (Z.eq_dec k (j + 1)) as [->|Nk].
    + replace (E + (j + 1) - 1) with (E + j) by lia. replace (574 - 2 * (j + 1)) with (573 - 2 * j - 1) by lia. replace (573 - 2 * (j + 1)) with (573 - 2 * j - 2) by lia.
      rewrite G1, G2, Wn, Wm. split; [exact Hnm|]. split.
      * intros i Hi Hlt'. destruct (PROV i ltac:(lia)) as [Eq|(p & Hp & Ep & Nn' & Nm')]; [exfalso; lia|].
        rewrite <- Ep in *. rewrite (Wq (arr_get HPj p)) by (apply (zone_ok_mem _ _ _ _ p Z0); left; lia).
        pose proof (MINn p Hp) as X1. pose proof (MINm p Hp ltac:(congruence)) as X2. apply lek_freq in X1. apply lek_freq in X2.
        rewrite (WGF n Vn) in X1. rewrite (WGF m Vm) in X2. rewrite (WGF (arr_get HPj p)) in X1, X2 by (apply (zone_ok_mem _ _ _ _ p Z0); left; lia). lia.
      * intros a Ha. exfalso. lia.
    + destruct (GR k ltac:(lia)) as (Ga & Gb & Gc). rewrite !(O4 (574 - 2 * k)), !(O4 (573 - 2 * k)) by lia.
      pose proof (zone_ok_mem _ _ _ _ (574 - 2 * k) Z0 ltac:(right; lia)) as V1. pose proof (zone_ok_mem _ _ _ _ (573 - 2 * k) Z0 ltac:(right; lia)) as V2.
      rewrite (Wq _ V1), (Wq _ V2). split; [exact Ga|]. split.
      * intros i Hi Hlt'. destruct (PROV i ltac:(lia)) as [Eq|(p & Hp & Ep & Nn' & Nm')]; [exfalso; lia|].
        rewrite <- Ep in *. rewrite (Wq (arr_get HPj p)) by (apply (zone_ok_mem _ _ _ _ p Z0); left; lia). apply Gb; [lia | exact Hlt'].
      * intros a Ha Hlt'. destruct (Z_lt_le_dec a (573 - 2 * j)) as [Anew|Aold].
        -- (* [comment removed for export] *)
           assert (Ha2 : a = 573 - 2 * j - 1 \/ a = 573 - 2 * j - 2) by lia.
           destruct Ha2 as [-> | ->]; [rewrite G1 in Hlt' |- *; rewrite Wn | rewrite G2 in Hlt' |- *; rewrite Wm].
           ++ rewrite En in Hlt' |- *. apply Gb; [lia | exact Hlt'].
           ++ rewrite <- Epm in Hlt' |- *. apply Gb; [lia | exact Hlt'].
        -- rewrite (O4 a) in Hlt' |- * by lia. rewrite (Wq (arr_get HPj a)) by (apply (zone_ok_mem _ _ _ _ a Z0); right; lia). apply Gc; [lia | exact Hlt'].
Qed.

Lemma loop4o_spec : forall f j FCj DLj HPj DPj Wg,
  0 <= j -> 2 <= L - j -> (Z.of_nat f >= L - j - 1) -> INV4o j FCj DLj HPj DPj Wg ->
  exists FC' DL' HP' DP' Wg',
    build_tree_loop4 f (U FCj DLj HPj (L - j) (573 - 2 * j) DPj BC OL SL MC) t (E + j)
    = U FC' DL' HP' 1 (573 - 2 * (L - 1)) DP' BC OL SL MC
    /\ INV4o (L - 1) FC' DL' HP' DP' Wg'.
Proof.
  induction f as [|f IH]; intros j FCj DLj HPj DPj Wg Hj Hr Hf INV; [lia|].
  destruct (loop4o_inv_step j FCj DLj HPj DPj Wg Hj Hr INV) as (FC' & DL' & HP' & DP' & Wg' & EQ & INV').
  rewrite (EQ f). cbv zeta.
  destruct (Z.leb_spec 2 (L - (j + 1))) as [C|C].
  - apply (IH (j + 1) _ _ _ _ Wg'); [lia | lia | lia | exact INV'].
  - exists FC', DL', HP', DP', Wg'. replace (L - 1) with (j + 1) by lia. split; [| exact INV'].
    replace (L - (j + 1)) with 1 by lia. reflexivity.
Qed.
End WholeLoopO.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record greedy_facts (t : tree_id) (FC2 : arr) (L : Z) (FCf HPf : arr) (Wg : Z -> Z) : Prop := {
  gf_wleaf : forall u, 0 <= u < sd_elems t -> Wg u = arr_get FC2 u;
  gf_wfc : forall u, (Vscan FC2 (sd_elems t) u \/ sd_elems t <= u < sd_elems t + (L - 1)) -> arr_get FCf u = Wg u;
  gf_wnn : forall u, 0 <= Wg u;
  gf_node : forall k, 1 <= k <= L - 1 -> Wg (sd_elems t + k - 1) = Wg (arr_get HPf (574 - 2 * k)) + Wg (arr_get HPf (573 - 2 * k));
  gf_nm : forall k, 1 <= k <= L - 1 -> Wg (arr_get HPf (574 - 2 * k)) <= Wg (arr_get HPf (573 - 2 * k));
  gf_min : forall k a, 1 <= k <= L - 1 -> 574 - 2 * L <= a < 573 - 2 * k -> arr_get HPf a < sd_elems t + k - 1 ->
             Wg (arr_get HPf (574 - 2 * k)) <= Wg (arr_get HPf a) /\ Wg (arr_get HPf (573 - 2 * k)) <= Wg (arr_get HPf a) }.

(* [comment removed for export] *)
Lemma zsum_existsb_le : forall (Fl : list Z) lo n, zsum (fun u => zind (existsb (Z.eqb u) Fl)) lo n <= Z.of_nat (length Fl).
Proof.
  induction Fl as [|a l IH]; intros lo n; cbn [existsb length].
  - rewrite zsum_0 by (intros; reflexivity). lia.
  - pose proof (zsum_mono (fun u => zind ((u =? a) || existsb (Z.eqb u) l)) (fun u => zind (u =? a) + zind (existsb (Z.eqb u) l)) lo n
                 ltac:(intros u Hu; cbv beta; destruct (u =? a), (existsb (Z.eqb u) l); cbn; lia)) as M.
    rewrite zsum_add in M. specialize (IH lo n).
    assert (zsum (fun u => zind (u =? a)) lo n <= 1).
    { destruct (Z_lt_le_dec a lo) as [C|C]; [| destruct (Z_lt_le_dec a (lo + Z.of_nat n)) as [C'|C']].
      - rewrite zsum_0; [lia|]. intros u Hu. replace (u =? a) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      - rewrite (zsum_single _ lo n a); [rewrite Z.eqb_refl; cbn; lia | lia |]. intros u Hu Nu. replace (u =? a) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      - rewrite zsum_0; [lia|]. intros u Hu. replace (u =? a) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    lia.
Qed.

Section HeapPhaseO.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation U := (bt_upd s t).
Local Notation E := (sd_elems t).

Theorem heap_phase_o : forall (FC : arr) (BC : arr) (OL SL MC : Z) (Fl : list Z) (DL2 HP2 DP2 : arr) (L : Z) (FCf DLf HPf DPf : arr),
  let FC2 := fc_forced Fl FC in
  let s3 := U FC2 DL2 HP2 L 573 DP2 BC (ol_forced Fl OL) (sl_forced t Fl SL) MC in
  let s4 := build_tree_loop3 (Z.to_nat (ds_heap_len s3 / 2)) s3 t (ds_heap_len s3 / 2) in
  let s5 := build_tree_loop4 573%nat s4 t E in
  let s6 := set_heap_max s5 (ds_heap_max s5 - 1) in
  let s7 := heap_set s6 (ds_heap_max s6) (heap_get s6 SMALLEST) in
  s7 = U FCf DLf HPf 1 (574 - 2 * L) DPf BC (ol_forced Fl OL) (sl_forced t Fl SL) MC ->
  2 <= L <= E -> zone_ok HP2 L 573 (Vscan FC2 E) -> arr_len HP2 = 573 -> arr_len DP2 = 573 -> arr_len DL2 = tsize t -> arr_len FC = tsize t ->
  (forall i, 0 <= arr_get DP2 i < 256) -> (forall i, 0 <= arr_get FC2 i < 65536) -> (forall i, 0 <= arr_get DL2 i < 65536) ->
  (length Fl <= 2)%nat -> (forall i, arr_get FC2 i = if existsb (Z.eqb i) Fl then 1 else arr_get FC i) ->
  (forall i, 0 <= arr_get FC i) -> zsum (fun u => arr_get FC u) 0 (Z.to_nat E) + 2 < 2 ^ 16 ->
  exists Wg, greedy_facts t FC2 L FCf HPf Wg.
Proof.
  intros FC BC OL SL MC Fl DL2 HP2 DP2 L FCf DLf HPf DPf. cbv zeta. intros E7 HL Z2 LHP2 LDP2 LDL2 LFC RDP2 RFC2 RDL2 LF FCE RFC WB.
  pose proof (elems_range t) as HE. rewrite bt_heap_len in E7.
  assert (LFC2 : arr_len (fc_forced Fl FC) = tsize t).
  { unfold fc_forced. clear - LFC. revert FC LFC. induction Fl as [|a l IH]; intros FC LFC; cbn [fold_left]; [exact LFC|]. apply IH. rewrite arr_len_set. exact LFC. }
  set (FC2 := fc_forced Fl FC) in *.
  (* [comment removed for export] *)
  assert (HL2h : 0 <= L / 2 <= L) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  destruct (loop3_spec s t (Z.to_nat (L / 2)) (L / 2) FC2 DL2 HP2 L 573 DP2 BC (ol_forced Fl OL) (sl_forced t Fl SL) MC (Vscan FC2 E) HL2h ltac:(lia) ltac:(lia) LHP2 Z2)
    as (HP3 & E3 & Z3 & LHP3 & HPE3).
  pose proof (loop3_order s t (Z.to_nat (L / 2)) (L / 2) FC2 DL2 HP2 L 573 DP2 BC (ol_forced Fl OL) (sl_forced t Fl SL) MC
                ltac:(lia) ltac:(lia) ltac:(lia) LHP2 (heap_prop_vacuous FC2 DP2 HP2 L (L / 2) ltac:(lia) ltac:(lia))) as ORD3.
  rewrite E3, bt_heap in ORD3. rewrite E3 in E7.
  (* [comment removed for export] *)
  set (Wtot := zsum (fun u => arr_get FC2 u) 0 (Z.to_nat E)).
  assert (WT : Wtot < 2 ^ 16).
  { subst Wtot. pose proof (zsum_mono (fun u => arr_get FC2 u) (fun u => arr_get FC u + zind (existsb (Z.eqb u) Fl)) 0 (Z.to_nat E)
                  ltac:(intros u Hu; cbv beta; rewrite FCE; pose proof (RFC u); destruct (existsb (Z.eqb u) Fl); cbn [zind]; lia)) as M.
    rewrite zsum_add in M. pose proof (zsum_existsb_le Fl 0 (Z.to_nat E)) as X.
    change (zsum (arr_get FC) 0 (Z.to_nat E)) with (zsum (fun u => arr_get FC u) 0 (Z.to_nat E)) in M.
    change (zsum (fun i : Z => zind (existsb (Z.eqb i) Fl)) 0 (Z.to_nat E)) with (zsum (fun u : Z => zind (existsb (Z.eqb u) Fl)) 0 (Z.to_nat E)) in M. lia. }
  (* [comment removed for export] *)
  assert (DPR2' : forall i, 0 <= arr_get DP2 i < 256) by exact RDP2.
  assert (SUM0 : zsum (fun i => arr_get FC2 (arr_get HP3 i)) 1 (Z.to_nat L) = Wtot).
  { subst Wtot. apply (zone_sum HP3 L (Vscan FC2 E) (fun u => (0 <=? u) && (u <? E) && negb (arr_get FC2 u =? 0)) (fun u => arr_get FC2 u) E Z3 ltac:(lia)).
    - intros u. unfold Vscan. rewrite !Bool.andb_true_iff, Bool.negb_true_iff, Z.leb_le, Z.ltb_lt, Z.eqb_neq. tauto.
    - unfold Vscan. intros u Hu. lia.
    - intros u Hu Hb. rewrite !Bool.andb_false_iff, Bool.negb_false_iff, Z.leb_gt, Z.ltb_ge, Z.eqb_eq in Hb. lia. }
  assert (INV0 : INV4o t FC2 DL2 L Wtot 0 FC2 DL2 HP3 DP2 (fun u => arr_get FC2 u)).
  { constructor.
    - constructor; try assumption; try (intros; lia); try (intros; reflexivity).
      replace (L - 0) with L by lia. replace (573 - 2 * 0) with 573 by lia.
      apply (zone_ok_ext _ _ _ (Vscan FC2 E)); [|exact Z3]. unfold RefDeflSafeB2.Vj, RefDeflSafeB2.V0. intros u. split; [intros A; left; exact A | intros [A|A]; [exact A | lia]].
    - replace (L - 0) with L by lia. exact ORD3.
    - intros; reflexivity.
    - intros; reflexivity.
    - intros u. pose proof (RFC2 u). lia.
    - replace (L - 0) with L by lia. rewrite SUM0. lia.
    - intros; lia.
    - intros; lia. }
  destruct (loop4o_spec s t FC2 DL2 L BC (ol_forced Fl OL) (sl_forced t Fl SL) MC Wtot WT HL 573 0 FC2 DL2 HP3 DP2 (fun u => arr_get FC2 u)
              ltac:(lia) ltac:(lia) ltac:(lia) INV0) as (FC' & DL' & HP' & DP' & Wg & E4 & INVf).
  replace (L - 0) with L in E4 by lia. replace (573 - 2 * 0) with 573 in E4 by lia. replace (E + 0) with E in E4 by lia.
  rewrite E4 in E7. autorewrite with btupd in E7. unfold SMALLEST in E7.
  pose proof (f_equal (fun x => tree_fc x t) E7) as Efc. cbv beta in Efc. rewrite !bt_tree_fc in Efc.
  pose proof (f_equal ds_heap E7) as Ehp. cbv beta in Ehp. rewrite !bt_heap in Ehp.
  destruct INVf as [INVb ORD WGL WGF WGN SUM NODE GR].
  assert (Gtail : forall a, 574 - 2 * L < a -> arr_get HPf a = arr_get HP' a).
  { intros a Ha. rewrite <- Ehp. rewrite arr_get_set. replace (573 - 2 * (L - 1) - 1 =? a) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  exists Wg. constructor.
  - exact WGL.
  - intros u Hu. rewrite <- Efc. apply WGF. exact Hu.
  - exact WGN.
  - intros k Hk. rewrite (Gtail (574 - 2 * k)), (Gtail (573 - 2 * k)) by lia. apply NODE. exact Hk.
  - intros k Hk. rewrite (Gtail (574 - 2 * k)), (Gtail (573 - 2 * k)) by lia. exact (proj1 (GR k Hk)).
  - intros k a Hk Ha Hlt. rewrite (Gtail (574 - 2 * k)), (Gtail (573 - 2 * k)) by lia.
    destruct (Z.eq_dec a (574 - 2 * L)) as [->|Na].
    + (* [comment removed for export] *) exfalso. rewrite <- Ehp, arr_get_set in Hlt. replace (573 - 2 * (L - 1) - 1) with (574 - 2 * L) in Hlt by lia.
      rewrite Z.eqb_refl in Hlt. unfold arr_inb in Hlt. rewrite (i4_lhp _ _ _ _ _ _ _ _ _ INVb) in Hlt.
      replace ((0 <=? 574 - 2 * L) && (574 - 2 * L <? 573)) with true in Hlt by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). cbn [andb] in Hlt.
      (* [comment removed for export] *)
      pose proof (i4_zone _ _ _ _ _ _ _ _ _ INVb) as Zf. destruct Zf as [pos [A B]].
      destruct (B (E + L - 2) ltac:(unfold RefDeflSafeB2.Vj; right; lia)) as [Lr Er]. unfold live in Lr.
      destruct Lr as [Lr|Lr]; [replace (pos (E + L - 2)) with 1 in Er by lia; rewrite Er in Hlt; lia|].
      pose proof (i4_old _ _ _ _ _ _ _ _ _ INVb (pos (E + L - 2)) ltac:(lia) ltac:(rewrite Er; lia)) as X. rewrite Er in X.
      assert ((572 - pos (E + L - 2)) / 2 < L - 1) by (apply Z.div_lt_upper_bound; lia). lia.
    + rewrite (Gtail a) in Hlt |- * by lia. apply (proj2 (proj2 (GR k Hk))); [lia | exact Hlt].
Qed.
End HeapPhaseO.
