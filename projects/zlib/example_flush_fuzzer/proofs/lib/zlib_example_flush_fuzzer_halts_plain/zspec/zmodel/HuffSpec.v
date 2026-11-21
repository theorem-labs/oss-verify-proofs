(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffFib HuffHeap HuffBuild HuffBuild2 HuffGen HuffGen2 HuffPen.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import TreeModel BuildTreeModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma gen_codes_loop2_flat : forall f s t FC DL HP HL HM DP BC OL SL MC nc mc n,
  exists FC', gen_codes_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc n
              = bt_upd s t FC' DL HP HL HM DP BC OL SL MC /\ arr_len FC' = arr_len FC.
Proof.
  induction f as [|f IH]; intros; [eexists; split; reflexivity|].
  cbn [gen_codes_loop2]. autorewrite with btupd.
  destruct (n <=? mc); [|eexists; split; reflexivity].
  destruct (arr_get DL n =? 0); [apply IH|].
  unfold set_Code. autorewrite with btupd.
  destruct (IH s t (arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) DL HP HL HM DP BC OL SL MC
               (arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1))) mc (n + 1)) as (FC' & E & L).
  exists FC'. split; [exact E|]. rewrite L. apply arr_len_set.
Qed.

Lemma gen_codes_flat : forall s t FC DL HP HL HM DP BC OL SL MC mc,
  exists FC', gen_codes (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t mc = bt_upd s t FC' DL HP HL HM DP BC OL SL MC
              /\ arr_len FC' = arr_len FC.
Proof. intros. unfold gen_codes. autorewrite with btupd. apply gen_codes_loop2_flat. Qed.


Definition bt_U (s : deflate_state) (t : tree_id) : list Z := UP (tree_fc s t) t.
Definition bt_F (s : deflate_state) (t : tree_id) (j : Z) : Z := FP (tree_fc s t) t j.
Definition bt_mc (s : deflate_state) (t : tree_id) : Z := MCP (tree_fc s t) t.
Definition bt_npad (s : deflate_state) (t : tree_id) : Z := zlen (pads (tree_fc s t) t).
Definition bt_slpad (s : deflate_state) (t : tree_id) : Z := sl_pad t (tree_fc s t).
Definition bt_Ftot (s : deflate_state) (t : tree_id) : Z := Ftot t (tree_fc s t).

Definition bt_pen (U : list Z) (F : Z -> Z) (ML : Z) (L Lz : Z -> Z) (BCz : Z -> Z) : Prop :=
  exists (L' : Z -> Z) (bstar : Z),
       Permutation (map L' U) (map L U)
    /\ zsum (map (fun j => F j * L' j) U) = zsum (map (fun j => F j * L j) U)
    /\ (forall H c, dep_ok H c -> kraft H c <= 2 ^ H -> (forall e, In e c -> 0 <= ew e) ->
          Permutation (map ew c) (map F U) -> zsum (map (fun j => F j * L' j) U) <= ccost c)
    /\ (forall i j, In i U -> In j U -> F i < F j -> L' j <= L' i)
    /\ (forall j, In j U -> 1 <= L' j <= zlen U - 1)
    /\ 1 <= bstar <= ML
    /\ (forall j, In j U -> (L' j < bstar -> Lz j = L' j) /\ (Lz j = L' j \/ (bstar + 1 <= Lz j <= ML /\ bstar <= L' j)))
    /\ (exists BCc, arr_len BCc = 16
          /\ (forall b, 0 <= b <= 15 -> arr_get BCc b = zsum (map (fun j => if Z.min (L j) ML =? b then 1 else 0) U))
          /\ 0 <= zsum (map (fun j => 2 ^ (ML - Z.min (L j) ML)) U) - 2 ^ ML
          /\ (forall b, 0 <= b <= 15 -> BCz b = arr_get (arepair (Z.to_nat (zsum (map (fun j => 2 ^ (ML - Z.min (L j) ML)) U) - 2 ^ ML)) ML BCc) b))
    /\ ((exists j, In j U /\ ML < L j) ->
          bstar <= ML - 1 /\ 2 ^ (ML - bstar) <= zlen U - 2
          /\ exists RL, Permutation RL U /\ noninc (map F RL) /\ nondec (map L' RL)
                        /\ map Lz RL = lens_asc BCz ML)
    /\ zsum (map (fun j => 2 ^ (zlen U - L' j)) U) <= 2 ^ (zlen U)
    /\ (ML = 15 -> zsum (map (fun j => F j * Z.max 0 (Lz j - L' j)) U) <= zsum (map F U))
    /\ zsum (map (fun j => 2 ^ (zlen U - L' j)) U) = 2 ^ (zlen U)
    /\ ((exists j, In j U /\ ML < L j) ->
          exists RL, Permutation RL U /\ noninc (map F RL) /\ nondec (map L' RL)
            /\ (forall r, (r < length RL)%nat ->
                  fibZ (nth r (map L' RL) 0 + 1) * nth r (map F RL) 0 + fibZ (nth r (map L' RL) 0) <= zsum (map F U))
            /\ map Lz RL = lens_asc (arr_get (arepair (Z.to_nat (zsum (map (fun x => 2 ^ (ML - x)) (map (fun x => Z.min x ML) (map L' RL))) - 2 ^ ML)) ML
                                             (bc_of (map (fun x => Z.min x ML) (map L' RL))))) ML).

Record bt_pre (s : deflate_state) (t : tree_id) : Prop := BT_PRE {
  bp_lens : tree_lens s;
  bp_freq : forall j, 0 <= j < sd_elems t -> 0 <= Freq s t j;
  bp_tot : bt_Ftot s t < 2 ^ 16;
  bp_ol : 0 <= ds_opt_len s < 2 ^ 64;
  bp_sl : 0 <= ds_static_len s < 2 ^ 64 }.

Lemma bt_U_facts : forall s t,
  NoDup (bt_U s t)
  /\ (forall j, In j (bt_U s t) -> 0 <= j < sd_elems t /\ j <= bt_mc s t)
  /\ In (bt_mc s t) (bt_U s t)
  /\ 2 <= zlen (bt_U s t)
  /\ (forall j, 0 <= j < sd_elems t -> Freq s t j <> 0 -> In j (bt_U s t) /\ bt_F s t j = Freq s t j)
  /\ (forall j, In j (bt_U s t) -> Freq s t j = 0 -> bt_F s t j = 1)
  /\ 0 <= bt_npad s t <= 2
  /\ zlen (bt_U s t) = zlen (Ulist (tree_fc s t) t) + bt_npad s t.
Proof.
  intros s t. pose proof (pads_facts t (tree_fc s t)) as (ND & RNG & U2 & PD & MX1 & MX2). pose proof (elems_tsize t).
  unfold bt_U, bt_mc, bt_F, bt_npad, Freq in *.
  split; [exact ND|]. split; [intros j Hj; split; auto|]. split; [exact MX2|]. split; [exact U2|].
  split.
  { intros j Hj Hnz. split.
    - unfold UP. apply in_app_iff. left. unfold Ulist. apply Ul_in; lia.
    - unfold FP. destruct (existsb (Z.eqb j) (pads (tree_fc s t) t)) eqn:E; [|reflexivity].
      apply existsb_exists in E. destruct E as (x & Hx & Ex). apply Z.eqb_eq in Ex. subst x. apply PD in Hx. lia. }
  split.
  { intros j Hj Hz. unfold FP. destruct (existsb (Z.eqb j) (pads (tree_fc s t) t)) eqn:E; [reflexivity|].
    exfalso. unfold UP in Hj. apply in_app_iff in Hj. destruct Hj as [Hj|Hj].
    - unfold Ulist in Hj. apply Ul_in in Hj; lia.
    - assert (existsb (Z.eqb j) (pads (tree_fc s t) t) = true); [|congruence].
      apply existsb_exists. exists j. rewrite Z.eqb_refl. auto. }
  unfold UP, pads. rewrite zlen_app. destruct (Ulist (tree_fc s t) t) as [|? [|? ?]]; cbn; unfold zlen; cbn; lia.
Qed.

Lemma bt_Ftot_eq : forall s t, bt_Ftot s t = zsum (map (Freq s t) (Ulist (tree_fc s t) t)) + bt_npad s t.
Proof.
  intros s t. pose proof (pads_facts t (tree_fc s t)) as (ND & RNG & U2 & PD & MX1 & MX2). pose proof (elems_tsize t).
  unfold bt_Ftot, Ftot, bt_npad, UP. rewrite map_app, zsum_app. f_equal.
  - apply zsum_map_ext. intros j Hj. unfold FP, Freq.
    destruct (existsb (Z.eqb j) (pads (tree_fc s t) t)) eqn:E; [|reflexivity].
    apply existsb_exists in E. destruct E as (x & Hx & Ex). apply Z.eqb_eq in Ex. subst x.
    apply PD in Hx. unfold Ulist in Hj. apply Ul_in in Hj; lia.
  - transitivity (zsum (map (fun _ => 1) (pads (tree_fc s t) t))).
    + apply zsum_map_ext. intros j Hj. unfold FP. replace (existsb (Z.eqb j) (pads (tree_fc s t) t)) with true; [reflexivity|].
      symmetry. apply existsb_exists. exists j. rewrite Z.eqb_refl. auto.
    + generalize (pads (tree_fc s t) t) as l. clear. induction l; [reflexivity|]. cbn. rewrite IHl, zlen_cons. lia.
Qed.


Section Main.
Variables (s : deflate_state) (t : tree_id).
Hypothesis PRE : bt_pre s t.

Local Set Warnings "-notation-for-abbreviation".
Local Notation U := (bt_U s t).
Local Notation F := (bt_F s t).
Local Notation ML := (sd_max_length t).
Local Notation elems := (sd_elems t).

Theorem build_tree_huffman :
  exists L : Z -> Z,
    (exists T, hbuild (map (fun j => HL (F j) j) U) T
               /\ Permutation (map (fun e => (ea e, ed e)) (hprof 0 T)) (map (fun j => (j, L j)) U)
               /\ Permutation (map (fun e => (ea e, ew e)) (hprof 0 T)) (map (fun j => (j, F j)) U)
               /\ hw T = bt_Ftot s t)
    /\ (forall j, In j U -> 1 <= L j)
    /\ (bt_Ftot s t < fibZ (ML + 3) -> forall j, In j U -> L j <= ML)
    /\ ((forall j, In j U -> L j <= ML) ->
        let s' := build_tree s t in
           (forall j, In j U -> Len s' t j = L j)
        /\ (forall j, 0 <= j < elems -> ~ In j U -> Len s' t j = 0)
        /\ zsum (map (fun j => 2 ^ (ML - L j)) U) = 2 ^ ML
        /\ (forall H c, dep_ok H c -> kraft H c <= 2 ^ H -> (forall e, In e c -> 0 <= ew e) ->
              Permutation (map ew c) (map F U) -> zsum (map (fun j => F j * L j) U) <= ccost c)
        /\ (forall i j, In i U -> In j U -> F i < F j -> L j <= L i)
        /\ ds_opt_len s' = wrap64 (ds_opt_len s - bt_npad s t + zsum (map (fun j => F j * (L j + xbits t j)) U))
        /\ ds_static_len s' = (if stree_has t
                               then wrap64 (ds_static_len s - bt_slpad s t + zsum (map (fun j => F j * (stree_Len t j + xbits t j)) U))
                               else ds_static_len s)
        /\ max_code s' t = bt_mc s t
        /\ (forall b, 0 <= b <= 15 -> bl_count_get s' b = zsum (map (fun j => if L j =? b then 1 else 0) U))
        /\ (exists FC' DL' HP' DP' BC', s' = bt_upd s t FC' DL' HP' 1 (575 - 2 * zlen U - 1) DP' BC' (ds_opt_len s') (ds_static_len s') (bt_mc s t)
               /\ arr_len FC' = tsize t /\ arr_len DL' = tsize t /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ arr_len BC' = 16)).
Proof.
  destruct PRE as [TL Fnn FB OLr SLr].
  destruct (build_tree_front s t TL Fnn FB OLr SLr) as (FC & DL & HP & DP & sub & EBT & INV).
  set (FC0 := tree_fc s t) in *.
  assert (LBC : arr_len (ds_bl_count s) = 16) by (unfold tree_lens in TL; tauto).
  set (OL2 := wrap64 (ds_opt_len s - zlen (pads FC0 t))) in *.
  set (SL2 := if stree_has t then wrap64 (ds_static_len s - sl_pad t FC0) else ds_static_len s) in *.
  assert (OL2r : 0 <= OL2 < 2 ^ 64) by (subst OL2; apply wrap64_range).
  assert (SL2r : 0 <= SL2 < 2 ^ 64) by (subst SL2; destruct (stree_has t); [apply wrap64_range| exact SLr]).
  change (575 - 2 * u t FC0) with (hm t FC0) in INV.
  pose proof (leaf_depths t FC0 FC DL HP DP sub INV) as [PD PW].
  pose proof (T_build t FC0 FC DL HP DP sub INV) as TB.
  pose proof (T_leaves t FC0 FC DL HP DP sub INV) as [PT WT].
  pose proof (bt_U_facts s t) as (NDU & RNGU & MCin & U2 & _).
  set (TT := T HP sub) in *. set (L := nd DL HP) in *.
  assert (HWT : hw TT = bt_Ftot s t).
  { unfold bt_Ftot, Ftot. rewrite <- (hw_prof 0). fold FC0.
    transitivity (zsum (map snd (map (fun e => (ea e, ew e)) (hprof 0 TT)))); [rewrite map_map; reflexivity|].
    rewrite (zsum_map_perm snd _ _ PW). rewrite map_map. reflexivity. }
  assert (LF : leaf_forest (F0 t FC0)).
  { intros x Hx. unfold F0 in Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & _). exact I. }
  assert (F0w : forall x, In x (F0 t FC0) -> 1 <= hw x).
  { intros x Hx. unfold F0 in Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & Hj). cbn. apply FP_pos; [|exact Hj].
    intros k Hk. unfold Freq in Fnn. apply Fnn. exact Hk. }
  assert (ENT : forall j, In j U -> exists e, In e (hprof 0 TT) /\ ea e = j /\ ed e = L j /\ ew e = F j).
  { intros j Hj. assert (Hin : In (j, L j) (map (fun e => (ea e, ed e)) (hprof 0 TT))).
    { apply (Permutation_in _ (Permutation_sym PD)). apply in_map_iff. exists j. auto. }
    apply in_map_iff in Hin. destruct Hin as (e & Ee & He). injection Ee as E1 E2.
    exists e. repeat split; auto. rewrite (WT e He), E1. reflexivity. }
  exists L. split.
  { exists TT. split; [exact TB|]. split; [exact PD|]. split; [exact PW| exact HWT]. }
  split.
  { intros j Hj. destruct (ENT j Hj) as (e & He & <- & <- & _). destruct (T_prof t FC0 FC DL HP DP sub INV e He) as (_ & _ & ?). assumption. }
  split.
  { intros HF j Hj. destruct (ENT j Hj) as (e & He & <- & <- & _).
    apply (hbuild_depth_bound (F0 t FC0) TT (ML) TB LF F0w); [rewrite HWT; exact HF| exact He]. }
  intros NOV.
  destruct (gen_bitlen_pass1 s t FC0 (ds_bl_count s) OL2 SL2 FC DL HP DP sub INV LBC OL2r SL2r) as (DLc & BCc & OLc & SLc & ovc & G & EGB).
  destruct (pass1_summary t FC0 OL2 SL2 FC DL HP DP sub INV OL2r SL2r DLc BCc OLc SLc ovc G) as (SDL & SZ & SBC & SOL & SSL & SOV & LDLc & LBCc).
  assert (OV0 : ovc = 0).
  { apply (proj2 SOV). intros e He. destruct (T_prof t FC0 FC DL HP DP sub INV e He) as (A1 & A2 & A3).
    fold L in A2. rewrite <- A2. apply NOV. exact A1. }
  rewrite OV0 in EGB. cbn [Z.eqb] in EGB.
  destruct (gen_codes_flat s t FC DLc (HP7 t FC0 HP) 1 (hm t FC0 - 1) DP BCc OLc SLc (MCP FC0 t) (MCP FC0 t)) as (FC' & EGC & LFC').
  assert (ES : build_tree s t = bt_upd s t FC' DLc (HP7 t FC0 HP) 1 (hm t FC0 - 1) DP BCc OLc SLc (MCP FC0 t)).
  { rewrite EBT. unfold HP7, root in EGB |- *. unfold hm in *. rewrite EGB. exact EGC. }
  assert (LminU : forall j, In j U -> Z.min (L j) ML = L j) by (intros j Hj; specialize (NOV j Hj); lia).
  cbv zeta. rewrite ES. unfold Len, bl_count_get. autorewrite with btupd.
  split; [intros j Hj; rewrite SDL by exact Hj; apply LminU; exact Hj|].
  split; [exact SZ|].
  split.
  {
    destruct (tree_code_complete TT) as [DT KT].
    assert (HH : hheight TT <= ML).
    { destruct (hheight_attained 0 TT) as (e & He & De). rewrite Z.add_0_l in De. rewrite <- De.
      destruct (T_prof t FC0 FC DL HP DP sub INV e He) as (A1 & A2 & A3). fold L in A2. rewrite <- A2. apply NOV. exact A1. }
    pose proof (kraft_scale ML (hheight TT) (hprof 0 TT) ltac:(intros e He; pose proof (hprof_dep 0 TT e He); lia) HH) as KS.
    rewrite KT, <- Z.pow_add_r in KS by (pose proof (hheight_nonneg TT); lia).
    replace (ML - hheight TT + hheight TT) with ML in KS by lia.
    rewrite <- KS. unfold kraft.
    transitivity (zsum (map (fun p => 2 ^ (ML - snd p)) (map (fun j => (j, L j)) U))); [rewrite map_map; reflexivity|].
    rewrite <- (zsum_map_perm _ _ _ PD). rewrite map_map. reflexivity. }
  split.
  {
    intros H c D K W P.
    assert (CT : zsum (map (fun j => F j * L j) U) = hcost TT).
    { pose proof (hcost_prof 0 TT) as CP. transitivity (ccost (hprof 0 TT)); [|lia]. unfold ccost.
      transitivity (zsum (map (fun p => F (fst p) * snd p) (map (fun j => (j, L j)) U))); [rewrite map_map; reflexivity|].
      rewrite <- (zsum_map_perm _ _ _ PD). rewrite map_map. apply zsum_map_ext. intros e He. cbn. rewrite (WT e He). reflexivity. }
    rewrite CT. apply (huffman_optimal_kraft (F0 t FC0) TT TB LF H c D K W).
    rewrite P. unfold F0. rewrite map_map. cbn. apply Permutation_refl. }
  split.
  {
    intros i j Hi Hj Fij. destruct (Z_le_gt_dec (L j) (L i)) as [|LT]; [assumption|]. exfalso.
    assert (Hij : i <> j) by (intros ->; lia).
    destruct (ENT i Hi) as (ei & Hei & Ai & Di & Wi). destruct (ENT j Hj) as (ej & Hej & Aj & Dj & Wj).
    apply in_split in Hei. destruct Hei as (l1 & l2 & EP).
    assert (Hej' : In ej (l1 ++ l2)).
    { assert (In ej (hprof 0 TT)) by exact Hej. rewrite EP in H. apply in_app_iff in H. cbn in H.
      destruct H as [H|[H|H]]; [apply in_app_iff; now left| subst; congruence| apply in_app_iff; now right]. }
    apply in_split in Hej'. destruct Hej' as (m1 & m2 & EQ).
    assert (PP0 : Permutation (hprof 0 TT) (ei :: ej :: m1 ++ m2)).
    { rewrite EP. rewrite <- Permutation_middle. apply perm_skip. rewrite EQ. rewrite <- Permutation_middle. apply Permutation_refl. }
    destruct (tree_code_complete TT) as [DT KT].
    set (c := setd ei (L j) :: setd ej (L i) :: m1 ++ m2).
    pose proof (huffman_optimal (F0 t FC0) TT TB LF (hheight TT) c) as OPT.
    assert (SDd : forall e d, ed (setd e d) = d) by reflexivity.
    assert (SDw : forall e d, ew (setd e d) = ew e) by reflexivity.
    assert (Dc : dep_ok (hheight TT) c).
    { intros e He. subst c. cbn [In app] in He. destruct He as [<-|[<-|He]]; rewrite ?SDd.
      - rewrite <- Dj. apply DT. apply (Permutation_in _ (Permutation_sym PP0)). cbn [In app]. auto.
      - rewrite <- Di. apply DT. apply (Permutation_in _ (Permutation_sym PP0)). cbn [In app]. auto.
      - apply DT. apply (Permutation_in _ (Permutation_sym PP0)). right. right. exact He. }
    assert (Kc : kraft (hheight TT) c = 2 ^ hheight TT).
    { rewrite <- KT. rewrite (kraft_perm _ _ _ PP0). subst c. rewrite !kraft_cons, !SDd. rewrite Di, Dj. lia. }
    assert (Pc : Permutation (map ew c) (map hw (F0 t FC0))).
    { rewrite <- (hbuild_leaves_w _ _ TB LF). rewrite (Permutation_map ew PP0). subst c. cbn [map]. rewrite !SDw. apply Permutation_refl. }
    specialize (OPT Dc Kc Pc).
    pose proof (hcost_prof 0 TT) as CP. rewrite (ccost_perm _ _ PP0) in CP.
    rewrite !ccost_cons in CP.
    subst c. rewrite !ccost_cons, !SDd, !SDw in OPT. rewrite Di, Dj, Wi, Wj in *. nia. }
  split.
  { rewrite SOL. subst OL2. rewrite BuildTreeModel.wrap64_add_l. unfold bt_npad. fold FC0. f_equal. f_equal.
    apply zsum_map_ext. intros j Hj. rewrite LminU by exact Hj. reflexivity. }
  split.
  { rewrite SSL. subst SL2. unfold bt_slpad. fold FC0. destruct (stree_has t); [|reflexivity]. rewrite BuildTreeModel.wrap64_add_l. reflexivity. }
  split; [reflexivity|].
  split.
  { intros b Hb. rewrite SBC by exact Hb. apply zsum_map_ext. intros j Hj. rewrite LminU by exact Hj. reflexivity. }
  destruct INV as [(L1 & L2 & L3 & L4)].
  exists FC', DLc, (HP7 t FC0 HP), DP, BCc. split; [|repeat split; try assumption].
  - unfold hm. unfold bt_U, u. fold FC0. reflexivity.
  - rewrite LFC'. exact L1.
  - unfold HP7. rewrite arr_len_set. exact L3.
Qed.


Theorem build_tree_lengths :
  exists L Lz : Z -> Z,
    (exists T, hbuild (map (fun j => HL (F j) j) U) T
               /\ Permutation (map (fun e => (ea e, ed e)) (hprof 0 T)) (map (fun j => (j, L j)) U)
               /\ Permutation (map (fun e => (ea e, ew e)) (hprof 0 T)) (map (fun j => (j, F j)) U)
               /\ hw T = bt_Ftot s t)
    /\ (forall j, In j U -> 1 <= L j)
    /\ (bt_Ftot s t < fibZ (ML + 3) -> forall j, In j U -> L j <= ML)
    /\ (forall H c, dep_ok H c -> kraft H c <= 2 ^ H -> (forall e, In e c -> 0 <= ew e) ->
          Permutation (map ew c) (map F U) -> zsum (map (fun j => F j * L j) U) <= ccost c)
    /\ (forall i j, In i U -> In j U -> F i < F j -> L j <= L i)
    /\ ((forall j, In j U -> L j <= ML) -> forall j, In j U -> Lz j = L j)
    /\ let s' := build_tree s t in
       (forall j, In j U -> Len s' t j = Lz j /\ 1 <= Lz j <= ML)
    /\ (forall j, 0 <= j < elems -> ~ In j U -> Len s' t j = 0)
    /\ zsum (map (fun j => 2 ^ (ML - Lz j)) U) = 2 ^ ML
    /\ (forall i j, In i U -> In j U -> F i < F j -> Lz j <= Lz i)
    /\ ds_opt_len s' = wrap64 (ds_opt_len s - bt_npad s t + zsum (map (fun j => F j * (Lz j + xbits t j)) U))
    /\ ds_static_len s' = (if stree_has t
                           then wrap64 (ds_static_len s - bt_slpad s t + zsum (map (fun j => F j * (stree_Len t j + xbits t j)) U))
                           else ds_static_len s)
    /\ max_code s' t = bt_mc s t
    /\ (forall b, 0 <= b <= 15 -> bl_count_get s' b = zsum (map (fun j => if Lz j =? b then 1 else 0) U))
    /\ bt_pen U F ML L Lz (bl_count_get s')
    /\ (exists FC' DL' HP' DP' BC', s' = bt_upd s t FC' DL' HP' 1 (575 - 2 * zlen U - 1) DP' BC' (ds_opt_len s') (ds_static_len s') (bt_mc s t)
           /\ arr_len FC' = tsize t /\ arr_len DL' = tsize t /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ arr_len BC' = 16).
Proof.
  destruct build_tree_huffman as (L & HT & L1 & LF & NOV).
  destruct PRE as [TL Fnn FB OLr SLr].
  destruct (build_tree_front s t TL Fnn FB OLr SLr) as (FC & DL & HP & DP & sub & EBT & INV).
  set (FC0 := tree_fc s t) in *.
  assert (LBC : arr_len (ds_bl_count s) = 16) by (unfold tree_lens in TL; tauto).
  set (OL2 := wrap64 (ds_opt_len s - zlen (pads FC0 t))) in *.
  set (SL2 := if stree_has t then wrap64 (ds_static_len s - sl_pad t FC0) else ds_static_len s) in *.
  assert (OL2r : 0 <= OL2 < 2 ^ 64) by (subst OL2; apply wrap64_range).
  assert (SL2r : 0 <= SL2 < 2 ^ 64) by (subst SL2; destruct (stree_has t); [apply wrap64_range| exact SLr]).
  change (575 - 2 * u t FC0) with (hm t FC0) in INV.
  pose proof (leaf_depths t FC0 FC DL HP DP sub INV) as [PD PW].
  pose proof (bt_U_facts s t) as (NDU & RNGU & MCin & U2 & _).
  clear L HT L1 LF NOV.
  destruct build_tree_huffman as (L & HT & L1 & LF & NOV).
  clear L HT L1 LF NOV.
  set (L := nd DL HP).
  pose proof (T_build t FC0 FC DL HP DP sub INV) as TB.
  pose proof (T_leaves t FC0 FC DL HP DP sub INV) as [PT WT].
  set (TT := T HP sub) in *.
  assert (HWT : hw TT = bt_Ftot s t).
  { unfold bt_Ftot, Ftot. rewrite <- (hw_prof 0). fold FC0.
    transitivity (zsum (map snd (map (fun e => (ea e, ew e)) (hprof 0 TT)))); [rewrite map_map; reflexivity|].
    rewrite (zsum_map_perm snd _ _ PW). rewrite map_map. reflexivity. }
  assert (LFo : leaf_forest (F0 t FC0)).
  { intros x Hx. unfold F0 in Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & _). exact I. }
  assert (F0w : forall x, In x (F0 t FC0) -> 1 <= hw x).
  { intros x Hx. unfold F0 in Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & Hj). cbn. apply FP_pos; [|exact Hj].
    intros k Hk. unfold Freq in Fnn. apply Fnn. exact Hk. }
  assert (ENT : forall j, In j U -> exists e, In e (hprof 0 TT) /\ ea e = j /\ ed e = L j /\ ew e = F j).
  { intros j Hj. assert (Hin : In (j, L j) (map (fun e => (ea e, ed e)) (hprof 0 TT))).
    { apply (Permutation_in _ (Permutation_sym PD)). apply in_map_iff. exists j. auto. }
    apply in_map_iff in Hin. destruct Hin as (e & Ee & He). injection Ee as E1 E2.
    exists e. repeat split; auto. rewrite (WT e He), E1. reflexivity. }
  destruct (gen_bitlen_pass1 s t FC0 (ds_bl_count s) OL2 SL2 FC DL HP DP sub INV LBC OL2r SL2r) as (DLc & BCc & OLc & SLc & ovc & G & EGB).
  destruct (pass1_summary t FC0 OL2 SL2 FC DL HP DP sub INV OL2r SL2r DLc BCc OLc SLc ovc G) as (SDL & SZ & SBC & SOL & SSL & SOV & LDLc & LBCc).
  assert (Lge1 : forall j, In j U -> 1 <= L j).
  { intros j Hj. destruct (ENT j Hj) as (e & He & <- & <- & _). destruct (T_prof t FC0 FC DL HP DP sub INV e He) as (_ & _ & ?). assumption. }
  assert (LOPT : forall H c, dep_ok H c -> kraft H c <= 2 ^ H -> (forall e, In e c -> 0 <= ew e) ->
          Permutation (map ew c) (map F U) -> zsum (map (fun j => F j * L j) U) <= ccost c).
  { intros H c D K W P.
    assert (CT : zsum (map (fun j => F j * L j) U) = hcost TT).
    { pose proof (hcost_prof 0 TT) as CP. transitivity (ccost (hprof 0 TT)); [|lia]. unfold ccost.
      transitivity (zsum (map (fun p => F (fst p) * snd p) (map (fun j => (j, L j)) U))); [rewrite map_map; reflexivity|].
      rewrite <- (zsum_map_perm _ _ _ PD). rewrite map_map. apply zsum_map_ext. intros e He. cbn. rewrite (WT e He). reflexivity. }
    rewrite CT. apply (huffman_optimal_kraft (F0 t FC0) TT TB LFo H c D K W).
    rewrite P. unfold F0. rewrite map_map. cbn. apply Permutation_refl. }
  assert (KU : forall Lx, Permutation (map Lx U) (map L U) -> zsum (map (fun j => 2 ^ (zlen U - Lx j)) U) = 2 ^ (zlen U)).
  { intros Lx PX. rewrite <- (map_map Lx (fun d => 2 ^ (zlen U - d))). rewrite (zsum_map_perm _ _ _ PX). rewrite map_map.
    destruct (tree_code_complete TT) as [DT KT].
    assert (HH : hheight TT <= zlen U).
    { pose proof (hheight_leaves TT). pose proof (Permutation_length PD) as PL. rewrite !length_map in PL. unfold bt_U, zlen. fold FC0. rewrite <- PL. lia. }
    pose proof (kraft_scale (zlen U) (hheight TT) (hprof 0 TT) ltac:(intros e He; pose proof (hprof_dep 0 TT e He); lia) HH) as KS.
    rewrite KT, <- Z.pow_add_r in KS by (pose proof (hheight_nonneg TT); pose proof (zlen_nonneg U); lia).
    replace (zlen U - hheight TT + hheight TT) with (zlen U) in KS by lia. rewrite <- KS. unfold kraft.
    transitivity (zsum (map (fun p => 2 ^ (zlen U - snd p)) (map (fun j => (j, L j)) U))); [rewrite !map_map; reflexivity|].
    rewrite <- (zsum_map_perm _ _ _ PD). rewrite map_map. reflexivity. }
  assert (LMONO : forall i j, In i U -> In j U -> F i < F j -> L j <= L i).
  { intros i j Hi Hj Fij. destruct (Z_le_gt_dec (L j) (L i)) as [|LT]; [assumption|]. exfalso.
    assert (Hij : i <> j) by (intros ->; lia).
    destruct (ENT i Hi) as (ei & Hei & Ai & Di & Wi). destruct (ENT j Hj) as (ej & Hej & Aj & Dj & Wj).
    apply in_split in Hei. destruct Hei as (l1 & l2 & EP).
    assert (Hej' : In ej (l1 ++ l2)).
    { assert (In ej (hprof 0 TT)) by exact Hej. rewrite EP in H. apply in_app_iff in H. cbn in H.
      destruct H as [H|[H|H]]; [apply in_app_iff; now left| subst; congruence| apply in_app_iff; now right]. }
    apply in_split in Hej'. destruct Hej' as (m1 & m2 & EQ).
    assert (PP0 : Permutation (hprof 0 TT) (ei :: ej :: m1 ++ m2)).
    { rewrite EP. rewrite <- Permutation_middle. apply perm_skip. rewrite EQ. rewrite <- Permutation_middle. apply Permutation_refl. }
    destruct (tree_code_complete TT) as [DT KT].
    set (c := setd ei (L j) :: setd ej (L i) :: m1 ++ m2).
    pose proof (huffman_optimal (F0 t FC0) TT TB LFo (hheight TT) c) as OPT.
    assert (SDd : forall e d, ed (setd e d) = d) by reflexivity.
    assert (SDw : forall e d, ew (setd e d) = ew e) by reflexivity.
    assert (Dc : dep_ok (hheight TT) c).
    { intros e He. subst c. cbn [In app] in He. destruct He as [<-|[<-|He]]; rewrite ?SDd.
      - rewrite <- Dj. apply DT. apply (Permutation_in _ (Permutation_sym PP0)). cbn [In app]. auto.
      - rewrite <- Di. apply DT. apply (Permutation_in _ (Permutation_sym PP0)). cbn [In app]. auto.
      - apply DT. apply (Permutation_in _ (Permutation_sym PP0)). right. right. exact He. }
    assert (Kc : kraft (hheight TT) c = 2 ^ hheight TT).
    { rewrite <- KT. rewrite (kraft_perm _ _ _ PP0). subst c. rewrite !kraft_cons, !SDd. rewrite Di, Dj. lia. }
    assert (Pc : Permutation (map ew c) (map hw (F0 t FC0))).
    { rewrite <- (hbuild_leaves_w _ _ TB LFo). rewrite (Permutation_map ew PP0). subst c. cbn [map]. rewrite !SDw. apply Permutation_refl. }
    specialize (OPT Dc Kc Pc).
    pose proof (hcost_prof 0 TT) as CP. rewrite (ccost_perm _ _ PP0) in CP.
    rewrite !ccost_cons in CP.
    subst c. rewrite !ccost_cons, !SDd, !SDw in OPT. rewrite Di, Dj, Wi, Wj in *. nia. }
  destruct (Z.eq_dec ovc 0) as [OV0|OV1].
  -
    rewrite OV0 in EGB. cbn [Z.eqb] in EGB.
    destruct (gen_codes_flat s t FC DLc (HP7 t FC0 HP) 1 (hm t FC0 - 1) DP BCc OLc SLc (MCP FC0 t) (MCP FC0 t)) as (FC' & EGC & LFC').
    assert (ES : build_tree s t = bt_upd s t FC' DLc (HP7 t FC0 HP) 1 (hm t FC0 - 1) DP BCc OLc SLc (MCP FC0 t)).
    { rewrite EBT. unfold HP7, root in EGB |- *. unfold hm in *. rewrite EGB. exact EGC. }
    assert (NOV : forall j, In j U -> L j <= ML).
    { intros j Hj. destruct (ENT j Hj) as (e & He & <- & <- & _). apply (proj1 SOV OV0). exact He. }
    assert (LminU : forall j, In j U -> Z.min (L j) ML = L j) by (intros j Hj; specialize (NOV j Hj); lia).
    exists L, L. split; [exists TT; split; [exact TB|]; split; [exact PD|]; split; [exact PW| exact HWT]|].
    split; [exact Lge1|].
    split; [intros HF j Hj; destruct (ENT j Hj) as (e & He & <- & <- & _); apply (hbuild_depth_bound (F0 t FC0) TT ML TB LFo F0w); [rewrite HWT; exact HF| exact He]|].
    split; [exact LOPT|]. split; [exact LMONO|]. split; [intros; reflexivity|].
    cbv zeta. rewrite ES. unfold Len, bl_count_get. autorewrite with btupd.
    split; [intros j Hj; rewrite SDL by exact Hj; rewrite LminU by exact Hj; auto|].
    split; [exact SZ|].
    split.
    { destruct (tree_code_complete TT) as [DT KT].
      assert (HH : hheight TT <= ML).
      { destruct (hheight_attained 0 TT) as (e & He & De). rewrite Z.add_0_l in De. rewrite <- De.
        destruct (T_prof t FC0 FC DL HP DP sub INV e He) as (A1 & A2 & A3). fold L in A2. rewrite <- A2. apply NOV. exact A1. }
      pose proof (kraft_scale ML (hheight TT) (hprof 0 TT) ltac:(intros e He; pose proof (hprof_dep 0 TT e He); lia) HH) as KS.
      rewrite KT, <- Z.pow_add_r in KS by (pose proof (hheight_nonneg TT); lia).
      replace (ML - hheight TT + hheight TT) with ML in KS by lia.
      rewrite <- KS. unfold kraft.
      transitivity (zsum (map (fun p => 2 ^ (ML - snd p)) (map (fun j => (j, L j)) U))); [rewrite map_map; reflexivity|].
      rewrite <- (zsum_map_perm _ _ _ PD). rewrite map_map. reflexivity. }
    split; [exact LMONO|].
    split.
    { rewrite SOL. subst OL2. rewrite BuildTreeModel.wrap64_add_l. unfold bt_npad. fold FC0. f_equal. f_equal.
      apply zsum_map_ext. intros j Hj. rewrite LminU by exact Hj. reflexivity. }
    split.
    { rewrite SSL. subst SL2. unfold bt_slpad. fold FC0. destruct (stree_has t); [|reflexivity]. rewrite BuildTreeModel.wrap64_add_l. reflexivity. }
    split; [reflexivity|].
    split.
    { intros b Hb. rewrite SBC by exact Hb. apply zsum_map_ext. intros j Hj. rewrite LminU by exact Hj. reflexivity. }
    split.
    {
      pose proof (excess_identity t FC0 0 FC DL HP DP sub INV) as (EK & EO & NN0).
      pose proof (ML_range t FC0 FC DL HP DP sub INV) as MR.
      destruct G as [GL GD GT GZ GB GO GS GV].
      assert (N0 : HuffGen2.N t FC0 DL HP = 0) by (rewrite OV0 in GV; rewrite EO in GV; lia).
      exists L, ML. split; [apply Permutation_refl|]. split; [reflexivity|]. split; [exact LOPT|]. split; [exact LMONO|].
      split; [intros j Hj; split; [apply Lge1; exact Hj| apply (depth_le_leaves U L TT PD j Hj)]|].
      split; [lia|].
      split; [intros j Hj; split; [intros; reflexivity| left; reflexivity]|].
      split.
      - exists BCc. split; [exact LBCc|]. split; [exact SBC|].
        assert (EKc : zsum (map (fun j => 2 ^ (ML - Z.min (L j) ML)) U) - 2 ^ ML = 0).
        { unfold K0, phi in EK. unfold bt_U. fold FC0. subst L. lia. }
        rewrite EKc. split; [lia|]. intros b Hb. reflexivity.
      - split; [intros (j & Hj & Dj); exfalso; specialize (NOV j Hj); lia|].
        split; [rewrite (KU L (Permutation_refl _)); lia|].
        split.
        { intros _. rewrite (zsum_map_ext _ (fun _ => 0)) by (intros j Hj; lia).
          replace (zsum (map (fun _ : Z => 0) U)) with 0 by (generalize U; clear; induction l; cbn; lia).
          apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & Hj).
          pose proof (FP_pos t FC0 ltac:(intros k Hk; unfold Freq in Fnn; apply Fnn; exact Hk) j Hj) as X. unfold bt_F. fold FC0. lia. }
        split; [exact (KU L (Permutation_refl _))|].
        intros (j & Hj & Dj). exfalso. specialize (NOV j Hj). lia. }
    destruct INV as [(Ln1 & Ln2 & Ln3 & Ln4)].
    exists FC', DLc, (HP7 t FC0 HP), DP, BCc. split; [|repeat split; try assumption].
    + unfold hm. unfold bt_U, u. fold FC0. reflexivity.
    + rewrite LFC'. exact Ln1.
    + unfold HP7. rewrite arr_len_set. exact Ln3.
  -
    replace (ovc =? 0) with false in EGB by (symmetry; apply Z.eqb_neq; exact OV1).
    destruct (gen_bitlen_overflow2 s t FC0 (ds_bl_count s) OL2 SL2 FC DL HP DP sub INV DLc BCc OLc SLc ovc LBC OL2r SL2r G OV1)
      as (DLf & BCf & OLf & bstar & sN & E23 & LDLf & LBCf & RNG & ZER & SUMg & KB' & OUTf & NNf & OLF & MONO
          & EBCF & N1 & Hbs & Hs & LOWEQ & ATEQ & GAP & LPM1 & LPP & LPN & LPR & LPMO & LPC & LPJ & LPZ & LPEN & LRF & LZC).
    rewrite E23 in EGB.
    destruct (gen_codes_flat s t FC DLf (HP7 t FC0 HP) 1 (hm t FC0 - 1) DP BCf OLf SLc (MCP FC0 t) (MCP FC0 t)) as (FC' & EGC & LFC').
    assert (ES : build_tree s t = bt_upd s t FC' DLf (HP7 t FC0 HP) 1 (hm t FC0 - 1) DP BCf OLf SLc (MCP FC0 t)).
    { rewrite EBT. unfold HP7, root in EGB |- *. unfold hm in *. rewrite EGB. exact EGC. }
    exists L, (arr_get DLf). split; [exists TT; split; [exact TB|]; split; [exact PD|]; split; [exact PW| exact HWT]|].
    split; [exact Lge1|].
    split; [intros HF j Hj; destruct (ENT j Hj) as (e & He & <- & <- & _); apply (hbuild_depth_bound (F0 t FC0) TT ML TB LFo F0w); [rewrite HWT; exact HF| exact He]|].
    split; [exact LOPT|]. split; [exact LMONO|].
    split.
    { intros NOV. exfalso. apply OV1. apply (proj2 SOV). intros e He.
      destruct (T_prof t FC0 FC DL HP DP sub INV e He) as (A1 & A2 & A3). fold L in A2. rewrite <- A2. apply NOV. exact A1. }
    cbv zeta. rewrite ES. unfold Len, bl_count_get. autorewrite with btupd.
    split; [intros j Hj; split; [reflexivity| apply RNG; exact Hj]|].
    split; [exact ZER|].
    split; [unfold bt_U; fold FC0; rewrite (SUMg (fun x => 2 ^ (ML - x))); exact KB'|].
    split; [exact MONO|].
    split; [rewrite OLF; subst OL2; rewrite BuildTreeModel.wrap64_add_l; unfold bt_npad; fold FC0; reflexivity|].
    split.
    { rewrite SSL. subst SL2. unfold bt_slpad. fold FC0. destruct (stree_has t); [|reflexivity]. rewrite BuildTreeModel.wrap64_add_l. reflexivity. }
    split; [reflexivity|].
    split.
    { intros b Hb. unfold bt_U. fold FC0. rewrite (SUMg (fun x => if x =? b then 1 else 0)).
      pose proof (ML_range t FC0 FC DL HP DP sub INV) as MR.
      destruct (Z_lt_le_dec b 1) as [Hb1|Hb1]; [|destruct (Z_lt_le_dec ML b) as [Hb2|Hb2]].
      - rewrite OUTf by lia. unfold isum. symmetry. etransitivity; [apply zsum_map_ext; intros i Hi; apply in_ziota in Hi; destruct (Z.eqb_spec i b); [lia|]; apply Z.mul_0_r|].
        generalize (ziota 1 (Z.to_nat ML)); clear; induction l; cbn; lia.
      - rewrite OUTf by lia. unfold isum. symmetry. etransitivity; [apply zsum_map_ext; intros i Hi; apply in_ziota in Hi; destruct (Z.eqb_spec i b); [lia|]; apply Z.mul_0_r|].
        generalize (ziota 1 (Z.to_nat ML)); clear; induction l; cbn; lia.
      - symmetry. rewrite <- (isum_ext (fun i => if i =? b then arr_get BCf b else 0)) by (intros i Hi; destruct (Z.eqb_spec i b); subst; lia).
        unfold isum. rewrite <- (Z2Nat.id ML) in Hb2 by lia. revert Hb1 Hb2. generalize (Z.to_nat ML) as q. clear. intros q.
        assert (G0 : forall a, (a <= b < a + Z.of_nat q -> zsum (map (fun i : Z => if i =? b then arr_get BCf b else 0) (ziota a q)) = arr_get BCf b)
                          /\ (~ (a <= b < a + Z.of_nat q) -> zsum (map (fun i : Z => if i =? b then arr_get BCf b else 0) (ziota a q)) = 0)).
        { induction q as [|q IH]; intros a; [cbn; split; intros; lia|]. rewrite Nat2Z.inj_succ. cbn [ziota map zsum].
          destruct (IH (a + 1)) as [A B]. split; intros; destruct (Z.eqb_spec a b); first [rewrite B; lia | rewrite A; lia | lia]. }
        intros. apply (proj1 (G0 1)). lia. }
    split.
    {
      pose proof (excess_identity t FC0 0 FC DL HP DP sub INV) as (EK & EO & NN0).
      pose proof (ML_range t FC0 FC DL HP DP sub INV) as MR.
      set (Lp := HuffPen.L' t FC0 DL HP) in *.
      assert (HU : u t FC0 = zlen U) by reflexivity.
      assert (CEQ : zsum (map (fun j => F j * Lp j) U) = zsum (map (fun j => F j * L j) U)).
      { apply Z.le_antisymm; [exact LPC|].
        set (H := zlen U). set (c := map (fun j => E (F j) j (Lp j)) U).
        assert (D : dep_ok H c).
        { unfold dep_ok. intros e He. subst c. apply in_map_iff in He. destruct He as (j & <- & Hj). cbn [ed]. subst H. specialize (LPR j Hj). lia. }
        assert (W : forall e, In e c -> 0 <= ew e).
        { intros e He. subst c. apply in_map_iff in He. destruct He as (j & <- & Hj). cbn [ew].
          pose proof (FP_pos t FC0 ltac:(intros k Hk; unfold Freq in Fnn; apply Fnn; exact Hk) j Hj) as X. unfold F, bt_F. fold FC0. lia. }
        assert (PWc : Permutation (map ew c) (map F U)) by (subst c; rewrite map_map; cbn; apply Permutation_refl).
        assert (K : kraft H c <= 2 ^ H).
        { unfold kraft. subst c. rewrite map_map. cbn [ed].
          transitivity (zsum (map (fun d => 2 ^ (H - d)) (map Lp U))); [rewrite map_map; apply Z.le_refl|].
          rewrite (zsum_map_perm _ _ _ LPP).
          destruct (tree_code_complete TT) as [DT KT].
          assert (HH : hheight TT <= H).
          { subst H. pose proof (hheight_leaves TT). pose proof (Permutation_length PD) as PL. rewrite !length_map in PL. unfold bt_U, zlen. fold FC0. rewrite <- PL. lia. }
          pose proof (kraft_scale H (hheight TT) (hprof 0 TT) ltac:(intros e He; pose proof (hprof_dep 0 TT e He); lia) HH) as KS.
          rewrite KT, <- Z.pow_add_r in KS by (pose proof (hheight_nonneg TT); lia).
          replace (H - hheight TT + hheight TT) with H in KS by lia. rewrite <- KS. unfold kraft.
          transitivity (zsum (map (fun p => 2 ^ (H - snd p)) (map (fun j => (j, L j)) U))); [rewrite !map_map; apply Z.le_refl|].
          rewrite <- (zsum_map_perm _ _ _ PD). rewrite map_map. apply Z.le_refl. }
        pose proof (LOPT H c D K W PWc) as O. unfold ccost in O. subst c. rewrite map_map in O. cbn [ew ed] in O. exact O. }
      exists Lp, bstar. split; [exact LPP|]. split; [exact CEQ|].
      split; [intros H c D K W P; rewrite CEQ; apply (LOPT H c D K W P)|].
      split; [exact LPMO|]. split; [rewrite <- HU; exact LPR|]. split; [lia|].
      split; [exact LPJ|].
      assert (EKc : zsum (map (fun j => 2 ^ (ML - Z.min (L j) ML)) U) - 2 ^ ML = HuffGen2.N t FC0 DL HP).
      { unfold K0, phi in EK. unfold bt_U. fold FC0. subst L. lia. }
      split.
      - exists BCc. split; [exact LBCc|]. split; [exact SBC|]. rewrite EKc. split; [lia|]. intros b Hb. rewrite EBCF. reflexivity.
      - split.
        { intros _. split; [lia|]. split; [rewrite <- HU; exact GAP|].
          exists (RLl t FC0 HP). split; [apply (RL_perm t FC0 FC DL HP DP sub INV)|]. split; [apply (F_rank_noninc t FC0 FC DL HP DP sub INV)|].
          split; [exact LPN|]. exact LPZ. }
        split; [rewrite (KU Lp LPP); lia|].
        split; [intros M15; unfold bt_U, bt_F, bt_Ftot; fold FC0; exact (LPEN M15)|].
        split; [exact (KU Lp LPP)|].
        intros _. exists (RLl t FC0 HP). split; [apply (RL_perm t FC0 FC DL HP DP sub INV)|]. split; [apply (F_rank_noninc t FC0 FC DL HP DP sub INV)|].
        split; [exact LPN|]. split; [unfold bt_U, bt_F; fold FC0; exact LRF| exact LZC]. }
    destruct INV as [(Ln1 & Ln2 & Ln3 & Ln4)].
    exists FC', DLf, (HP7 t FC0 HP), DP, BCf. split; [|repeat split; try assumption].
    + unfold hm. unfold bt_U, u. fold FC0. reflexivity.
    + rewrite LFC'. exact Ln1.
    + unfold HP7. rewrite arr_len_set. exact Ln3.
Qed.

End Main.

