(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffBuild HuffFlush DeflRoom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import TreeModel ScanModel SendModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Fixpoint emits (f : nat) (lens : Z -> Z) (mc n prevlen nextlen count mx mn : Z) : list (Z * Z * Z * Z) :=
  match f with
  | O => []
  | S f' =>
      if n <=? mc then
        let curlen := nextlen in
        let nextlen' := lens (n + 1) in
        let count' := count + 1 in
        if (count' <? mx) && (curlen =? nextlen') then emits f' lens mc (n + 1) prevlen nextlen' count' mx mn
        else let '(mx', mn') := tree_counts curlen nextlen' in
             (mn, curlen, prevlen, count') :: emits f' lens mc (n + 1) curlen nextlen' 0 mx' mn'
      else []
  end.

Lemma emits_ext : forall f lens lens' mc n p q c mx mn, (forall i, lens i = lens' i) ->
  emits f lens mc n p q c mx mn = emits f lens' mc n p q c mx mn.
Proof.
  induction f as [|f IH]; intros; cbn; [reflexivity|]. rewrite <- !H.
  destruct (n <=? mc); [|reflexivity]. destruct ((c + 1 <? mx) && (q =? lens (n + 1))); [apply IH; exact H|].
  destruct (tree_counts q (lens (n + 1))). f_equal. apply IH. exact H.
Qed.

Definition em_upd (b : arr) (e : Z * Z * Z * Z) : arr :=
  let '(mn, cu, pr, ct) := e in st_upd mn b cu pr ct.
Definition em_calls (s : deflate_state) (e : Z * Z * Z * Z) : list (Z * Z) :=
  let '(mn, cu, pr, ct) := e in st_calls s mn cu pr ct.

Lemma scan_emits : forall f s0 b t mc n p q c mx mn,
  scan_tree_loop f (set_bl_tree_fc s0 b) t mc n p q c mx mn
  = set_bl_tree_fc s0 (fold_left em_upd (emits f (Len s0 t) mc n p q c mx mn) b).
Proof.
  induction f as [|f IH]; intros; [reflexivity|].
  rewrite scan_loop_S. cbn [emits]. destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct ((c + 1 <? mx) && (q =? Len s0 t (n + 1))); [apply IH|].
  destruct (tree_counts q (Len s0 t (n + 1))) as [mx' mn']. cbn [fold_left em_upd]. apply IH.
Qed.

Lemma send_emits : forall f s t mc n p q c mx mn, (mn = 3 \/ mn = 4) ->
  send_tree_loop f s t mc n p q c mx mn
  = sbs_run s (flat_map (em_calls s) (emits f (Len s t) mc n p q c mx mn)).
Proof.
  induction f as [|f IH]; intros s t mc n p q c mx mn Hmn; [reflexivity|].
  rewrite send_loop_S by lia. cbn [emits]. destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct ((c + 1 <? mx) && (q =? Len s t (n + 1))); [apply IH; exact Hmn|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:TC. cbn [flat_map em_calls].
  rewrite sbs_run_app. rewrite IH by (apply (tree_counts_range _ _ _ _ TC)).
  rewrite (emits_ext f (Len (sbs_run s (st_calls s mn q p (c + 1))) t) (Len s t)) by (intros; apply sbs_Len). f_equal.
  generalize (emits f (Len s t) mc (n + 1) q (Len s t (n + 1)) 0 mx' mn'). generalize (st_calls s mn q p (c + 1)). clear. intros cs l.
  induction l as [|e l IHl]; cbn; [reflexivity|]. rewrite IHl. f_equal.
  destruct e as [[[mn0 cu] pr] ct]. unfold em_calls, st_calls, blc. rewrite !sbs_Code, !sbs_Len. reflexivity.
Qed.


Definition blx (y : Z) : Z := if y =? REP_3_6 then 2 else if y =? REPZ_3_10 then 3 else if y =? REPZ_11_138 then 7 else 0.

Definition wsum (w : Z -> Z) (b : arr) : Z := zsum (map (fun y => arr_get b y * w y) (ziota 0 19)).

Lemma wsum_set : forall w b i v, arr_len b = 39 -> 0 <= i < 19 ->
  wsum w (arr_set b i v) = wsum w b + (v - arr_get b i) * w i.
Proof.
  intros w b i v L Hi. unfold wsum.
  rewrite (zsum_map_ziota_upd (fun y => arr_get b y * w y) (fun y => arr_get (arr_set b i v) y * w y) 0 19 i)
    by (intros j Hj; rewrite arr_get_set_other by lia; reflexivity).
  replace ((0 <=? i) && (i <? 0 + Z.of_nat 19)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
  rewrite arr_get_set_same by lia. lia.
Qed.

Lemma sumlen_repeat : forall v l k, sumlen (repeat (v, l) k) = Z.of_nat k * l.
Proof. induction k; cbn [repeat sumlen]; [lia|]. rewrite IHk. lia. Qed.

Section Emit.
Variable s : deflate_state.
Let LB (y : Z) : Z := Len s TB y.

Lemma emit_bits : forall mn cu pr ct b,
  arr_len b = 39 -> bnn b -> 0 <= cu <= 15 -> (mn = 3 \/ mn = 4) -> 1 <= ct -> bsum b + ct < 65536 ->
  sumlen (st_calls s mn cu pr ct) = wsum (fun y => LB y + blx y) (st_upd mn b cu pr ct) - wsum (fun y => LB y + blx y) b.
Proof.
  intros mn cu pr ct b L NN Hcu Hmn Hct Hs.
  pose proof (bsum_ge b) as BG.
  assert (BLX : blx cu = 0) by (unfold blx, REP_3_6, REPZ_3_10, REPZ_11_138; destruct (Z.eqb_spec cu 16); [lia|]; destruct (Z.eqb_spec cu 17); [lia|]; destruct (Z.eqb_spec cu 18); [lia|]; reflexivity).
  assert (B16 : blx 16 = 2) by reflexivity. assert (B17 : blx 17 = 3) by reflexivity. assert (B18 : blx 18 = 7) by reflexivity.
  set (w := fun y => LB y + blx y).
  assert (Wy : forall y, w y = LB y + blx y) by reflexivity.
  unfold st_calls, st_upd, blc, REP_3_6, REPZ_3_10, REPZ_11_138.
  destruct (Z.ltb_spec ct mn).
  - rewrite sumlen_repeat. rewrite wsum_set by lia. rewrite wrap16_id by (pose proof (NN cu); pose proof (BG cu NN ltac:(lia)); lia).
    rewrite Wy, BLX. replace (Z.of_nat (Z.to_nat ct)) with ct by lia. unfold LB. lia.
  - destruct (Z.eqb_spec cu 0); cbn [negb].
    + destruct (Z.leb_spec ct 10); cbn [sumlen app].
      * rewrite wsum_set by lia. rewrite wrap16_id by (pose proof (NN 17); pose proof (BG 17 NN ltac:(lia)); lia). rewrite Wy, B17. unfold LB. lia.
      * rewrite wsum_set by lia. rewrite wrap16_id by (pose proof (NN 18); pose proof (BG 18 NN ltac:(lia)); lia). rewrite Wy, B18. unfold LB. lia.
    + destruct (Z.eqb_spec cu pr); cbn [negb sumlen app].
      * rewrite wsum_set by lia. rewrite wrap16_id by (pose proof (NN 16); pose proof (BG 16 NN ltac:(lia)); lia). rewrite Wy, B16. unfold LB. lia.
      * pose proof (NN cu) as N1. pose proof (BG cu NN ltac:(lia)) as G1. pose proof (NN 16) as N2. pose proof (BG 16 NN ltac:(lia)) as G2.
        rewrite (wrap16_id (arr_get b cu + 1)) by lia.
        rewrite wsum_set; [| rewrite arr_len_set; exact L| lia].
        rewrite arr_get_set_other by lia. rewrite (wrap16_id (arr_get b 16 + 1)) by lia.
        rewrite wsum_set by lia. rewrite !Wy, BLX, B16. unfold LB. lia.
Qed.
End Emit.

Lemma emits_ext_upto : forall f lens lens' mc n p q c mx mn, 0 <= n ->
  (forall i, 1 <= i <= mc + 1 -> lens i = lens' i) ->
  emits f lens mc n p q c mx mn = emits f lens' mc n p q c mx mn.
Proof.
  induction f as [|f IH]; intros lens lens' mc n p q c mx mn Hn H; cbn; [reflexivity|].
  destruct (Z.leb_spec n mc); [|reflexivity]. rewrite <- (H (n + 1)) by lia.
  destruct ((c + 1 <? mx) && (q =? lens (n + 1))); [apply IH; [lia| exact H]|].
  destruct (tree_counts q (lens (n + 1))). f_equal. apply IH; [lia| exact H].
Qed.

Lemma emits_bits : forall s f lens mc n p q c mx mn b,
  arr_len b = 39 -> bnn b -> 0 <= c -> 0 <= n -> (mn = 3 \/ mn = 4) ->
  (forall i, 0 <= i <= mc -> 0 <= lens i <= 15) -> (n <= mc -> q = lens n) ->
  bsum b + c + (mc + 1 - n) < 65536 ->
  let E := emits f lens mc n p q c mx mn in
  let b' := fold_left em_upd E b in
  sumlen (flat_map (em_calls s) E) = wsum (fun y => Len s TB y + blx y) b' - wsum (fun y => Len s TB y + blx y) b
  /\ arr_len b' = 39 /\ bnn b' /\ bsum b' <= bsum b + c + Z.max 0 (mc + 1 - n)
  /\ (forall j, arr_get b j <= arr_get b' j).
Proof.
  intros s. induction f as [|f IH]; intros lens mc n p q c mx mn b L NN Hc Hn Hmn HL Hq Hs.
  - cbn. repeat split; auto; try lia; try (intros; lia).
  - cbn [emits]. destruct (Z.leb_spec n mc); [| cbn; repeat split; auto; try lia; try (intros; lia)]. cbv zeta.
    specialize (Hq ltac:(lia)). pose proof (HL n ltac:(lia)) as HLn.
    destruct ((c + 1 <? mx) && (q =? lens (n + 1))).
    + destruct (IH lens mc (n + 1) p (lens (n + 1)) (c + 1) mx mn b L NN ltac:(lia) ltac:(lia) Hmn HL ltac:(intros; reflexivity) ltac:(lia))
        as (A1 & A2 & A3 & A4 & A5). cbv zeta in *. repeat split; auto. lia.
    + destruct (tree_counts q (lens (n + 1))) as [mx' mn'] eqn:TC.
      pose proof (tree_counts_range _ _ _ _ TC) as [_ Hmn'].
      cbn [flat_map fold_left]. rewrite sumlen_app.
      pose proof (st_upd_ok mn b q p (c + 1) L NN ltac:(subst q; lia) Hmn ltac:(lia) ltac:(lia)) as (L1 & NN1 & S1 & M1).
      pose proof (emit_bits s mn q p (c + 1) b L NN ltac:(subst q; lia) Hmn ltac:(lia) ltac:(lia)) as EB.
      destruct (IH lens mc (n + 1) q (lens (n + 1)) 0 mx' mn' (st_upd mn b q p (c + 1)) L1 NN1 ltac:(lia) ltac:(lia) Hmn' HL ltac:(intros; reflexivity) ltac:(lia))
        as (A1 & A2 & A3 & A4 & A5). cbv zeta in *.
      unfold em_calls at 1. unfold em_upd at 1 2 3 4. cbn [fold_left] in *.
      split; [rewrite EB, A1; unfold em_upd; lia|]. split; [exact A2|]. split; [exact A3|]. split; [unfold em_upd in *; lia|].
      intros j. specialize (M1 j). specialize (A5 j). unfold em_upd in *. lia.
Qed.



Definition scan_E (s : deflate_state) (t : tree_id) (mc : Z) : list (Z * Z * Z * Z) :=
  let s1 := set_Len s t (mc + 1) 65535 in
  emits (Z.to_nat (mc + 1)) (Len s1 t) mc 0 (-1) (Len s1 t 0) 0
        (if Len s1 t 0 =? 0 then 138 else 7) (if Len s1 t 0 =? 0 then 3 else 4).

Theorem scan_send : forall s t mc,
  0 <= mc -> mc + 1 < arr_len (tree_dl s t) -> tree_lens s ->
  bnn (ds_bl_tree_fc s) -> (forall i, 0 <= i <= mc -> 0 <= Len s t i <= 15) ->
  bsum (ds_bl_tree_fc s) + (mc + 1) < 65536 ->
  exists b', let E := scan_E s t mc in
    scan_tree s t mc = set_bl_tree_fc (set_Len s t (mc + 1) 65535) b'
    /\ arr_len b' = 39 /\ bnn b' /\ bsum b' <= bsum (ds_bl_tree_fc s) + (mc + 1)
    /\ (forall j, arr_get (ds_bl_tree_fc s) j <= arr_get b' j)
    /\ forall s', (forall i, 0 <= i <= mc + 1 -> Len s' t i = Len (set_Len s t (mc + 1) 65535) t i) ->
         send_tree s' t mc = sbs_run s' (flat_map (em_calls s') E)
         /\ sumlen (flat_map (em_calls s') E)
              = wsum (fun y => Len s' TB y + blx y) b' - wsum (fun y => Len s' TB y + blx y) (ds_bl_tree_fc s).
Proof.
  intros s t mc Hmc Hmc1 TL NN L15 BS.
  set (s1 := set_Len s t (mc + 1) 65535).
  assert (LB : arr_len (ds_bl_tree_fc s) = 39) by (unfold tree_lens in TL; tauto).
  assert (B1 : ds_bl_tree_fc s1 = ds_bl_tree_fc s) by (subst s1; unfold set_Len, set_Dad; destruct t; reflexivity).
  assert (L1 : forall i, 0 <= i <= mc -> Len s1 t i = Len s t i).
  { intros i Hi. subst s1. rewrite Len_set_Len by lia. destruct (Z.eqb_spec (mc + 1) i); [lia| reflexivity]. }
  assert (L0 : Len s t 0 = Len s1 t 0) by (rewrite L1 by lia; reflexivity).
  set (mx := if Len s1 t 0 =? 0 then 138 else 7). set (mn := if Len s1 t 0 =? 0 then 3 else 4).
  set (E := emits (Z.to_nat (mc + 1)) (Len s1 t) mc 0 (-1) (Len s1 t 0) 0 mx mn).
  assert (Hmn : mn = 3 \/ mn = 4) by (subst mn; destruct (Len s1 t 0 =? 0); lia).
  exists (fold_left em_upd E (ds_bl_tree_fc s)). change (scan_E s t mc) with E. cbv zeta.
  destruct (emits_bits s (Z.to_nat (mc + 1)) (Len s1 t) mc 0 (-1) (Len s1 t 0) 0 mx mn (ds_bl_tree_fc s)
              LB NN ltac:(lia) ltac:(lia) Hmn ltac:(intros i Hi; rewrite L1 by lia; apply L15; lia) ltac:(intros; reflexivity) ltac:(lia))
    as (_ & LB' & NN' & BS' & GR). fold E in LB', NN', BS', GR.
  split.
  { assert (SE : forall f mc0 n p q c mx0 mn0, scan_tree_loop f s1 t mc0 n p q c mx0 mn0
              = set_bl_tree_fc s1 (fold_left em_upd (emits f (Len s1 t) mc0 n p q c mx0 mn0) (ds_bl_tree_fc s))).
    { intros. rewrite <- B1, <- scan_emits, sbf_self. reflexivity. }
    unfold scan_tree. rewrite L0. fold s1. subst mx mn E. destruct (Len s1 t 0 =? 0); apply SE. }
  split; [exact LB'|]. split; [exact NN'|]. split; [lia|]. split; [exact GR|].
  intros s' LEN.
  assert (L0' : Len s' t 0 = Len s1 t 0) by (apply LEN; lia).
  destruct (emits_bits s' (Z.to_nat (mc + 1)) (Len s1 t) mc 0 (-1) (Len s1 t 0) 0 mx mn (ds_bl_tree_fc s)
              LB NN ltac:(lia) ltac:(lia) Hmn ltac:(intros i Hi; rewrite L1 by lia; apply L15; lia) ltac:(intros; reflexivity) ltac:(lia))
    as (SB & _). fold E in SB.
  split; [| exact SB].
  unfold send_tree. rewrite L0'.
  subst mx mn E. destruct (Len s1 t 0 =? 0);
    (rewrite send_emits by lia; rewrite (emits_ext_upto _ (Len s' t) (Len s1 t)) by (lia || (intros; apply LEN; lia)); reflexivity).
Qed.

Lemma sat_loop_sbs : forall f s blcodes rank, 0 <= rank ->
  send_all_trees_loop f s blcodes rank
  = sbs_run s (map (fun r => (Len s TB (arr_get bl_order_a r), 3)) (ziota rank (Nat.min f (Z.to_nat (blcodes - rank))))).
Proof.
  induction f as [|f IH]; intros s blcodes rank Hr; [reflexivity|].
  cbn [send_all_trees_loop]. destruct (Z.ltb_spec rank blcodes).
  - replace (Nat.min (S f) (Z.to_nat (blcodes - rank))) with (S (Nat.min f (Z.to_nat (blcodes - (rank + 1))))) by lia.
    cbn [ziota map sbs_run]. rewrite IH by lia.
    f_equal. apply map_ext. intros r. rewrite sb_Len. reflexivity.
  - replace (Nat.min (S f) (Z.to_nat (blcodes - rank))) with 0%nat by lia. reflexivity.
Qed.

Lemma sumlen_map3 : forall (g : Z -> Z) l, sumlen (map (fun r => (g r, 3)) l) = 3 * Z.of_nat (length l).
Proof. induction l; cbn [map sumlen length]; [lia|]. rewrite IHl, Nat2Z.inj_succ. lia. Qed.

Theorem send_all_trees_sbs : forall s lcodes dcodes blcodes EL ED,
  0 <= blcodes <= 19 ->
  (forall s1, (forall t n, Len s1 t n = Len s t n) -> (forall n, Code s1 TB n = Code s TB n) ->
      send_tree s1 TL (lcodes - 1) = sbs_run s1 (flat_map (em_calls s1) EL)
      /\ send_tree s1 TD (dcodes - 1) = sbs_run s1 (flat_map (em_calls s1) ED)) ->
  send_all_trees s lcodes dcodes blcodes
  = sbs_run s ([(lcodes - 257, 5); (dcodes - 1, 5); (blcodes - 4, 4)]
               ++ map (fun r => (Len s TB (arr_get bl_order_a r), 3)) (ziota 0 (Z.to_nat blcodes))
               ++ flat_map (em_calls s) EL ++ flat_map (em_calls s) ED)
  /\ sumlen ([(lcodes - 257, 5); (dcodes - 1, 5); (blcodes - 4, 4)]
               ++ map (fun r => (Len s TB (arr_get bl_order_a r), 3)) (ziota 0 (Z.to_nat blcodes))
               ++ flat_map (em_calls s) EL ++ flat_map (em_calls s) ED)
     = 14 + 3 * blcodes + sumlen (flat_map (em_calls s) EL) + sumlen (flat_map (em_calls s) ED).
Proof.
  intros s lcodes dcodes blcodes EL ED Hbl ST.
  assert (EMC : forall s1 E, (forall t n, Len s1 t n = Len s t n) -> (forall n, Code s1 TB n = Code s TB n) ->
            flat_map (em_calls s1) E = flat_map (em_calls s) E).
  { intros s1 E HL HC. induction E as [|e E IH]; cbn; [reflexivity|]. rewrite IH. f_equal.
    destruct e as [[[mn cu] pr] ct]. unfold em_calls, st_calls, blc. rewrite !HL, !HC. reflexivity. }
  split.
  - unfold send_all_trees. rewrite !sbs_run_app. cbn [sbs_run].
    set (s3 := send_bits (send_bits (send_bits s (lcodes - 257) 5) (dcodes - 1) 5) (blcodes - 4) 4).
    assert (L3 : forall t n, Len s3 t n = Len s t n) by (intros; subst s3; rewrite !sb_Len; reflexivity).
    assert (C3 : forall n, Code s3 TB n = Code s TB n) by (intros; subst s3; rewrite !sb_Code; reflexivity).
    rewrite sat_loop_sbs by lia. replace (Nat.min 19 (Z.to_nat (blcodes - 0))) with (Z.to_nat blcodes) by lia.
    rewrite (map_ext _ (fun r => (Len s TB (arr_get bl_order_a r), 3))) by (intros; rewrite L3; reflexivity).
    set (s4 := sbs_run s3 _).
    assert (L4 : forall t n, Len s4 t n = Len s t n) by (intros; subst s4; rewrite sbs_Len; apply L3).
    assert (C4 : forall n, Code s4 TB n = Code s TB n) by (intros; subst s4; rewrite sbs_Code; apply C3).
    destruct (ST s4 L4 C4) as [E1 _]. rewrite E1, (EMC s4 EL L4 C4).
    set (s5 := sbs_run s4 _).
    assert (L5 : forall t n, Len s5 t n = Len s t n) by (intros; subst s5; rewrite sbs_Len; apply L4).
    assert (C5 : forall n, Code s5 TB n = Code s TB n) by (intros; subst s5; rewrite sbs_Code; apply C4).
    destruct (ST s5 L5 C5) as [_ E2]. rewrite E2, (EMC s5 ED L5 C5). reflexivity.
  - rewrite !sumlen_app. cbn [sumlen]. rewrite sumlen_map3, ziota_length. lia.
Qed.
