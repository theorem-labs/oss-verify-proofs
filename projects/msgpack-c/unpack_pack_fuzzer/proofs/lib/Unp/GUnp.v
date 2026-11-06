(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Ops GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Cost Acct.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GU.

Section Owned.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.

Lemma owned_byte_props : forall A LB m mo md g ws ob a,
  aw_holds segs IMGX AW A LB ws m mo -> windows_wf ws LB (aw_ceiling segs IMGX AW mo) -> own_ok g LB -> wins_ok md g ws ->
  In ob (owned g) -> in_iv ob a -> safe md g ws a ->
  (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws ws a /\ m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None.
Proof.
  intros A LB m mo md g ws ob a HA WF O W Hob Ha SF.
  pose proof (proj1 O ob Hob) as HLB.
  destruct (aw_blocks_ok segs IMGX AW A LB _ m mo ob HA HLB) as (B1 & B2 & B3 & B4 & B5).
  destruct (aw_user_ok segs IMGX AW A LB _ m mo ob a HA HLB Ha) as [MAT NS].
  unfold in_iv in Ha.
  split; [lia|]. split; [exact (B5 a Ha)|]. split; [| split; [exact MAT| exact NS]].
  intros X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
  destruct (Z.eq_dec (w_kind w) K_STACK) as [K|NK].
  - pose proof (proj1 (Forall_forall _ _) WF w Hw) as (_ & _ & _ & [[_ S]|[[K' _]|[K' _]]]).
    + unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. lia.
    + rewrite K in K'. discriminate.
    + rewrite K in K'. unfold K_SUB, K_STACK in K'. lia.
  - destruct (proj1 (Forall_forall _ _) W w Hw NK) as [[_ D]|[NB SO]].
    + exact (D ob Hob a Hin Ha).
    + exact (SF w Hw SO Hin).
Qed.

Lemma safe_level_no4 : forall md g LB ws l a,
  pure_ok g -> own_ok g LB -> (forall w, In w ws -> w_kind w <> K_SLOT) ->
  In l (u_levels g) -> lv_P l <= a < lv_P l + lv_bytes l -> safe md g ws a.
Proof.
  intros md g LB ws l a P O N4 Hl Ha w Hw SO Hin. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin.
  pose proof (pf g P) as (VC & EC & SC & VV & EV & SV & LV & LA & ZV).
  destruct (level_array g P l Hl) as (V & A & G1 & G2 & G4 & c & Hc & IC).
  unfold sub_ok in SO. cbv zeta in SO.
  destruct SO as [(KD & I1 & I2 & I3)|[(KD & I1 & I2 & I3)|[(KD & lD & HlD & I2 & I3)|(KD & I2 & I3)]]].
  - pose proof (disj_cc g LB O c Hc) as D. unfold in_chunk, chunk_lo, chunk_hi, v_end, v_capend, v_bytes, rdisj, CHUNK_HDR in *. nia.
  - pose proof (disj_vc g LB O c Hc) as D. unfold in_chunk, chunk_lo, chunk_hi, v_end, v_capend, v_bytes, rdisj, CHUNK_HDR in *. nia.
  - exact (N4 w Hw KD).
  - pose proof (level_geom l V) as (_ & _ & _ & _ & _ & G6).
    pose proof (in_alloc_fresh_disj (u_zone g) (lv_P l) (lv_bytes l) (w_lo w) (w_len w) ZV ltac:(unfold OBJ_SIZE in G6; lia) A I2 I3) as D.
    unfold rdisj in D. lia.
Qed.

Lemma level_block : forall g LB l, pure_ok g -> own_ok g LB -> In l (u_levels g) ->
  exists c, In c (z_chunks (u_zone g)) /\ In (chunk_block c) (owned g) /\
    forall a, lv_P l <= a < lv_P l + lv_bytes l -> in_iv (chunk_block c) a.
Proof.
  intros g LB l P O Hl. destruct (level_array g P l Hl) as (V & A & G1 & G2 & G4 & c & Hc & IC).
  exists c. split; [exact Hc|]. split; [exact (owned_chunk g c Hc)|].
  intros a Ha. unfold in_iv, chunk_block, in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
Qed.

End Owned.

Lemma range_ok_mono_levels : forall z ls ls' r,
  (forall l', In l' ls' -> exists l, In l ls /\ lv_slot l <= lv_slot l' /\ lv_slot l' + lv_unfilled l' <= lv_slot l + lv_unfilled l) ->
  range_ok z ls r -> range_ok z ls' r.
Proof.
  intros z ls ls' r SUB (R0 & A & D). split; [exact R0|]. split; [exact A|]. intros l' Hl'.
  destruct (SUB l' Hl') as (l & Hl & H1 & H2). pose proof (D l Hl) as X. unfold rdisj in *. lia.
Qed.

Lemma bodies_ok_mono_levels : forall z ls ls' o,
  (forall l', In l' ls' -> exists l, In l ls /\ lv_slot l <= lv_slot l' /\ lv_slot l' + lv_unfilled l' <= lv_slot l + lv_unfilled l) ->
  bodies_ok z ls o -> bodies_ok z ls' o.
Proof.
  intros z ls ls' o SUB B. unfold bodies_ok in *. eapply Forall_impl; [|exact B]. intros r. apply range_ok_mono_levels. exact SUB.
Qed.

Lemma completed_ok_item : forall m z ls l l' o,
  Forall level_valid (ls ++ [l]) -> levels_alloc z (ls ++ [l]) -> consume_top l = CS_Ret l' ->
  completed_ok m z (ls ++ [l]) ->
  tree_at m z (lv_slot l) o -> (forall c, In c (tl (obj_cells (lv_slot l) o)) -> Inv.cell_ok z (ls ++ [l]) c) -> bodies_ok z (ls ++ [l]) o ->
  completed_ok m z (ls ++ [l']).
Proof.
  intros m z ls l l' o V LA Hc CW Ht Htl Hb.
  apply Forall_app in V. destruct V as [Vls Vl]. inversion Vl as [|l0 l1 Vl' _]; subst. clear Vl.
  pose proof (consume_top_ret l l' Hc Vl') as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof (level_geom l Vl') as G. pose proof (level_geom l' S5) as G'. assert (HO : OBJ_SIZE = 24) by reflexivity.
  assert (SUB : forall x', In x' (ls ++ [l']) -> exists x, In x (ls ++ [l]) /\ lv_slot x <= lv_slot x' /\ lv_slot x' + lv_unfilled x' <= lv_slot x + lv_unfilled x).
  { intros x' Hx'. apply in_app_iff in Hx'. destruct Hx' as [Hx'|[<-|[]]].
    - exists x'. split; [apply in_app_iff; now left|lia].
    - exists l. split; [apply in_app_iff; right; now left|]. lia. }
  assert (ROOT : Inv.cell_ok z (ls ++ [l']) (lv_slot l)).
  { destruct LA as [A B]. split.
    - eapply in_alloc_sub; [apply A; apply in_app_iff; right; now left| lia | lia].
    - intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]]; [|unfold rdisj; lia].
      apply ForallOrdPairs_sub_snoc in B. destruct B as [_ B2]. apply Forall_forall with (x := x) in B2; [|exact Hx].
      apply Forall_forall with (x := x) in Vls; [|exact Hx]. pose proof (level_geom x Vls).
      unfold level_disj, rdisj in *. lia. }
  intros x Hx i Hi. apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]].
  - destruct (CW x ltac:(apply in_app_iff; now left) i Hi) as (ox & Hox & Hcx & Hbx). exists ox. split; [exact Hox|]. split.
    + intros c Hcc. eapply cell_ok_mono_levels; [exact SUB|]. now apply Hcx.
    + eapply bodies_ok_mono_levels; [exact SUB| exact Hbx].
  - rewrite S2. destruct (Z.lt_ge_cases i (lv_k l)) as [Hlt|Hge].
    + destruct (CW l ltac:(apply in_app_iff; right; now left) i ltac:(lia)) as (ox & Hox & Hcx & Hbx). exists ox. split; [exact Hox|]. split.
      * intros c Hcc. eapply cell_ok_mono_levels; [exact SUB|]. now apply Hcx.
      * eapply bodies_ok_mono_levels; [exact SUB| exact Hbx].
    + assert (Ei : i = lv_k l) by lia. subst i. replace (lv_P l + OBJ_SIZE * lv_k l) with (lv_slot l) by (unfold lv_slot; lia).
      exists o. split; [exact Ht|]. split.
      * intros c Hcc. rewrite obj_cells_hd in Hcc. destruct Hcc as [<-|Hcc]; [exact ROOT|].
        eapply cell_ok_mono_levels; [exact SUB|]. now apply Htl.
      * eapply bodies_ok_mono_levels; [exact SUB| exact Hb].
Qed.

Lemma collect_kids_b : forall m z (Q : Z -> Prop) (R : Z * Z -> Prop) K P,
  (forall i, 0 <= i < Z.of_nat K -> exists o, tree_at m z (P + OBJ_SIZE * i) o /\
       (forall c, In c (obj_cells (P + OBJ_SIZE * i) o) -> Q c) /\ (forall b, In b (obj_bodies o) -> R b)) ->
  exists kids, length kids = K /\ objs_at m P kids /\ trees_wf m z kids /\
    (forall c, In c (kids_cells P kids) -> Q c) /\ (forall b, In b (objs_bodies kids) -> R b).
Proof.
  intros m z Q R K. induction K as [|K IH]; intros P H.
  - exists []. cbn. repeat split; auto; intros c [].
  - destruct (H 0 ltac:(lia)) as (o & Ho & Hc & Hb). rewrite Z.mul_0_r, Z.add_0_r in Ho, Hc.
    destruct (IH (P + OBJ_SIZE)) as (kids & Hlen & Hat & Hwf & HQ & HR).
    { intros i Hi. destruct (H (i + 1) ltac:(lia)) as (o' & Ho' & Hc' & Hb').
      replace (P + OBJ_SIZE * (i + 1)) with (P + OBJ_SIZE + OBJ_SIZE * i) in Ho', Hc' by lia. eauto 6. }
    exists (o :: kids). cbn [length objs_at trees_wf kids_cells]. rewrite Hlen. repeat split; auto; try apply Ho.
    + intros c Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; auto.
    + intros b Hin. unfold objs_bodies in Hin. cbn [flat_map] in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; auto.
Qed.

Lemma complete_container_ok : forall m z ls l C,
  Forall level_valid (ls ++ [l]) -> levels_alloc z (ls ++ [l]) -> zone_valid z -> consume_top l = CS_Pop ->
  completed_ok m z (ls ++ [l]) ->
  (exists o, tree_at m z (lv_slot l) o /\ (forall c, In c (tl (obj_cells (lv_slot l) o)) -> Inv.cell_ok z (ls ++ [l]) c) /\
             bodies_ok z (ls ++ [l]) o) ->
  exists o, obj_type o = container_type (lv_t l) /\ obj_count o = lv_n l /\ obj_ptr o = lv_P l /\
    tree_wf m z o /\ kids_at m o /\
    (u32_at m C (container_type (lv_t l)) -> u32_at m (C + 8) (lv_n l) -> u64_at m (C + 16) (lv_P l) -> hdr_at m C o) /\
    (forall c, In c (tl (obj_cells C o)) -> Inv.cell_ok z ls c) /\ bodies_ok z ls o /\
    completed_ok m z ls /\ levels_alloc z ls /\ Forall level_valid ls.
Proof.
  intros m z ls l C V LA Vz Hc CW (o & Ht & Htl & Hb).
  apply Forall_app in V. destruct V as [Vls Vl]. inversion Vl as [|l0 l1 Vl' _]; subst. clear Vl.
  destruct (consume_top_pop l Hc) as [R1 NK]. pose proof (pop_full l Vl' R1 NK) as FULL. pose proof (level_geom l Vl') as G.
  assert (HO : OBJ_SIZE = 24) by reflexivity.
  assert (SUB : forall x', In x' ls -> exists x, In x (ls ++ [l]) /\ lv_slot x <= lv_slot x' /\ lv_slot x' + lv_unfilled x' <= lv_slot x + lv_unfilled x).
  { intros x' Hx'. exists x'. split; [apply in_app_iff; now left|lia]. }
  assert (ROOT : Inv.cell_ok z ls (lv_slot l)).
  { destruct LA as [A B]. split.
    - eapply in_alloc_sub; [apply A; apply in_app_iff; right; now left| lia | lia].
    - intros x Hx. apply ForallOrdPairs_sub_snoc in B. destruct B as [_ B2]. apply Forall_forall with (x := x) in B2; [|exact Hx].
      apply Forall_forall with (x := x) in Vls; [|exact Hx]. pose proof (level_geom x Vls). unfold level_disj, rdisj in *. lia. }
  destruct (collect_kids_b m z (Inv.cell_ok z ls) (range_ok z ls) (Z.to_nat (lv_k l + 1)) (lv_P l)) as (kids & Hlen & Hat & Hwf & Hcells & Hbods).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia. destruct (Z.lt_ge_cases i (lv_k l)) as [Hlt|Hge].
    - destruct (CW l ltac:(apply in_app_iff; right; now left) i ltac:(lia)) as (ox & Hox & Hcx & Hbx). exists ox. split; [exact Hox|]. split.
      + intros c Hcc. eapply cell_ok_mono_levels; [exact SUB|]. now apply Hcx.
      + intros b Hbb. eapply range_ok_mono_levels; [exact SUB|]. exact (proj1 (Forall_forall _ _) Hbx b Hbb).
    - assert (Ei : i = lv_k l) by lia. subst i. replace (lv_P l + OBJ_SIZE * lv_k l) with (lv_slot l) by (unfold lv_slot; lia).
      exists o. split; [exact Ht|]. split.
      + intros c Hcc. rewrite obj_cells_hd in Hcc. destruct Hcc as [<-|Hcc]; [exact ROOT|].
        eapply cell_ok_mono_levels; [exact SUB|]. now apply Htl.
      + intros b Hbb. eapply range_ok_mono_levels; [exact SUB|]. exact (proj1 (Forall_forall _ _) Hb b Hbb). }
  assert (Hlen' : Z.of_nat (length kids) = lv_k l + 1) by (rewrite Hlen, Z2Nat.id; lia).
  assert (Hne : kids <> []) by (intros ->; cbn in Hlen'; lia).
  assert (HPz : in_zone z (lv_P l) (OBJ_SIZE * Z.of_nat (length kids))).
  { rewrite Hlen'. destruct LA as [A _]. destruct Vz as (Vz1 & _ & _ & Vz4 & Vz5 & Vz6 & _).
    apply in_alloc_in_zone; [exact Vz1| lia |]. rewrite Z.mul_comm, FULL. apply A. apply in_app_iff. right; now left. }
  destruct Vl' as (W1 & W2 & W3 & W4 & W5).
  assert (REST : completed_ok m z ls /\ levels_alloc z ls /\ Forall level_valid ls).
  { split; [| split; [eapply levels_alloc_pop; exact LA| exact Vls]].
    intros x Hx i Hi. destruct (CW x ltac:(apply in_app_iff; now left) i Hi) as (ox & Hox & Hcx & Hbx). exists ox. split; [exact Hox|]. split.
    - intros c Hcc. eapply cell_ok_mono_levels; [exact SUB|]. now apply Hcx.
    - eapply bodies_ok_mono_levels; [exact SUB| exact Hbx]. }
  destruct (lv_t l) eqn:Et; [| exfalso; now apply NK |].
  -   exists (OArr (lv_P l) kids). unfold kids_at. cbn [obj_type obj_count obj_ptr container_type].
    assert (Hn : Z.of_nat (length kids) = lv_n l) by (rewrite Hlen'; unfold lv_k; rewrite Et; lia).
    split; [reflexivity|]. split; [exact Hn|]. split; [reflexivity|]. split; [| split; [exact Hat| split; [| split; [| split; [| exact REST]]]]].
    + apply tree_wf_arr. rewrite ?Hn. repeat split; auto; try lia; try tauto. now rewrite <- Hn.
    + intros A1 A2 A3. unfold hdr_at. cbn [obj_type]. rewrite Hn. auto.
    + intros c Hcc. rewrite obj_cells_arr in Hcc. cbn [tl] in Hcc. now apply Hcells.
    + unfold bodies_ok. rewrite obj_bodies_arr. apply Forall_forall. exact Hbods.
  -   exists (OMap (lv_P l) kids). unfold kids_at. cbn [obj_type obj_count obj_ptr container_type].
    assert (Hn : Z.of_nat (length kids) = 2 * lv_n l) by (rewrite Hlen'; unfold lv_k; rewrite Et; lia).
    assert (Hn2 : Z.of_nat (length kids) / 2 = lv_n l) by (rewrite Hn, Z.mul_comm; apply Z.div_mul; lia).
    assert (Hev : even_len kids = true). { apply even_len_spec. exists (Z.to_nat (lv_n l)). lia. }
    split; [reflexivity|]. split; [exact Hn2|]. split; [reflexivity|]. split; [| split; [exact Hat| split; [| split; [| split; [| exact REST]]]]].
    + apply tree_wf_map. rewrite ?Hn2. repeat split; auto; try lia; try tauto.
    + intros A1 A2 A3. unfold hdr_at. cbn [obj_type]. rewrite Hn2. auto.
    + intros c Hcc. rewrite obj_cells_map in Hcc. cbn [tl] in Hcc. now apply Hcells.
    + unfold bodies_ok. rewrite obj_bodies_map. apply Forall_forall. exact Hbods.
Qed.

Lemma container_depth_acct : forall m z ls l X o oc,
  level_valid l -> consume_top l = CS_Pop ->
  Acct.acct_ok m z (ls ++ [l]) X ->
  tree_at m z (lv_slot l) o -> (Cost.obj_depth o + length (ls ++ [l]) <= 1001)%nat ->
  obj_type oc = container_type (lv_t l) -> obj_count oc = lv_n l -> obj_ptr oc = lv_P l ->
  tree_wf m z oc -> kids_at m oc ->
  (Cost.obj_depth oc + length ls <= 1001)%nat /\ exists X', Acct.acct_ok m z ls X'.
Proof.
  intros m z ls l X o oc V Hc A Ht Hd TY CNT PTR TW KA.
  destruct (consume_top_pop l Hc) as [R1 NK]. pose proof (pop_full l V R1 NK) as FULL.
  destruct A as (oss & F & B & D & N). destruct (Acct.Forall2_snoc_inv _ ls l oss F) as (oss1 & os & -> & F1 & [Hlen Hk]).

  assert (KIDS : exists K, (forall i o', nth_error K i = Some o' -> tree_at m z (lv_P l + OBJ_SIZE * Z.of_nat i) o') /\
                           Cost.obj_depth oc = S (Cost.objs_depth K) /\ Z.of_nat (length K) = lv_k l + 1).
  { unfold lv_bytes in FULL. unfold lv_k in *.
    destruct oc; cbn [obj_type] in TY; try (exfalso; destruct (lv_t l); cbn in TY; discriminate TY).
    - exists kids. cbn [kids_at obj_ptr obj_count] in KA, PTR, CNT. apply tree_wf_arr in TW. destruct TW as (_ & _ & _ & T1). subst p.
      split; [intros i o' Hn; exact (Acct.objs_at_nth m z kids _ i o' KA T1 Hn)|]. split; [apply Cost.obj_depth_arr|].
      destruct (lv_t l); cbn [container_type per] in TY, FULL |- *; try discriminate TY.
      unfold OBJ_SIZE in FULL. lia.
    - exists kids. cbn [kids_at obj_ptr obj_count] in KA, PTR, CNT. apply tree_wf_map in TW. destruct TW as (E1 & _ & _ & _ & T1). subst p.
      split; [intros i o' Hn; exact (Acct.objs_at_nth m z kids _ i o' KA T1 Hn)|]. split; [apply Cost.obj_depth_map|].
      destruct (lv_t l); cbn [container_type per] in TY, FULL |- *; try discriminate TY; [exfalso; apply NK; reflexivity|].
      apply even_len_spec in E1. destruct E1 as [q Hq]. rewrite Hq in CNT |- *. rewrite Nat2Z.inj_mul in CNT |- *. change (Z.of_nat 2) with 2 in *.
      rewrite Z.mul_comm, Z.div_mul in CNT by lia. unfold OBJ_SIZE in FULL. lia. }
  destruct KIDS as (K & HK & DEPTH & HKlen).

  assert (HKeq : K = os ++ [o]).
  { apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length K)) as [Hi|Hi].
    - destruct (nth_error K i) as [x|] eqn:E; [|exfalso; apply (proj2 (nth_error_Some K i) Hi); exact E].
      pose proof (HK i x E) as Tx.
      destruct (Nat.lt_ge_cases i (length os)) as [Hi2|Hi2].
      + rewrite nth_error_app1 by exact Hi2. destruct (nth_error os i) as [y|] eqn:E2; [|exfalso; apply (proj2 (nth_error_Some os i) Hi2); exact E2].
        f_equal. pose proof (Hk i y E2) as Ty. unfold Acct.kid_addr in Ty. exact (Acct.tree_at_unique _ _ _ _ _ Tx Ty).
      + rewrite nth_error_app2 by exact Hi2. replace (i - length os)%nat with 0%nat by lia. cbn. f_equal.
        replace (Z.of_nat i) with (lv_k l) in Tx by lia. unfold lv_slot in Ht. exact (Acct.tree_at_unique _ _ _ _ _ Tx Ht).
    - destruct (nth_error K i) eqn:E; [exfalso; pose proof (Acct.nth_error_lt _ _ _ E); lia|].
      destruct (nth_error (os ++ [o]) i) eqn:E2; [exfalso; pose proof (Acct.nth_error_lt _ _ _ E2) as L2; rewrite length_app in L2; cbn in L2; lia| reflexivity]. }
  subst K. rewrite Cost.objs_depth_app, Acct.objs_depth_cons1 in DEPTH.
  pose proof (D (length oss1) os ltac:(rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity)) as D1.
  pose proof (Acct.Forall2_length' _ _ _ F1) as L1. rewrite length_app in Hd. cbn [length] in Hd.
  split; [lia|].
  rewrite !length_app, !map_app, !Acct.zsum_app in B. cbn [length map Acct.zsum fold_right] in B.
  apply Forall_app in N. destruct N as [N1 N2]. inversion N2; subst.
  exists X. exists oss1. split; [exact F1|]. split; [lia|]. split; [| exact N1].
  intros j os' Hn. apply D. rewrite nth_error_app1; [exact Hn|]. exact (Acct.nth_error_lt _ _ _ Hn).
Qed.

Definition vec_pop (v : vecg) : vecg := mkVec (v_begin v) (v_size v - 1) (v_cap v) (v_elt v).
Lemma vec_pop_valid : forall v, vec_valid v -> 1 <= v_size v -> vec_valid (vec_pop v) /\ v_end (vec_pop v) = v_end v - v_elt v.
Proof. intros v V H. unfold vec_valid, vec_pop, v_end in *; cbn. split; [lia|lia]. Qed.

Lemma cstk_at_app : forall m a l1 l2, cstk_at m a (l1 ++ l2) <-> cstk_at m a l1 /\ cstk_at m (a + 8 * Z.of_nat (length l1)) l2.
Proof.
  intros m a l1. revert a. induction l1 as [|l l1 IH]; intros a l2; cbn [app cstk_at length].
  - rewrite Z.mul_0_r, Z.add_0_r. tauto.
  - rewrite IH. rewrite Nat2Z.inj_succ. replace (a + 8 * Z.succ (Z.of_nat (length l1))) with (a + 8 + 8 * Z.of_nat (length l1)) by lia. tauto.
Qed.
Lemma vstk_at_app : forall m a l1 l2, vstk_at m a (l1 ++ l2) <-> vstk_at m a l1 /\ vstk_at m (a + 8 * Z.of_nat (length l1)) l2.
Proof.
  intros m a l1. revert a. induction l1 as [|l l1 IH]; intros a l2; cbn [app vstk_at length].
  - rewrite Z.mul_0_r, Z.add_0_r. tauto.
  - rewrite IH. rewrite Nat2Z.inj_succ. replace (a + 8 * Z.succ (Z.of_nat (length l1))) with (a + 8 + 8 * Z.of_nat (length l1)) by lia. tauto.
Qed.

Lemma completed_ok_push : forall m z z' ls t n P,
  t <> CT_MAP_VALUE -> zone_grows z z' ->
  (forall a k, 0 <= k -> in_alloc z a k -> rdisj a k P (lv_bytes (new_level t n P))) ->
  completed_ok m z ls -> completed_ok m z' (push_level ls t n P).
Proof.
  intros m z z' ls t n P Ht ZG FR CW l Hl i Hi. unfold push_level in Hl. apply in_app_iff in Hl as [Hl|[<-|[]]].
  - destruct (CW l Hl i Hi) as (o & T & C & B). exists o. split; [| split].
    + eapply tree_at_frame; [apply readable_mono_refl| exact ZG| intros c _; apply agree_on_refl| exact T].
    + intros c Hc. destruct (C c Hc) as [A D]. split; [exact (proj2 ZG _ _ A)|].
      intros x Hx. apply in_app_iff in Hx as [Hx|[<-|[]]]; [exact (D x Hx)|].
      rewrite (new_level_slot t n P Ht). unfold lv_unfilled. rewrite (new_level_slot t n P Ht). cbn [new_level lv_P].
      pose proof (FR c OBJ_SIZE ltac:(unfold OBJ_SIZE; lia) A) as X. unfold rdisj in *. lia.
    + unfold bodies_ok in *. eapply Forall_impl; [| exact B]. intros r (R0 & A & D). split; [exact R0|]. split; [exact (proj2 ZG _ _ A)|].
      intros x Hx. apply in_app_iff in Hx as [Hx|[<-|[]]]; [exact (D x Hx)|].
      rewrite (new_level_slot t n P Ht). unfold lv_unfilled. rewrite (new_level_slot t n P Ht). cbn [new_level lv_P].
      pose proof (FR (fst r) (snd r) R0 A) as X. unfold rdisj in *. lia.
  - rewrite (new_level_k t n P Ht) in Hi. lia.
Qed.

Lemma vec_push_end : forall v, v_end (vec_push v) = v_end v + v_elt v /\ v_begin (vec_push v) = v_begin v /\
  v_capend (vec_push v) = v_capend v /\ v_bytes (vec_push v) = v_bytes v /\ v_size (vec_push v) = v_size v + 1 /\
  v_cap (vec_push v) = v_cap v /\ v_elt (vec_push v) = v_elt v.
Proof. intros v. unfold vec_push, v_end, v_capend, v_bytes. cbn. repeat split; lia. Qed.

Lemma last_opt_snoc : forall (ls : list level) l, last_opt (ls ++ [l]) = Some l.
Proof. intros ls l. unfold last_opt. rewrite rev_app_distr. reflexivity. Qed.

End GU.
