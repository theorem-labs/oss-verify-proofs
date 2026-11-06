(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFhh.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma RIx_open : forall U pp cc bb s b t,
RIx U pp cc bb s [] (b :: t) [] ->
RIx U pp cc bb s (b_items b) t [b_self b] /\ (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Proof.
intros U pp cc bb s b t (W & IT & ND & BL & SF & NDS & RM). cbn [app flat_map map] in IT, ND, SF, NDS, RM.
inversion BL as [|b0 P0 BLb BLP]; subst. split; [|exact BLb].
unfold RIx. cbn [app]. split; [exact W|]. split; [exact IT|]. split; [exact ND|]. split; [exact BLP|]. split; [exact SF|]. split; [exact NDS|].
cbn [length app] in RM |- *. rewrite ?length_map in RM |- *. eapply fa_room_xfer; [exact RM | rewrite ?length_map; lia | lia].
Qed.
Lemma RIx_head : forall U pp cc bb s k its P selfs,
RIx U pp cc bb s (k :: its) P selfs ->
WfP U pp cc bb s /\ In k (st_chunks s) /\ ck_state k = CQuarantined /\ ~ In (ck_beg k) (map ck_beg (q_items s)).
Proof.
intros U pp cc bb s k its P selfs (W & IT & ND & _). inversion IT as [|k0 rest [Hk Hst] ITr]; subst.
split; [exact W|]. split; [exact Hk|]. split; [exact Hst|].
cbn [app map] in ND. inversion ND; subst. intros Hin. match goal with H : ~ In (ck_beg k) _ |- _ => apply H end.
rewrite map_app. apply in_app_iff. right. exact Hin.
Qed.
Lemma RIx_rc_step : forall U pp cc bb s k its P selfs ns s1,
RIx U pp cc bb s (k :: its) P selfs -> recycle_post U pp cc bb s k ns (tt, s1) ->
RIx U pp cc bb s1 its P selfs /\ fframe s s1 /\ st_qthread s1 = st_qthread s /\ st_qglobal s1 = st_qglobal s /\ unq s1 = unq s - ck_n k.
Proof.
intros U pp cc bb s k its P selfs ns s1 RX RP.
destruct RX as (W & IT & ND & BL & SF & NDS & RM). inversion IT as [|k0 rest [Hk Hst] ITr]; subst.
pose proof (recycle_post_fframe U pp cc bb s k ns _ Hst RP) as FF. unfold recycle_post in RP. cbn [fst snd] in FF, RP |- *.
destruct RP as (W1 & (l1 & l2 & E & E1) & Rqt & Rqg & Rnev & Rfs & Rdep & SE & AU & CE & MF & LEN).
assert (EQI : q_items s1 = q_items s) by (unfold q_items, all_batches; rewrite Rqt, Rqg; reflexivity).
pose proof (unq_del s s1 l1 k l2 E E1 Hst Rqt Rqg) as UQ1.
cbn [app map] in ND. inversion ND as [|b0 rest0 Hnk NDr]; subst.
split; [|split; [exact FF | split; [exact Rqt | split; [exact Rqg | exact UQ1]]]].
unfold RIx. split; [exact W1|]. split.
{ apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) ITr k' Hk') as [H1 H2]. split; [|exact H2].
rewrite E1. rewrite E in H1. apply in_app_iff in H1 as [H1|[<-|H1]]; [apply in_app_iff; left; exact H1 | exfalso | apply in_app_iff; right; exact H1].
apply Hnk. rewrite map_app. apply in_app_iff. left. apply in_map. exact Hk'. }
split; [rewrite EQI; exact NDr|]. split; [exact BL|]. split.
{ eapply Forall_impl; [|exact SF]. cbv beta. intros z (Z1 & Z2 & Z3). rewrite AU by (unfold kBatchClass; lia).
split; [exact Z1 | split; [exact Z2|]]. intros Hin. exact (Z3 (CE kBatchClass _ ltac:(unfold kBatchClass; lia) Hin)). }
split; [exact NDS|].
rewrite AU, LEN, Rnev by (unfold kBatchClass; lia). eapply fa_room_xfer; [exact RM | apply Z.le_refl | apply MF; unfold kBatchClass; lia].
Qed.
Lemma RIx_cd_pre : forall U pp cc bb s P z selfs,
RIx U pp cc bb s [] P (z :: selfs) ->
WfP U pp cc bb s /\ 0 <= z - region_off kBatchClass < rg_alloc_user (reg s kBatchClass) /\
(z - region_off kBatchClass) mod class_size kBatchClass = 0 /\ ~ In (z - region_off kBatchClass) (class_elems s kBatchClass) /\
4 * (Z.of_nat (length (class_elems s kBatchClass)) + 1 + (cc + bb + 2 * (EV_MAX - st_nev s))) <= rg_mapped_fa (reg s kBatchClass).
Proof.
intros U pp cc bb s P z selfs (W & IT & ND & BL & SF & NDS & RM). cbn [app] in SF, RM.
inversion SF as [|z0 l0 (Z1 & Z2 & Z3) SFP]; subst.
split; [exact W|]. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|].
destruct RM as [Z0|R]; [lia|]. cbn [length] in R. lia.
Qed.
Lemma RIx_cd_step : forall U pp cc bb s t z ns s2,
RIx U pp cc bb s [] t [z] -> cache_dealloc_post U pp cc bb s kBatchClass (z - region_off kBatchClass) ns (tt, s2) ->
RIx U pp cc bb s2 [] t [] /\ fframe s s2 /\ st_qthread s2 = st_qthread s /\ st_qglobal s2 = st_qglobal s /\ unq s2 = unq s /\ st_chunks s2 = st_chunks s.
Proof.
intros U pp cc bb s t z ns s2 RX CP.
destruct RX as (W1 & IT1 & ND1 & BL1 & SF1 & NDS1 & RM1). cbn [app] in IT1, ND1. cbn [app length fst snd] in RM1. cbn [fst snd app] in SF1.
inversion SF1 as [|z0 l0 (Z1 & Z2 & Z3) SFP]; subst. inversion NDS1 as [|z1 l1 Hnself NDSP]; subst.
pose proof (cache_dealloc_post_fframe _ _ _ _ _ _ _ _ _ CP) as FF2. cbn [fst snd] in FF2.
destruct CP as (W2 & RO2 & AU2 & CE2 & MF2 & LEN2). cbn [snd] in W2, RO2, AU2, CE2, MF2, LEN2.
destruct RO2 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
pose proof (unq_same s s2 R1 R5 R6) as UQ2.
split; [|split; [exact FF2 | split; [exact R5 | split; [exact R6 | split; [exact UQ2 | exact R1]]]]].
unfold RIx. cbn [app]. split; [exact W2|]. split; [rewrite R1; exact IT1|]. split.
{ replace (q_items s2) with (q_items s) by (unfold q_items, all_batches; rewrite R5, R6; reflexivity). exact ND1. }
split; [exact BL1|]. split.
{ apply Forall_forall. intros y Hy. pose proof (proj1 (Forall_forall _ _) SFP y Hy) as (Y1 & Y2 & Y3).
rewrite AU2 by (unfold kBatchClass; lia). split; [exact Y1 | split; [exact Y2|]].
intros Hin. destruct (CE2 kBatchClass _ ltac:(unfold kBatchClass; lia) Hin) as [[Ez _]|Hin'].
- apply Hnself. replace z with y by lia. exact Hy.
- exact (Y3 Hin'). }
split; [exact NDSP|].
rewrite AU2, (LEN2 kBatchClass), R10 by (unfold kBatchClass; lia). rewrite Z.eqb_refl.
eapply fa_room_xfer; [exact RM1 | rewrite length_map; cbn [length]; lia | apply MF2; unfold kBatchClass; lia].
Qed.
Lemma RIx_nil : forall U pp cc bb s, RIx U pp cc bb s [] [] [] -> WfP U pp cc bb s.
Proof. intros U pp cc bb s (W & _). exact W. Qed.
Lemma aowned_del_back : forall B ly s s' l1 k l2, st_chunks s = l1 ++ k :: l2 -> st_chunks s' = l1 ++ l2 -> ck_state k = CQuarantined ->
st_fs s' = st_fs s -> forall a, aowned B ly s' a -> aowned B ly s a.
Proof.
intros B ly s s' l1 k l2 E E' Hst Hfs a [OWN NC].
assert (SE : forall e, In e (sec_extents ly s') -> In e (sec_extents ly s)).
{ intros e He. unfold sec_extents in He |- *. rewrite E' in He. rewrite E. apply in_flat_map in He as (y & Hy & He). apply in_flat_map. exists y. split; [|exact He].
apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]. }
split.
- destruct OWN as [O|[O|[O|[O|O]]]]; [left; exact O | right; left; exact O | right; right; left; exact O | |].
+ right; right; right; left. apply Exists_exists in O as (e & He & Ha). apply Exists_exists. exists e. split; [exact (SE e He) | exact Ha].
+ right; right; right; right. apply Exists_exists in O as (e & He & Ha). apply Exists_exists. exists e. split; [|exact Ha].
rewrite !in_app_iff in He |- *. destruct He as [He|[He|He]]; [tauto | right; left; exact (SE e He) | tauto].
- intros C. apply NC. destruct C as [(y & Hy & Hal & Hr)|(cp & Hcp & Hr)].
+ left. exists y. split; [|split; [exact Hal | exact Hr]]. rewrite E'. rewrite E in Hy.
apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply in_app_iff; left; exact Hy | rewrite Hst in Hal; discriminate | apply in_app_iff; right; exact Hy].
+ right. exists cp. split; [|exact Hr]. unfold frames in Hcp |- *. rewrite Hfs. exact Hcp.
Qed.
Lemma aowned_same_chunks : forall B ly s s', st_chunks s' = st_chunks s -> st_fs s' = st_fs s -> forall a, aowned B ly s' a <-> aowned B ly s a.
Proof.
intros B ly s s' E Hfs a.
assert (SE : sec_extents ly s' = sec_extents ly s) by (unfold sec_extents; rewrite E; reflexivity).
assert (FR : frames s' = frames s) by (unfold frames; rewrite Hfs; reflexivity).
unfold aowned, aclient_byte. rewrite SE, FR, E. tauto.
Qed.
Lemma aowned_rc_back : forall B ly U pp cc bb s k ns s1, ck_state k = CQuarantined -> recycle_post U pp cc bb s k ns (tt, s1) ->
forall a, aowned B ly s1 a -> aowned B ly s a.
Proof.
intros B ly U pp cc bb s k ns s1 Hst RP a. unfold recycle_post in RP. cbn [snd] in RP. destruct RP as (_ & (l1 & l2 & E & E1) & _ & _ & _ & Hfs & _).
exact (aowned_del_back B ly s s1 l1 k l2 E E1 Hst Hfs a).
Qed.
Lemma aowned_cd_same : forall B ly U pp cc bb s c x ns s2, cache_dealloc_post U pp cc bb s c x ns (tt, s2) ->
forall a, aowned B ly s2 a <-> aowned B ly s a.
Proof.
intros B ly U pp cc bb s c x ns s2 CP a. destruct CP as (_ & RO & _). cbn [snd] in RO. destruct RO as (R1 & _ & _ & _ & _ & _ & R7 & _).
exact (aowned_same_chunks B ly s s2 R1 R7 a).
Qed.
