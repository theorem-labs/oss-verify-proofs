(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YO0y.v; 234 of its 324 lines of code are new or changed and 87 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocPackMalloc.v, with its module paths changed; 127 of its 163 lines of code are new or changed and 288 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0y YO03 YO0m YO0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocSI AllocGS AllocMalloc AllocCount AllocPack AllocPackUPB AllocPackMallocN AllocPackMallocW AllocPackMallocC AllocPackMallocA AllocPackMalloc AllocPack3.
Import ListNotations.
Local Open Scope Z_scope.

Definition capsP (caps mc : list Z) : list Z := map (fun i => znth (Z.of_nat i) caps + znth (Z.of_nat i) mc) (seq 0 49).

Definition mis_lift (s : astate) (M : list (sptr * Z)) (L : list Z) : list Z :=
  map (fun i => znth (Z.of_nat i) L + (if (1 <=? Z.of_nat i) && (Z.of_nat i <? 48) then mis_in s M (Z.of_nat i) else 0))
    (seq 0 49).

Lemma znth_mapseq (f : Z -> Z) n k : 0 <= k < Z.of_nat n -> znth k (map (fun i => f (Z.of_nat i)) (seq 0 n)) = f k.
Proof.
  intros Hk. unfold znth. pose proof (map_nth (fun i => f (Z.of_nat i)) (seq 0 n) 0%nat (Z.to_nat k)) as E. cbv beta in E.
  rewrite (nth_indep _ 0 (f (Z.of_nat 0))) by (rewrite length_map, length_seq; lia).
  rewrite E, seq_nth by lia. cbn [Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma znth_capsP caps mc k : 0 <= k < 49 -> znth k (capsP caps mc) = znth k caps + znth k mc.
Proof. intros Hk. exact (znth_mapseq (fun z => znth z caps + znth z mc) 49 k Hk). Qed.

Lemma znth_lift s M L k : 0 <= k < 49 ->
  znth k (mis_lift s M L) = znth k L + (if (1 <=? k) && (k <? 48) then mis_in s M k else 0).
Proof.
  intros Hk. exact (znth_mapseq (fun z => znth z L + (if (1 <=? z) && (z <? 48) then mis_in s M z else 0)) 49 k Hk).
Qed.

Lemma nf3_eq caps mc caps' : (forall c, 0 <= c < 48 -> znth c caps' = znth c caps + znth c mc) ->
  forall k, (k <= 48)%nat -> nf_build caps' k = nf3_build caps mc k.
Proof.
  intros H. induction k as [|k IH]; intros Hk; [reflexivity|]. cbn [nf_build nf3_build]. rewrite IH by lia.
  f_equal. f_equal. unfold nf_next, nf3_next. rewrite (H (Z.of_nat k)) by lia. f_equal. f_equal. lia.
Qed.

Lemma NF_capsP caps mc : NF (capsP caps mc) = NF3 caps mc.
Proof. unfold NF, NF3. apply nf3_eq; [intros c Hc; apply znth_capsP; lia | lia]. Qed.

Lemma PKC3_iff X caps mc s : PKC3 X caps mc s <-> PKC X (capsP caps mc) s.
Proof. unfold PKC3, PKC. rewrite NF_capsP. tauto. Qed.

Lemma p3_flen {A} (f g : A -> bool) l : (forall x, In x l -> f x = true -> g x = true) ->
  (length (filter f l) <= length (filter g l))%nat.
Proof.
  induction l as [|x l IH]; intros H; cbn [filter]; [lia|].
  assert (IH' := IH (fun y Hy => H y (or_intror Hy))).
  destruct (f x) eqn:Ef; destruct (g x) eqn:Eg; cbn [length]; try lia.
  rewrite (H x (or_introl eq_refl) Ef) in Eg. discriminate.
Qed.

Lemma mis_in_nonneg s M c : 0 <= mis_in s M c.
Proof. unfold mis_in. lia. Qed.

Lemma mis_le_count s M c : mis_in s M c <= count_mis M c.
Proof.
  unfold mis_in, count_mis. apply Nat2Z.inj_le. apply p3_flen. intros e _ H. unfold mis_ok in H.
  apply andb_prop in H as [H _]. exact H.
Qed.

Lemma mis_in_mono s s' M c : incl (ub_cls s c) (ub_cls s' c) -> mis_in s M c <= mis_in s' M c.
Proof.
  intros Hi. unfold mis_in. apply Nat2Z.inj_le. apply p3_flen. intros e _ H. unfold mis_ok in *.
  apply andb_prop in H as [H1 H2]. rewrite H1. cbn [andb]. apply existsb_exists in H2 as (b & Hb & Eb).
  apply existsb_exists. exists b. split; [exact (Hi b Hb) | exact Eb].
Qed.

Lemma MIS_grow s s' M mc : (forall b, In b (user_blocks s) -> In b (user_blocks s')) -> MIS s M mc -> MIS s' M mc.
Proof.
  intros Hb (N & E & C). split; [exact N|]. split; [|exact C]. intros e He. destruct (E e He) as (R & k & Hk).
  split; [exact R|]. exists k. apply Hb. exact Hk.
Qed.

Lemma UPB3_eq s s' L M : user_blocks s' = user_blocks s -> (forall c, ub_cls s' c = ub_cls s c) -> UPB3 s L M -> UPB3 s' L M.
Proof.
  intros E1 E2 [U1 U2].
  assert (Em : forall c, mis_in s' M c = mis_in s M c) by (intros c; unfold mis_in, mis_ok; rewrite E2; reflexivity).
  split.
  - intros k Hk. unfold bcount. rewrite E1. exact (U1 k Hk).
  - intros c Hc. rewrite Em. unfold bcount, upc. rewrite E1, E2. exact (U2 c Hc).
Qed.

Lemma P3_same s s' L M mc : NoDup (keys s) -> NoDup (keys s') -> ub_same s s' -> CL s s' ->
  UPB3 s L M /\ MIS s M mc -> UPB3 s' L M /\ MIS s' M mc.
Proof.
  intros N N' UB HC [HU HM]. pose proof (ub_same_user_blocks s s' N N' UB) as E1. split.
  - apply (UPB3_eq s s' L M E1); [intros c; exact (ub_cls_same s s' c N N' UB HC) | exact HU].
  - apply (MIS_grow s s' M mc); [intros b Hb; rewrite E1; exact Hb | exact HM].
Qed.

Lemma UPB3_step s s3 L M n k : UPB3 s L M -> length L = 49%nat -> 0 <= band n < 49 ->
  (forall b, bcount s3 b = bcount s b + (if band n =? b then 1 else 0)) ->
  (forall c, upc s3 c = upc s c + (if (k =? c) && (band n =? c - 1) then 1 else 0)) ->
  (forall c, mis_in s M c <= mis_in s3 M c) ->
  (k = band n + 1 -> 1 <= k < 48 -> upc s k <= 12) ->
  UPB3 s3 (lv_add L (band n) 1) M.
Proof.
  intros (U1 & U2) HL Hb HB HU HMi HC. split.
  - intros j Hj. rewrite HB, znth_lv_add_u by (rewrite ?HL; lia). pose proof (U1 j Hj) as E.
    destruct (Z.eqb_spec (band n) j) as [->|N]; [rewrite Z.eqb_refl; lia|].
    replace (j =? band n) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  - intros c Hc. rewrite HB, HU, znth_lv_add_u by (rewrite ?HL; lia).
    pose proof (U1 c ltac:(lia)) as E1. pose proof (U2 c Hc) as E2. pose proof (HMi c) as E3.
    pose proof (mis_in_nonneg s M c) as E4.
    destruct ((k =? c) && (band n =? c - 1)) eqn:Q.
    + apply andb_prop in Q as [Q1 Q2]. apply Z.eqb_eq in Q1. apply Z.eqb_eq in Q2. subst k.
      specialize (HC ltac:(lia) Hc).
      replace (band n =? c) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (c =? band n) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota. unfold COARSE in *. lia.
    + destruct (Z.eqb_spec (band n) c) as [e|e];
        [rewrite e, Z.eqb_refl; cbv iota; lia
        |replace (c =? band n) with false by (symmetry; apply Z.eqb_neq; lia); cbv iota; lia].
Qed.

Lemma ucls_ins_incl s2 gm am idx hdr off n c : NoDup (keys s2) -> MT s2 gm = Some (MUsed am) -> 0 <= idx <= am_last am ->
  length (am_slots am) = Z.to_nat (am_last am + 1) -> ss_fr (nth_slot am idx) = None ->
  incl (ub_cls s2 c) (ub_cls (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2) c).
Proof.
  intros N Mg Hi Hlen Hfr.
  destruct (ucls_split s2 gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) c N
    (MT_Some_In_keys _ _ _ Mg)) as (K1 & K2 & E1 & E2).
  rewrite E1, E2, Mg. cbn [ucls].
  pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser)))) as (Fm & Fl & Fsc & _). rewrite Fsc, Fl.
  destruct (blocks_of_upd_slot gm am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))) Hi Hlen) as (l1 & l2 & B1 & B2).
  apply (f_equal (map fst)) in B1. apply (f_equal (map fst)) in B2. rewrite map_fst_blocks_of, !map_app in B1, B2.
  unfold slot_block in B1. rewrite Hfr in B1. cbn [map app] in B1.
  unfold slotst_block in B2. cbn [ss_fr fr_kind fr_off fr_n map fst] in B2.
  rewrite B1, B2. intros y Hy.
  destruct (am_sc am =? c); destruct (1 <=? am_last am); cbn [andb] in *; repeat rewrite in_app_iff in Hy;
  repeat rewrite in_app_iff; cbn [In] in *; tauto.
Qed.

Lemma final_UPB3 s s2 L M mc gm am idx hdr off n :
  Inv [] (Some (gm, idx)) U0 s2 -> NoDup (keys s) -> ub_same s s2 -> CL s s2 -> UPB3 s L M -> MIS s M mc ->
  length L = 49%nat -> 0 <= n ->
  MT s2 gm = Some (MUsed am) -> 0 <= idx <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
  ss_fr (nth_slot am idx) = None ->
  ((if 1 <=? am_last am then am_sc am else 100) = band n + 1 -> 1 <= band n + 1 < 48 -> upc s (band n + 1) <= 12) ->
  UPB3 (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2) (lv_add L (band n) 1) M /\
  MIS (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2) M mc.
Proof.
  intros HI2 N0 UB2 CL2 HU HM HLn Hn Mg2 Hidx Glen Hfr Hco.
  pose proof (proj1 (inv_keys HI2)) as N2.
  assert (N3 : NoDup (keys (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2)))
    by (rewrite keys_upd_In by exact (MT_Some_In_keys _ _ _ Mg2); exact N2).
  destruct (enframe_inserts [] (Some (gm, idx)) U0 s s2 gm am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser)))
    (padd (slot_start am idx) (UNIT * off)) n HI2 UB2 Mg2 Hidx Glen Hfr eq_refl) as (l1 & l2 & E1 & E2).
  pose proof (band_range n Hn) as BR.
  assert (Eb3 : user_blocks (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2) =
    map fst l1 ++ (padd (slot_start am idx) (UNIT * off), n) :: map fst l2)
    by (rewrite (user_blocks_ublist _ N3), E1, map_app; reflexivity).
  assert (Eb : user_blocks s = map fst l1 ++ map fst l2) by (rewrite (user_blocks_ublist s N0), E2, map_app; reflexivity).
  assert (Inc : forall c, incl (ub_cls s c)
    (ub_cls (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2) c)).
  { intros c. rewrite <- (ub_cls_same s s2 c N0 N2 UB2 CL2). exact (ucls_ins_incl s2 gm am idx hdr off n c N2 Mg2 Hidx Glen Hfr). }
  split.
  - apply (UPB3_step s _ L M n (if 1 <=? am_last am then am_sc am else 100) HU HLn ltac:(lia)).
    + exact (bcount_ins s _ (map fst l1) (map fst l2) (padd (slot_start am idx) (UNIT * off)) n Eb3 Eb).
    + intros c. rewrite (delta_k (am_sc am) (am_last am) (band n) c ltac:(lia)).
      rewrite (upc_ins s2 gm am idx hdr off n c N2 Mg2 Hidx Glen Hfr).
      assert (Eu : upc s2 c = upc s c) by (unfold upc; rewrite (ub_cls_same s s2 c N0 N2 UB2 CL2); reflexivity).
      rewrite Eu. reflexivity.
    + intros c. exact (mis_in_mono s _ M c (Inc c)).
    + intros Hk Hk48. rewrite Hk in Hk48 |- *. exact (Hco Hk Hk48).
  - apply (MIS_grow s _ M mc); [|exact HM]. intros b Hb. rewrite Eb3. rewrite Eb in Hb.
    apply in_app_iff in Hb as [Hb|Hb]; apply in_app_iff; [left; exact Hb | right; right; exact Hb].
Qed.

Lemma lift_caps s M L caps mc : UPB3 s L M -> MIS s M mc ->
  (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps /\ 0 <= znth k mc) ->
  CAPS (capsP caps mc) (mis_lift s M L) /\ UPB s (mis_lift s M L).
Proof.
  intros HU (_ & _ & HMc) HL. split; [|split].
  - intros k Hk. rewrite znth_capsP, znth_lift by lia. destruct (HL k Hk) as [A B].
    pose proof (mis_in_nonneg s M k) as C.
    destruct ((1 <=? k) && (k <? 48)) eqn:E; [|lia].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    pose proof (mis_le_count s M k). pose proof (HMc k ltac:(lia)). lia.
  - intros k Hk. rewrite znth_lift by lia. pose proof (proj1 HU k Hk). pose proof (mis_in_nonneg s M k).
    destruct ((1 <=? k) && (k <? 48)); lia.
  - intros c Hc. rewrite znth_lift by lia. rewrite (proj2 (Z.leb_le 1 c)) by lia. rewrite (proj2 (Z.ltb_lt c 48)) by lia.
    cbn [andb]. pose proof (proj2 HU c Hc). lia.
Qed.
