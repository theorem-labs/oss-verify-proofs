(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.


Definition bview (m : word -> option byte) : byteview :=
  fun a => if (0 <=? a) && (a <? 2^64) then
             match wview segs m (wa a), ov_read_bytes segs m (wa a) 1 with
             | Some _, Some [b] => Some (bv_unsigned b)
             | _, _ => None
             end
           else None.

#[using="Type"] Lemma bview_some : forall m a z, bview m a = Some z ->
  0 <= a < 2^64 /\ wview segs m (wa a) <> None /\ ov_read_bytes segs m (wa a) 1 = Some [Z_to_bv 8 z].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a z H. unfold bview in H.
  destruct ((0 <=? a) && (a <? 2^64)) eqn:Ea; [|discriminate].
  apply andb_prop in Ea as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct (wview segs m (wa a)) as [w|] eqn:Ew; [|discriminate].
  destruct (ov_read_bytes segs m (wa a) 1) as [[|b [|]]|] eqn:Er; try discriminate.
  injection H as <-. split; [lia|]. split; [congruence|].
  replace (Z_to_bv 8 (bv_unsigned b)) with b; [reflexivity|].
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  pose proof (bv_unsigned_in_range 8 b) as Rb. rewrite Z.mod_small; [reflexivity|]. exact Rb.
Qed.

#[using="Type"] Lemma wa_add1 : forall a, (wa a + 1)%bv = wa (a + 1).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros. unfold wa. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1 : word)) with 1. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ov_read_bytes_of_bytes : forall m n a (f : nat -> byte),
  (forall k, (k < n)%nat -> ov_read_bytes segs m (wa (a + Z.of_nat k)) 1 = Some [f k]) ->
  ov_read_bytes segs m (wa a) n = Some (map f (seq 0 n)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m n. induction n as [|n IH]; intros a f H; [reflexivity|].
  pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  cbn [ov_read_bytes]. cbn [ov_read_bytes] in H0.
  destruct (match m (wa a) with Some b => Some b | None => match memory_read segs (wa a) 1 with Some (b :: _) => Some b | _ => None end end)
    as [b|] eqn:Eb; [|discriminate].
  injection H0 as E0. subst b.
  rewrite wa_add1.
  rewrite (IH (a + 1) (fun k => f (S k))).
  - cbn [seq map]. f_equal. f_equal. rewrite <- seq_shift, map_map. reflexivity.
  - intros k Hk. specialize (H (S k) ltac:(lia)). replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (S k)) by lia. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma le_byte_Z_to_le_bytes : forall z w k, (w <= 8)%nat -> (k < w)%nat ->
  nth k (word_to_le_bytes w (Z_to_bv 64 z)) (Z_to_bv 8 0) = Z_to_bv 8 (le_byte z w k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z w k Hw Hk. unfold word_to_le_bytes, le_byte.
  assert (HN : forall n (x : Z) j, (j < n)%nat -> nth j (Z_to_le_bytes n x) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr x (8 * Z.of_nat j))).
  { induction n as [|n IH]; intros x j Hj; [lia|]. destruct j as [|j].
    - cbn. rewrite Z.shiftr_0_r. reflexivity.
    - cbn [Z_to_le_bytes nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia. }
  rewrite HN by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
  change 256 with (2^8).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 8) as [Hl|Hg].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

#[using="Type"] Lemma map_nth_seq : forall (l : list byte) n, length l = n -> map (fun k => nth k l (Z_to_bv 8 0)) (seq 0 n) = l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l n <-. induction l as [|x l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn. exact IH.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cell_ov_read : forall L m l w v,
  cell_holds L (bview m) (MCell l w v) -> (forall z, v <> VLo5 z) -> (w <= 8)%nat ->
  ov_read_bytes segs m (wa (loc_addr L l)) w = Some (word_to_le_bytes w (Z_to_bv 64 (sval_num L v))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L m l w v H Hv Hw.
  assert (H' : forall k, (k < w)%nat -> bview m (loc_addr L l + Z.of_nat k) = Some (le_byte (sval_num L v) w k)).
  { unfold cell_holds in H. cbn [mc_loc mc_w mc_val] in H. destruct v; try (apply H); exfalso; eapply Hv; reflexivity. }
  rewrite (ov_read_bytes_of_bytes m w (loc_addr L l) (fun k => Z_to_bv 8 (le_byte (sval_num L v) w k))).
  - f_equal. rewrite <- (map_nth_seq (word_to_le_bytes w (Z_to_bv 64 (sval_num L v))) w) by (apply length_Z_to_le_bytes).
    apply map_ext_in. intros k Hk. apply in_seq in Hk. rewrite le_byte_Z_to_le_bytes by lia. reflexivity.
  - intros k Hk. destruct (bview_some _ _ _ (H' k Hk)) as (_ & _ & R). exact R.
Qed.

#[using="Type"] Lemma cell_wview : forall L m c k, cell_holds L (bview m) c -> (k < mc_w c)%nat ->
  (match mc_val c with VLo5 _ => k = 0%nat | _ => True end) ->
  wview segs m (wa (loc_addr L (mc_loc c) + Z.of_nat k)) <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L m [l w v] k H Hk Hv. cbn [mc_loc mc_w mc_val] in *. unfold cell_holds in H. cbn [mc_loc mc_w mc_val] in H.
  destruct v.
  - destruct (bview_some _ _ _ (H k Hk)) as (_ & W & _). exact W.
  - destruct (bview_some _ _ _ (H k Hk)) as (_ & W & _). exact W.
  - subst k. destruct H as (b & Hb & _). rewrite Z.add_0_r. destruct (bview_some _ _ _ Hb) as (_ & W & _). exact W.
  - destruct (bview_some _ _ _ (H k Hk)) as (_ & W & _). exact W.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Update.
Variable segs : list Segment.

#[using="Type"] Lemma image_pair_disjoint : forall s L c1 c2,
  WF s -> layout_ok L s -> In c1 (image s) -> In c2 (image s) -> c1 <> c2 ->
  ranges_disjoint (cell_range L c1) (cell_range L c2).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s L c1 c2 HW HL H1 H2 Hne.
  pose proof (image_cells_disjoint s L HW HL) as P.
  destruct (pairwise_map_In _ _ _ _ _ P H1 H2 Hne) as [D|D]; [exact D | apply ranges_disjoint_sym; exact D].
Qed.

Definition in_rng (r : Z * Z) (a : Z) : Prop := fst r <= a < fst r + snd r.

#[using="Type"] Lemma ranges_disjoint_sym' : forall a b, ranges_disjoint a b -> ranges_disjoint b a.
Proof. LiaFast.lf_pins LiaFast.u0. intros a b H. unfold ranges_disjoint in *. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cell_holds_frame : forall L (bv bv' : byteview) c,
  (1 <= mc_w c)%nat ->
  cell_holds L bv c -> (forall a, in_rng (cell_range L c) a -> bv' a = bv a) -> cell_holds L bv' c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L bv bv' [l w v] Hw H Hf. unfold cell_holds in *. cbn [mc_loc mc_w mc_val] in *.
  unfold cell_range, in_rng in Hf. cbn [fst snd mc_loc mc_w] in Hf.
  destruct v.
  - intros k Hk. rewrite Hf by lia. apply H. exact Hk.
  - intros k Hk. rewrite Hf by lia. apply H. exact Hk.
  - destruct H as (b & Hb & Hm). exists b. split; [|exact Hm]. rewrite Hf; [exact Hb| lia].
  - intros k Hk. rewrite Hf by lia. apply H. exact Hk.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma meta_slot_cells_width : forall q x c, In c (meta_slot_cells q x) -> (1 <= mc_w c)%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros q x c H. unfold meta_slot_cells in H.
  destruct x as [[pr nx | | am]|]; cbn in H; repeat (destruct H as [<-|H]; [cbn; lia|]); destruct H.
Qed.

#[using="Type"] Lemma area_cells_width : forall s a next c, In c (area_cells s a next) -> (1 <= mc_w c)%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s a next c H. unfold area_cells in H. apply in_app_iff in H as [H|H].
  - cbn in H. repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H.
  - apply in_flat_map in H as [k [_ H]]. eapply meta_slot_cells_width; exact H.
Qed.

#[using="Type"] Lemma slot_cells_width : forall am i c, In c (slot_cells am i) -> (1 <= mc_w c)%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros am i c H. unfold slot_cells in H. apply in_app_iff in H as [H|H].
  - destruct H as [<-|[]]. cbn. lia.
  - apply in_app_iff in H as [H|H].
    + destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; cbn in H; [|destruct H].
      repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H.
    + destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct H].
      destruct (fr_off fr =? 0); cbn in H; [destruct H|].
      repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H.
Qed.

#[using="Type"] Lemma group_cells_width : forall g am c, In c (group_cells g am) -> (1 <= mc_w c)%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros g am c H. unfold group_cells in H. apply in_app_iff in H as [H|H].
  - destruct (am_maplen am =? 0); cbn in H; repeat (destruct H as [<-|H]; [cbn; lia|]); destruct H.
  - apply in_flat_map in H as [i [_ H]]. eapply slot_cells_width; exact H.
Qed.

#[using="Type"] Lemma image_cell_width : forall s c, In c (image s) -> (1 <= mc_w c)%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s c Hc. destruct (In_image_inv s c Hc) as [Hc' | [(a & next & Ha & Hc') | (g & am & Hg & Hc')]].
  - unfold ctx_cells in Hc'. repeat rewrite in_app_iff in Hc'.
    destruct Hc' as [H|[H|[H|H]]].
    + cbn in H. repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H.
    + apply in_map_iff in H as [k [<- _]]. cbn. lia.
    + apply in_map_iff in H as [k [<- _]]. cbn. lia.
    + repeat rewrite in_app_iff in H. destruct H as [H|H]; apply in_map_iff in H as [k [<- _]]; cbn; lia.
  - eapply area_cells_width; exact Hc'.
  - eapply group_cells_width; exact Hc'.
Qed.

Definition writes_only (L : layout) (s : astate) (Cold : list mcell) (bv bv' : byteview) : Prop :=
  forall a, bv' a <> bv a -> (exists c, In c Cold /\ in_rng (cell_range L c) a) \/ ~ in_footprint L s a.

#[using="Type"] Lemma option_Z_eq_dec : forall x y : option Z, {x = y} + {x <> y}.
Proof. LiaFast.lf_pins LiaFast.u0. decide equality. apply Z.eq_dec. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma repr_update : forall L s s' bv bv' Cold Cnew,
  WF s -> repr L s bv ->
  layout_ok L s' ->
  Forall (range_mapped L bv') (footprint s') ->
  (forall c, In c Cold -> In c (image s)) ->
  (forall c, In c (image s') -> (In c (image s) /\ ~ In c Cold) \/ In c Cnew) ->
  Forall (cell_holds L bv') Cnew ->
  writes_only L s Cold bv bv' ->
  repr L s' bv'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s s' bv bv' Cold Cnew HW [HL [HC HF]] HL' HF' HCold Hcov HNew HWO.
  split; [exact HL'|]. split; [|exact HF'].
  apply Forall_forall. intros c Hc. destruct (Hcov c Hc) as [[Hin Hnot] | Hnw].
  - apply (cell_holds_frame L bv bv' c (image_cell_width s c Hin)).
    + exact (proj1 (Forall_forall _ _) HC c Hin).
    + intros a Ha. destruct (option_Z_eq_dec (bv' a) (bv a)) as [E|E]; [exact E|].
      exfalso. destruct (HWO a E) as [(c' & Hc' & Ha') | Hnf].
      * assert (Hne : c <> c') by (intros ->; exact (Hnot Hc')).
        pose proof (image_pair_disjoint s L c c' HW HL Hin (HCold c' Hc') Hne) as D.
        unfold ranges_disjoint, in_rng in *. lia.
      * apply Hnf. destruct (image_in_footprint s L c HW HL Hin) as (rg & Hrg & Hincl).
        exists rg. split; [exact Hrg|]. unfold range_incl, crange, cell_range, in_rng in *. cbn [fst snd] in *. lia.
  - exact (proj1 (Forall_forall _ _) HNew c Hnw).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pairwise_In_app : forall {A} (R : A -> A -> Prop) (l1 l2 : list A),
  pairwise R (l1 ++ l2) -> forall x y, In x l1 -> In y l2 -> R x y.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A R l1. induction l1 as [|a t IH]; intros l2 HP x y Hx Hy; [destruct Hx|].
  cbn in HP. destruct HP as [H1 H2]. destruct Hx as [<-|Hx].
  - apply H1. apply in_app_iff. right. exact Hy.
  - eapply IH; eassumption.
Qed.

#[using="Type"] Lemma pairwise_perm : forall {A} (R : A -> A -> Prop) (l l' : list A),
  (forall x y, R x y -> R y x) -> Permutation l l' -> pairwise R l -> pairwise R l'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A R l l' Hsym HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact H.
  - cbn in *. destruct H as [Hx Hl]. split; [|apply IH; exact Hl].
    intros y Hy. apply Hx. apply (Permutation_in y (Permutation_sym HP) Hy).
  - cbn in *. destruct H as [Hy [Hx Hl]]. split; [|split; [|exact Hl]].
    + intros z [<-|Hz]; [apply Hsym, Hy; left; reflexivity | apply Hx, Hz].
    + intros z Hz. apply Hy. right. exact Hz.
  - apply IH2, IH1, H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma repr_update3 : forall L s s' bv bv' U K R W,
  WF s -> repr L s bv ->
  layout_ok L s' ->
  Forall (range_mapped L bv') (footprint s') ->
  Permutation (image s) (U ++ K ++ R) ->
  (forall c, In c (image s') -> In c U \/ In c K \/ In c W) ->
  Forall (cell_holds L bv') W ->
  writes_only L s R bv bv' ->
  repr L s' bv'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s s' bv bv' U K R W HW [HL [HC HF]] HL' HF' HP Hcov HNew HWO.
  split; [exact HL'|]. split; [|exact HF'].
  pose proof (pairwise_perm _ _ _ ranges_disjoint_sym' (Permutation_map (cell_range L) HP) (image_cells_disjoint s L HW HL)) as PW.
  rewrite !map_app in PW.
  assert (Hold : forall c, In c U \/ In c K -> cell_holds L bv' c).
  { intros c Hc.
    assert (Hin : In c (image s)).
    { apply (Permutation_in c (Permutation_sym HP)). apply in_app_iff. destruct Hc as [Hc|Hc]; [left; exact Hc | right; apply in_app_iff; left; exact Hc]. }
    apply (cell_holds_frame L bv bv' c (image_cell_width s c Hin)).
    - exact (proj1 (Forall_forall _ _) HC c Hin).
    - intros a Ha. destruct (option_Z_eq_dec (bv' a) (bv a)) as [E|E]; [exact E|].
      exfalso. destruct (HWO a E) as [(c' & Hc' & Ha') | Hnf].
      + assert (D : ranges_disjoint (cell_range L c) (cell_range L c')).
        { destruct Hc as [Hc|Hc].
          - apply (pairwise_In_app _ _ _ PW); [apply in_map; exact Hc | apply in_app_iff; right; apply in_map; exact Hc'].
          - rewrite app_assoc in PW. apply (pairwise_In_app _ _ _ PW); [apply in_app_iff; right; apply in_map; exact Hc | apply in_map; exact Hc']. }
        unfold ranges_disjoint, in_rng in *. lia.
      + apply Hnf. destruct (image_in_footprint s L c HW HL Hin) as (rg & Hrg & Hincl).
        exists rg. split; [exact Hrg|]. unfold range_incl, crange, cell_range, in_rng in *. cbn [fst snd] in *. lia. }
  apply Forall_forall. intros c Hc. destruct (Hcov c Hc) as [H1 | [H2 | H3]].
  - apply Hold. left. exact H1.
  - apply Hold. right. exact H2.
  - exact (proj1 (Forall_forall _ _) HNew c H3).
Qed.

End Update.
