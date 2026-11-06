(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzR5a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5cD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ws_stream_hdr (bs : Z) : list (Z * Z) := [(8, 66); (8, 90); (8, 104); (8, 48 + bs)].

Lemma seg_stream_hdr : forall bs L d s, 1 <= bs <= 9 ->
  dfeed (ws_stream_hdr bs) (DGo 10 L d s) =
  Some (DGo 14 L (let d2 := d_set_bs100k (d_set_state d 13) bs in if smallb d then d_set_ll_al d2 true else d_set_tt_al d2 true) s).
Proof.
  intros bs L d s Hbs. unfold ws_stream_hdr.
  ostep gb_bits_10 gb_after_10. ostep gb_bits_11 gb_after_11. ostep gb_bits_12 gb_after_12. ostep gb_bits_13 gb_after_13.
  cbv zeta. replace ((48 + bs <? 49) || (57 <? 48 + bs))%bool with false by (symmetry; apply Bool.orb_false_iff; split; [apply Z.ltb_ge| apply Z.ltb_ge]; lia).
  rewrite dfeed_nil. replace (48 + bs - 48) with bs by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ws_blk_hdr (crc op : Z) : list (Z * Z) :=
  [(8, 49); (8, 65); (8, 89); (8, 38); (8, 83); (8, 89)] ++ ws_u32 crc ++
  [(1, 0); (8, op / 65536); (8, (op / 256) mod 256); (8, op mod 256)].

Lemma seg_blk_hdr : forall crc op L d s, 0 <= crc < 4294967296 -> 0 <= op < 16777216 -> op <= 10 + 100000 * d_bs100k d ->
  dfeed (ws_blk_hdr crc op) (DGo 14 L d s) =
  Some (DGo 28 (sv_set_i L 0) (d_set_origPtr (d_set_rand (d_set_sbcrc (d_set_blockNo (d_set_state d 27) (d_blockNo d + 1)) crc) 0) op) s).
Proof.
  intros crc op L d s Hc Hop Hcap. unfold ws_blk_hdr, ws_u32. cbn [app].
  cps_destruct (u32_bytes crc Hc) as (B3 & B2 & B1 & B0). rewrite B3, B2, B1, B0.
  ostep gb_bits_14 gb_after_14. ostep gb_bits_15 gb_after_15. ostep gb_bits_16 gb_after_16.
  ostep gb_bits_17 gb_after_17. ostep gb_bits_18 gb_after_18. ostep gb_bits_19 gb_after_19.
  ostep gb_bits_20 gb_after_20. ostep gb_bits_21 gb_after_21. ostep gb_bits_22 gb_after_22. ostep gb_bits_23 gb_after_23.
  ostep gb_bits_24 gb_after_24. ostep gb_bits_25 gb_after_25. ostep gb_bits_26 gb_after_26. ostep gb_bits_27 gb_after_27.
  cbv zeta.
  match goal with |- context [d_origPtr ?X <? 0] => set (D := X) end.
  assert (EO : d_origPtr D = op).
  { subst D. cbn [d_origPtr d_set_origPtr d_set_state d_set_rand d_set_sbcrc d_set_blockNo]. apply op_assemble. exact Hop. }
  rewrite EO. replace (op <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  assert (EB : d_bs100k D = d_bs100k d) by reflexivity. rewrite EB.
  replace (10 + 100000 * d_bs100k d <? op) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  rewrite dfeed_nil. f_equal. f_equal. subst D. dnorm d.
  rewrite crc_assemble, op_assemble by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma map2_cong : forall m i L L' d d' s, L = L' -> d = d' -> Some (map2_outer m i L d s) = Some (map2_outer m i L' d' s).
Proof. intros; subst; reflexivity. Qed.
Lemma dgo_cong : forall l L L' d d' s, L = L' -> d = d' -> Some (DGo l L d s) = Some (DGo l L' d' s).
Proof. intros; subst; reflexivity. Qed.
Lemma dfeed_cong : forall ws l L L' d d' s, L = L' -> d = d' -> dfeed ws (DGo l L d s) = dfeed ws (DGo l L' d' s).
Proof. intros; subst; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zsets (n : nat) (i : Z) (f : Z -> option Z) (a : zarr) : zarr :=
  match n with
  | O => a
  | S n' => zsets n' (i + 1) f (match f i with Some v => zset a i v | None => a end)
  end.
Lemma zsets_get : forall n i f a p,
  zget (zsets n i f a) p = (if (i <=? p) && (p <? i + Z.of_nat n) then match f p with Some v => v | None => zget a p end else zget a p)%bool.
Proof.
  induction n as [|n IH]; intros i f a p; cbn [zsets].
  - destruct (Z.leb_spec i p), (Z.ltb_spec p (i + Z.of_nat 0)); cbn; try reflexivity. lia.
  - rewrite IH. destruct (Z.eq_dec p i) as [->|NE].
    + replace ((i + 1 <=? i) && (i <? i + 1 + Z.of_nat n))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      replace ((i <=? i) && (i <? i + Z.of_nat (S n)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
      destruct (f i); [apply zget_zset_same| reflexivity].
    + assert (E : zget (match f i with Some v => zset a i v | None => a end) p = zget a p) by (destruct (f i); [apply zget_zset_other; exact NE| reflexivity]).
      rewrite E. destruct (Z.leb_spec (i + 1) p), (Z.ltb_spec p (i + 1 + Z.of_nat n)), (Z.leb_spec i p), (Z.ltb_spec p (i + Z.of_nat (S n))); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Fixpoint ws_bits16 (n : nat) (f : Z -> Z) (i : Z) : list (Z * Z) :=
  match n with O => [] | S n' => (1, f i) :: ws_bits16 n' f (i + 1) end.

Lemma seg_map1 : forall k f i L d s, sv_i L = i -> 0 <= i -> i + Z.of_nat k = 16 -> (1 <= k)%nat ->
  (forall j, 0 <= j < 16 -> f j = 0 \/ f j = 1) ->
  dfeed (ws_bits16 k f i) (DGo 28 L d s) =
  Some (let D := d_set_inUse16 (d_set_state d 28) (zsets k i (fun j => Some (f j)) (d_inUse16 d)) in
        map2_outer 17 0 (sv_set_i L 256) (d_set_inUse D (clear256 256 0 (d_inUse D))) s).
Proof.
  induction k as [|k IH]; intros f i L d s Hi H0 Hk K1 Hf; [lia|].
  cbn [ws_bits16 zsets]. ostep gb_bits_28 gb_after_28. cbv zeta. rewrite Hi.
  replace (if f i =? 1 then 1 else 0) with (f i) by (destruct (Hf i ltac:(lia)) as [E|E]; rewrite E; reflexivity).
  destruct k as [|k].
  - replace (i + 1 <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbn [zsets]. rewrite dfeed_nil. reflexivity.
  - replace (i + 1 <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (IH f (i + 1)) by (try (cbn [sv_i sv_set_i]; lia); exact Hf). cbv zeta.
    reflexivity.
Qed.

(* [comment removed for export] *)
Definition rowf (bit : Z -> Z) (c : Z) : option Z := if bit c =? 1 then Some 1 else None.

Lemma seg_row : forall k bit i j L d s, sv_i L = i -> sv_j L = j -> 0 <= j -> j + Z.of_nat k = 16 -> (1 <= k)%nat ->
  dfeed (ws_bits16 k (fun j' => bit (i * 16 + j')) j) (DGo 29 L d s) =
  Some (map2_outer 17 (i + 1) (sv_set_j L 16) (d_set_inUse (d_set_state d 29) (zsets k (i * 16 + j) (rowf bit) (d_inUse d))) s).
Proof.
  induction k as [|k IH]; intros bit i j L d s Hi Hj H0 Hk K1; [lia|].
  cbn [ws_bits16 zsets]. ostep gb_bits_29 gb_after_29. cbv zeta. rewrite Hi, Hj. unfold rowf at 1.
  destruct k as [|k].
  - replace (j + 1 <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbn [zsets]. rewrite dfeed_nil.
    replace (j + 1) with 16 by lia. apply map2_cong; [reflexivity|]. unfold rowf. destruct (bit (i * 16 + j) =? 1); destruct d; reflexivity.
  - replace (j + 1 <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    etransitivity.
    { apply dfeed_cong; [reflexivity|]. instantiate (1 := d_set_inUse (d_set_state d 29) match rowf bit (i * 16 + j) with Some v => zset (d_inUse d) (i * 16 + j) v | None => d_inUse d end).
      unfold rowf. destruct (bit (i * 16 + j) =? 1); destruct d; reflexivity. }
    rewrite (IH bit i (j + 1)) by (cbn [sv_i sv_j sv_set_j]; lia). cbv zeta. replace (i * 16 + (j + 1)) with (i * 16 + j + 1) by lia.
    apply map2_cong; [destruct L; reflexivity| destruct d; reflexivity].
Qed.

(* [comment removed for export] *)
Fixpoint ws_rows (n : nat) (g16 bit : Z -> Z) (i : Z) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => (if negb (g16 i =? 0) then ws_bits16 16 (fun j => bit (i * 16 + j)) 0 else []) ++ ws_rows n' g16 bit (i + 1)
  end.
Fixpoint map_rows (n : nat) (i : Z) (g16 bit : Z -> Z) (d : dst) : dst :=
  match n with
  | O => d
  | S n' => map_rows n' (i + 1) g16 bit
             (if negb (g16 i =? 0) then d_set_inUse (d_set_state d 29) (zsets 16 (i * 16) (rowf bit) (d_inUse d)) else d)
  end.
Fixpoint anyrow (n : nat) (i : Z) (g16 : Z -> Z) : bool :=
  match n with O => false | S n' => negb (g16 i =? 0) || anyrow n' (i + 1) g16 end.

(* [comment removed for export] *)

Lemma seg_map2 : forall k m g16 bit i L d s, 0 <= i -> i + Z.of_nat k = 16 -> (k < m)%nat ->
  (forall i', i <= i' < 16 -> zget (d_inUse16 d) i' = g16 i') ->
  dfeed (ws_rows k g16 bit i) (map2_outer m i L d s) =
  Some (let D := makeMaps_d (map_rows k i g16 bit d) in
        let L1 := sv_set_i (if anyrow k i g16 then sv_set_j L 16 else L) 16 in
        if d_nInUse D =? 0 then DRet BZ_DATA_ERROR L1 D s else DGo 30 (sv_set_alphaSize L1 (d_nInUse D + 2)) D s).
Proof.
  induction k as [|k IH]; intros m g16 bit i L d s H0 Hk Hm G16.
  - destruct m as [|m]; [lia|]. rewrite map2_outer_S. cbn [ws_rows map_rows anyrow]. rewrite dfeed_nil.
    replace (16 <=? i) with true by (symmetry; apply Z.leb_le; lia). cbv zeta. replace i with 16 by lia. reflexivity.
  - destruct m as [|m]; [lia|]. rewrite map2_outer_S. cbn [ws_rows map_rows anyrow].
    replace (16 <=? i) with false by (symmetry; apply Z.leb_gt; lia). rewrite G16 by lia.
    destruct (negb (g16 i =? 0)) eqn:GI.
    + rewrite dfeed_app. rewrite (seg_row 16 bit i 0) by (try reflexivity; lia). replace (i * 16 + 0) with (i * 16) by lia.
      rewrite (IH 17%nat g16 bit (i + 1)); try lia.
      2:{ intros i' Hi'. cbn [d_inUse16 d_set_inUse d_set_state]. apply G16. lia. }
      cbv zeta. cbn [orb]. destruct (anyrow k (i + 1) g16); reflexivity.
    + cbn [app]. rewrite (IH m g16 bit (i + 1)); try lia; [| intros; apply G16; lia]. cbn [orb]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sel_next (MX : Z) (i jv : Z) (L : dsv) (d : dst) (s : dstrm) : dres :=
  let L0 := sv_set_j L jv in
  let d0 := d_set_state d 32 in
  let d1 := if i <? MX then d_set_selMtf d0 (zset (d_selMtf d0) i jv) else d0 in
  let i1 := i + 1 in
  if i1 <? sv_nSelectors L then DGo 32 (sv_set_j (sv_set_i L0 i1) 0) d1 s
  else
    let nSel := if MX <? sv_nSelectors L then MX else sv_nSelectors L in
    let pos0 := pos_init (Z.to_nat (sv_nGroups L)) 0 znew in
    let '(_, sel1) := sel_undo (Z.to_nat nSel) 0 pos0 (d_selMtf d1) (d_sel d1) in
    DGo 33 (sv_set_t (sv_set_i (sv_set_nSelectors L0 nSel) nSel) 0) (d_set_sel d1 sel1) s.

Lemma seg_sel1 : forall m j i L d s rest, sv_i L = i -> sv_j L = j -> 0 <= j -> j + Z.of_nat m < sv_nGroups L ->
  dfeed (repeat (1, 1) m ++ (1, 0) :: rest) (DGo 32 L d s) = dfeed rest (sel_next BZ_MAX_SELECTORS i (j + Z.of_nat m) L d s).
Proof.
  induction m as [|m IH]; intros j i L d s rest Hi Hj H0 Hm.
  - cbn [repeat app]. ostep gb_bits_32 gb_after_32. remember BZ_MAX_SELECTORS as MX eqn:HMX. cbv zeta.
    unfold sel_next. rewrite Hi, Hj, Z.add_0_r. cbn [sv_nSelectors sv_nGroups sv_set_j d_selMtf d_sel d_set_state].
    destruct (i + 1 <? sv_nSelectors L); [apply dfeed_cong; [destruct L; reflexivity| reflexivity]|].
    destruct (sel_undo _ _ _ _ _) as [p1 sel1]. apply dfeed_cong; [destruct L; cbn in Hj |- *; subst; reflexivity| reflexivity].
  - cbn [repeat app]. ostep gb_bits_32 gb_after_32. cbv zeta. rewrite Hj.
    replace (sv_nGroups L <=? j + 1) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite (IH (j + 1) i) by (cbn [sv_i sv_j sv_nGroups sv_set_j]; lia).
    replace (j + 1 + Z.of_nat m) with (j + Z.of_nat (S m)) by lia.
    unfold sel_next. cbn [sv_nSelectors sv_nGroups sv_set_j sv_set_i sv_set_nSelectors d_selMtf d_sel d_set_state d_set_selMtf].
    remember BZ_MAX_SELECTORS as MX eqn:HMX.
    destruct (i + 1 <? sv_nSelectors L); [apply dfeed_cong; [destruct L; reflexivity| destruct (i <? MX); destruct d; reflexivity]|].
    replace (d_selMtf (if i <? MX then d_set_selMtf (d_set_state (d_set_state d 32) 32) (zset (d_selMtf d) i (j + Z.of_nat (S m))) else d_set_state (d_set_state d 32) 32))
      with (d_selMtf (if i <? MX then d_set_selMtf (d_set_state d 32) (zset (d_selMtf d) i (j + Z.of_nat (S m))) else d_set_state d 32))
      by (destruct (i <? MX); reflexivity).
    replace (d_sel (if i <? MX then d_set_selMtf (d_set_state (d_set_state d 32) 32) (zset (d_selMtf d) i (j + Z.of_nat (S m))) else d_set_state (d_set_state d 32) 32))
      with (d_sel (if i <? MX then d_set_selMtf (d_set_state d 32) (zset (d_selMtf d) i (j + Z.of_nat (S m))) else d_set_state d 32))
      by (destruct (i <? MX); reflexivity).
    destruct (sel_undo _ _ _ _ _) as [p1 sel1].
    apply dfeed_cong; [destruct L; reflexivity| destruct (i <? MX); destruct d; reflexivity].
Qed.

Lemma seg_sel_hdr : forall nG nS L d s, 2 <= nG <= 6 -> 1 <= nS < 32768 ->
  dfeed [(3, nG); (15, nS)] (DGo 30 L d s) =
  Some (DGo 32 (sv_set_j (sv_set_i (sv_set_nSelectors (sv_set_nGroups L nG) nS) 0) 0) (d_set_state d 31) s).
Proof.
  intros nG nS L d s HG HS. ostep gb_bits_30 gb_after_30.
  replace ((nG <? 2) || (BZ_N_GROUPS <? nG))%bool with false by (symmetry; apply Bool.orb_false_iff; unfold BZ_N_GROUPS; split; apply Z.ltb_ge; lia).
  ostep gb_bits_31 gb_after_31. replace (nS <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite dfeed_nil. apply dgo_cong; [reflexivity| destruct d; reflexivity].
Qed.

Fixpoint ws_unary (n : nat) (msel : Z -> Z) (i : Z) : list (Z * Z) :=
  match n with O => [] | S n' => (repeat (1, 1) (Z.to_nat (msel i)) ++ [(1, 0)]) ++ ws_unary n' msel (i + 1) end.

Lemma seg_sels : forall n msel i L d s, sv_i L = i -> sv_j L = 0 -> 0 <= i -> i + Z.of_nat n = sv_nSelectors L -> (1 <= n)%nat ->
  sv_nSelectors L <= BZ_MAX_SELECTORS -> (forall k, i <= k < sv_nSelectors L -> 0 <= msel k < sv_nGroups L) ->
  dfeed (ws_unary n msel i) (DGo 32 L d s) =
  Some (let nS := sv_nSelectors L in
        let D := d_set_selMtf (d_set_state d 32) (zsets n i (fun k => Some (msel k)) (d_selMtf d)) in
        let sel1 := snd (sel_undo (Z.to_nat nS) 0 (pos_init (Z.to_nat (sv_nGroups L)) 0 znew) (d_selMtf D) (d_sel D)) in
        DGo 33 (sv_set_t (sv_set_i (sv_set_nSelectors (sv_set_j L (msel (nS - 1))) nS) nS) 0) (d_set_sel D sel1) s).
Proof.
  induction n as [|n IH]; intros msel i L d s Hi Hj H0 Hn N1 HMX HM; [lia|].
  cbn [ws_unary]. rewrite <- app_assoc. cbn [app].
  pose proof (HM i ltac:(lia)) as Mi.
  rewrite (seg_sel1 (Z.to_nat (msel i)) 0 i L d s) by (try assumption; lia).
  unfold sel_next. remember BZ_MAX_SELECTORS as MX eqn:HMX'.
  replace (i <? MX) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (0 + Z.of_nat (Z.to_nat (msel i))) with (msel i) by lia.
  destruct n as [|n].
  - replace (i + 1 <? sv_nSelectors L) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (MX <? sv_nSelectors L) with false by (symmetry; apply Z.ltb_ge; lia). cbv zeta.
    cbn [zsets d_selMtf d_sel d_set_selMtf d_set_state].
    destruct (sel_undo _ _ _ _ _) as [p1 sel1] eqn:SU. rewrite dfeed_nil. cbn [snd].
    replace (sv_nSelectors L - 1) with i by lia. reflexivity.
  - replace (i + 1 <? sv_nSelectors L) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
    rewrite (IH msel (i + 1)); try (cbn [sv_i sv_j sv_nSelectors sv_nGroups sv_set_j sv_set_i]; lia).
    2:{ intros k Hk. cbn [sv_nSelectors sv_nGroups sv_set_j sv_set_i] in Hk |- *. apply HM. lia. }
    cbv zeta. cbn [sv_nSelectors sv_nGroups sv_set_j sv_set_i d_selMtf d_sel d_set_selMtf d_set_state zsets].
    apply dgo_cong; [destruct L; reflexivity| destruct d; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint dsteps (up : bool) (m : nat) : list (Z * Z) :=
  match m with O => [] | S m' => (1, 1) :: (1, if up then 0 else 1) :: dsteps up m' end.
Lemma dsteps_legal : forall up m, wlegal (dsteps up m).
Proof. intros up m. induction m; cbn [dsteps]; [apply wlegal_nil|]. apply wlegal_cons. split; [cbn; lia|]. apply wlegal_cons. split; [destruct up; cbn; lia| exact IHm]. Qed.
(* [comment removed for export] *)
Lemma wbits_dsteps_up : forall m, wbits (repeat (2, 2) m) = wbits (dsteps true m).
Proof.
  induction m as [|m IH]; cbn [repeat dsteps wbits]; [reflexivity|]. rewrite IH.
  rewrite <- (bapp_assoc (Bits 1 1) (Bits 1 0)) by (try (cbn; lia); apply wbits_len; apply dsteps_legal). reflexivity.
Qed.
Lemma wbits_dsteps_down : forall m, wbits (repeat (2, 3) m) = wbits (dsteps false m).
Proof.
  induction m as [|m IH]; cbn [repeat dsteps wbits]; [reflexivity|]. rewrite IH.
  rewrite <- (bapp_assoc (Bits 1 1) (Bits 1 1)) by (try (cbn; lia); apply wbits_len; apply dsteps_legal). reflexivity.
Qed.

(* [comment removed for export] *)
Definition len_next (tgt : Z) (L : dsv) (d : dst) (s : dstrm) : dres :=
  let L0 := sv_set_curr L tgt in
  let t := sv_t L in let i := sv_i L in
  let d1 := d_set_len (d_set_state d 34) (zset (d_len d) (258 * t + i) tgt) in
  let i1 := i + 1 in
  if i1 <? sv_alphaSize L then coding_check (sv_set_i L0 i1) d1 s
  else let t1 := t + 1 in
       if t1 <? sv_nGroups L then DGo 33 (sv_set_t (sv_set_i L0 i1) t1) d1 s
       else after_tables (sv_set_t (sv_set_i L0 i1) t1) d1 s.

Lemma seg_len1 : forall m (up : bool) L d s rest curr, sv_curr L = curr -> 1 <= curr <= 20 ->
  let tgt := (if up then curr + Z.of_nat m else curr - Z.of_nat m) in 1 <= tgt <= 20 ->
  dfeed (dsteps up m ++ (1, 0) :: rest) (coding_check L d s) = dfeed rest (len_next tgt L d s).
Proof.
  induction m as [|m IH]; intros up L d s rest curr Hc Hr; cbv zeta; intros Ht.
  - cbn [dsteps app]. unfold coding_check at 1. rewrite Hc.
    replace ((curr <? 1) || (20 <? curr))%bool with false by (symmetry; apply Bool.orb_false_iff; split; apply Z.ltb_ge; lia).
    ostep gb_bits_34 gb_after_34. unfold len_next. rewrite Hc.
    replace (if up then curr + Z.of_nat 0 else curr - Z.of_nat 0) with curr by (destruct up; lia).
    replace (sv_set_curr L curr) with L by (destruct L; cbn in Hc |- *; subst; reflexivity).
    reflexivity.
  - cbn [dsteps app]. unfold coding_check at 1. rewrite Hc.
    replace ((curr <? 1) || (20 <? curr))%bool with false by (symmetry; apply Bool.orb_false_iff; split; apply Z.ltb_ge; lia).
    ostep gb_bits_34 gb_after_34. ostep gb_bits_35 gb_after_35. rewrite Hc.
    rewrite (IH up _ _ s rest (if up then curr + 1 else curr - 1)); [| destruct up; reflexivity| destruct up; lia| destruct up; lia].
    unfold len_next. cbn [sv_t sv_i sv_alphaSize sv_nGroups sv_curr sv_set_curr d_len d_set_state d_set_len].
    replace (d_set_state (d_set_state (d_set_state d 34) 35) 34) with (d_set_state d 34) by (destruct d; reflexivity).
    destruct up; zb.
    + replace (curr + 1 + Z.of_nat m) with (curr + Z.of_nat (S m)) by lia.
      replace (sv_set_curr (sv_set_curr L (curr + 1)) (curr + Z.of_nat (S m))) with (sv_set_curr L (curr + Z.of_nat (S m))) by (destruct L; reflexivity).
      reflexivity.
    + replace (curr - 1 - Z.of_nat m) with (curr - Z.of_nat (S m)) by lia.
      replace (sv_set_curr (sv_set_curr L (curr - 1)) (curr - Z.of_nat (S m))) with (sv_set_curr L (curr - Z.of_nat (S m))) by (destruct L; reflexivity).
      reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint ws_drow (n : nat) (ln : Z -> Z) (i curr : Z) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => let tgt := ln i in
            (if curr <? tgt then dsteps true (Z.to_nat (tgt - curr)) else dsteps false (Z.to_nat (curr - tgt))) ++
            (1, 0) :: ws_drow n' ln (i + 1) tgt
  end.
Lemma ws_drow_app : forall n ln i curr rest, ws_drow n ln i curr ++ rest =
  match n with O => rest | S n' => let tgt := ln i in
    (if curr <? tgt then dsteps true (Z.to_nat (tgt - curr)) else dsteps false (Z.to_nat (curr - tgt))) ++ (1, 0) :: (ws_drow n' ln (i + 1) tgt ++ rest) end.
Proof. intros [|n] ln i curr rest; cbn [ws_drow]; [reflexivity|]. rewrite <- app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Definition row_next (lastlen : Z) (lens : zarr) (L : dsv) (d : dst) (s : dstrm) : dres :=
  let aS := sv_alphaSize L in let t := sv_t L in
  let L' := sv_set_i (sv_set_curr L lastlen) aS in
  let D := d_set_len (d_set_state d 34) lens in
  if t + 1 <? sv_nGroups L then DGo 33 (sv_set_t L' (t + 1)) D s else after_tables (sv_set_t L' (t + 1)) D s.

Lemma seg_row_len : forall n ln i curr L d s rest, sv_i L = i -> sv_curr L = curr -> 0 <= i -> 1 <= curr <= 20 ->
  (forall v, i <= v < i + Z.of_nat n -> 1 <= ln v <= 20) -> i + Z.of_nat n = sv_alphaSize L -> (1 <= n)%nat ->
  dfeed (ws_drow n ln i curr ++ rest) (coding_check L d s) =
  dfeed rest (row_next (ln (sv_alphaSize L - 1)) (zsets n (258 * sv_t L + i) (fun c => Some (ln (c - 258 * sv_t L))) (d_len d)) L d s).
Proof.
  induction n as [|n IH]; intros ln i curr L d s rest Hi Hc H0 Hr Hl Hn N1; [lia|].
  rewrite ws_drow_app. cbv zeta. pose proof (Hl i ltac:(lia)) as Li.
  destruct (Z.ltb_spec curr (ln i)) as [LT|GE];
    [ rewrite (seg_len1 (Z.to_nat (ln i - curr)) true L d s _ curr Hc Hr) by lia;
      replace (curr + Z.of_nat (Z.to_nat (ln i - curr))) with (ln i) by lia
    | rewrite (seg_len1 (Z.to_nat (curr - ln i)) false L d s _ curr Hc Hr) by lia;
      replace (curr - Z.of_nat (Z.to_nat (curr - ln i))) with (ln i) by lia ].
  all: unfold len_next; rewrite Hi; cbn [zsets]; replace (258 * sv_t L + i - 258 * sv_t L) with i by lia.
  all: destruct n as [|n].
  1,3: replace (i + 1 <? sv_alphaSize L) with false by (symmetry; apply Z.ltb_ge; lia); cbn [app zsets];
       unfold row_next; replace (sv_alphaSize L - 1) with i by lia; replace (sv_alphaSize L) with (i + 1) by lia; reflexivity.
  all: replace (i + 1 <? sv_alphaSize L) with true by (symmetry; apply Z.ltb_lt; lia).
  all: rewrite (IH ln (i + 1) (ln i)); try (cbn [sv_i sv_curr sv_alphaSize sv_set_i sv_set_curr]; lia); [| intros; apply Hl; lia].
  all: unfold row_next; cbn [sv_alphaSize sv_t sv_nGroups sv_set_i sv_set_curr sv_set_t d_len d_set_len d_set_state].
  all: replace (258 * sv_t L + (i + 1)) with (258 * sv_t L + i + 1) by lia.
  all: replace (d_set_len (d_set_state (d_set_len (d_set_state d 34) (zset (d_len d) (258 * sv_t L + i) (ln i))) 34)
                 (zsets (S n) (258 * sv_t L + i + 1) (fun c : Z => Some (ln (c - 258 * sv_t L))) (zset (d_len d) (258 * sv_t L + i) (ln i))))
         with (d_set_len (d_set_state d 34) (zsets (S n) (258 * sv_t L + i + 1) (fun c : Z => Some (ln (c - 258 * sv_t L))) (zset (d_len d) (258 * sv_t L + i) (ln i))))
         by (destruct d; reflexivity).
  all: replace (sv_set_i (sv_set_curr (sv_set_i (sv_set_curr L (ln i)) (i + 1)) (ln (sv_alphaSize L - 1))) (sv_alphaSize L))
         with (sv_set_i (sv_set_curr L (ln (sv_alphaSize L - 1))) (sv_alphaSize L)) by (destruct L; reflexivity).
  all: reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint ws_dtables (n : nat) (lnT : Z -> Z -> Z) (aS : nat) (t : Z) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => ((5, lnT t 0) :: ws_drow aS (lnT t) 0 (lnT t 0)) ++ ws_dtables n' lnT aS (t + 1)
  end.
Fixpoint ztabs (n : nat) (t : Z) (aS : nat) (lnT : Z -> Z -> Z) (a : zarr) : zarr :=
  match n with
  | O => a
  | S n' => ztabs n' (t + 1) aS lnT (zsets aS (258 * t) (fun c => Some (lnT t (c - 258 * t))) a)
  end.

Lemma seg_tables : forall n lnT t aS nG L d s rest, sv_t L = t -> sv_alphaSize L = aS -> sv_nGroups L = nG ->
  0 <= t -> t + Z.of_nat n = nG -> (1 <= n)%nat -> 1 <= aS ->
  (forall t' v, t <= t' < nG -> 0 <= v < aS -> 1 <= lnT t' v <= 20) ->
  dfeed (ws_dtables n lnT (Z.to_nat aS) t ++ rest) (DGo 33 L d s) =
  dfeed rest (after_tables (sv_set_t (sv_set_i (sv_set_curr L (lnT (nG - 1) (aS - 1))) aS) nG)
                           (d_set_len (d_set_state d 34) (ztabs n t (Z.to_nat aS) lnT (d_len d))) s).
Proof.
  induction n as [|n IH]; intros lnT t aS nG L d s rest Ht HA HG H0 Hn N1 A1 Hl; [lia|].
  cbn [ws_dtables ztabs]. rewrite <- app_assoc. cbn [app].
  pose proof (Hl t 0 ltac:(lia) ltac:(lia)) as L0.
  rewrite dfeed_cons. change (mtf_lbl 33) with false. rewrite gb_bits_33. cbn [negb andb Z.eqb Pos.eqb]. rewrite gb_after_33.
  rewrite (seg_row_len (Z.to_nat aS) (lnT t) 0 (lnT t 0)); try (cbn [sv_i sv_curr sv_alphaSize sv_set_i sv_set_curr]; lia).
  2:{ intros v Hv. apply Hl; lia. }
  unfold row_next. cbn [sv_alphaSize sv_t sv_nGroups sv_set_i sv_set_curr sv_set_t d_len d_set_len d_set_state]. rewrite Ht, HA, HG.
  replace (258 * t + 0) with (258 * t) by lia.
  destruct n as [|n].
  - replace (t + 1 <? nG) with false by (symmetry; apply Z.ltb_ge; lia). cbn [ztabs].
    replace (nG - 1) with t by lia. replace nG with (t + 1) by lia.
    replace (d_set_len (d_set_state (d_set_state d 33) 34)) with (d_set_len (d_set_state d 34)) by (destruct d; reflexivity).
    replace (sv_set_i (sv_set_curr (sv_set_i (sv_set_curr L (lnT t 0)) 0) (lnT t (aS - 1))) aS)
      with (sv_set_i (sv_set_curr L (lnT t (aS - 1))) aS) by (destruct L; reflexivity).
    reflexivity.
  - replace (t + 1 <? nG) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (IH lnT (t + 1) aS nG); try (cbn [sv_t sv_alphaSize sv_nGroups sv_set_t sv_set_i sv_set_curr]; lia).
    2:{ intros t' v Ht' Hv. apply Hl; lia. }
    cbn [ztabs].
    replace (d_set_len (d_set_state (d_set_len (d_set_state (d_set_state d 33) 34) (zsets (Z.to_nat aS) (258 * t) (fun c : Z => Some (lnT t (c - 258 * t))) (d_len d))) 34))
      with (d_set_len (d_set_state d 34)) by (destruct d; reflexivity).
    replace (d_len (d_set_len (d_set_state (d_set_state d 33) 34) (zsets (Z.to_nat aS) (258 * t) (fun c : Z => Some (lnT t (c - 258 * t))) (d_len d))))
      with (zsets (Z.to_nat aS) (258 * t) (fun c : Z => Some (lnT t (c - 258 * t))) (d_len d)) by reflexivity.
    replace (sv_set_t (sv_set_i (sv_set_curr (sv_set_t (sv_set_i (sv_set_curr (sv_set_i (sv_set_curr L (lnT t 0)) 0) (lnT t (aS - 1))) aS) (t + 1)) (lnT (nG - 1) (aS - 1))) aS) nG)
      with (sv_set_t (sv_set_i (sv_set_curr L (lnT (nG - 1) (aS - 1))) aS) nG) by (destruct L; reflexivity).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tables_d (L : dsv) (d : dst) : dst :=
  let d1 := make_tables (Z.to_nat (sv_nGroups L)) 0 (sv_alphaSize L) d in
  mtf_init (d_set_unzftab d1 (clear256 256 0 (d_unzftab d1))).
Definition tables_L (L : dsv) (d : dst) : dsv :=
  let D := tables_d L d in
  let gSel := zget (d_sel D) 0 in
  let gMinlen := zget (d_minLens D) gSel in
  sv_set_zn (sv_set_gPtr (sv_set_gMinlen (sv_set_gSel (sv_set_groupPos (sv_set_groupNo
    (sv_set_nblock (sv_set_i (sv_set_groupPos (sv_set_groupNo (sv_set_nblockMAX (sv_set_EOB (sv_set_t (sv_set_i L (sv_alphaSize L)) (sv_nGroups L))
      (d_nInUse D + 1)) (100000 * d_bs100k D)) (-1)) 0) 256) 0) 0) (BZ_G_SIZE - 1)) gSel) gMinlen) true) gMinlen.

Lemma after_tables_eq : forall L d s, 1 <= sv_nSelectors L ->
  after_tables L d s = DGo 36 (tables_L L d) (tables_d L d) s.
Proof.
  intros L d s HS. unfold after_tables, tables_L, tables_d. unfold mtf_val_start.
  cbn [sv_groupPos sv_groupNo sv_nSelectors sv_set_nblock sv_set_i sv_set_groupPos sv_set_groupNo sv_set_nblockMAX sv_set_EOB sv_set_t].
  change (0 =? 0) with true. cbv iota. replace (sv_nSelectors L <=? -1 + 1) with false by (symmetry; apply Z.leb_gt; lia).
  assert (E1 : forall x, d_nInUse (mtf_init (d_set_unzftab x (clear256 256 0 (d_unzftab x)))) = d_nInUse x).
  { intros x. unfold mtf_init. destruct (mtfinit_i _ _ _ _ _). reflexivity. }
  assert (E2 : forall x, d_bs100k (mtf_init (d_set_unzftab x (clear256 256 0 (d_unzftab x)))) = d_bs100k x).
  { intros x. unfold mtf_init. destruct (mtfinit_i _ _ _ _ _). reflexivity. }
  rewrite E1, E2. change (-1 + 1) with 0. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ws_eos (ccrc : Z) : list (Z * Z) := [(8, 23); (8, 114); (8, 69); (8, 56); (8, 80); (8, 144)] ++ ws_u32 ccrc.

Lemma seg_eos : forall ccrc L d s, 0 <= ccrc < 4294967296 ->
  dfeed (ws_eos ccrc) (DGo 14 L d s) = Some (DRet BZ_STREAM_END L (d_set_state (d_set_sccrc d ccrc) BZ_X_IDLE) s).
Proof.
  intros ccrc L d s Hc. unfold ws_eos, ws_u32. cbn [app].
  cps_destruct (u32_bytes ccrc Hc) as (B3 & B2 & B1 & B0). rewrite B3, B2, B1, B0.
  ostep gb_bits_14 gb_after_14. ostep gb_bits_42 gb_after_42. ostep gb_bits_43 gb_after_43. ostep gb_bits_44 gb_after_44.
  ostep gb_bits_45 gb_after_45. ostep gb_bits_46 gb_after_46. ostep gb_bits_47 gb_after_47. ostep gb_bits_48 gb_after_48.
  ostep gb_bits_49 gb_after_49. ostep gb_bits_50 gb_after_50. rewrite dfeed_nil.
  do 2 f_equal. dnorm d. rewrite crc_assemble by exact Hc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition map_d (f16 bit : Z -> Z) (crc op : Z) (d : dst) : dst :=
  let d0 := d_set_origPtr (d_set_rand (d_set_sbcrc (d_set_blockNo (d_set_state d 27) (d_blockNo d + 1)) crc) 0) op in
  let D := d_set_inUse16 (d_set_state d0 28) (zsets 16 0 (fun j => Some (f16 j)) (d_inUse16 d0)) in
  makeMaps_d (map_rows 16 0 f16 bit (d_set_inUse D (clear256 256 0 (d_inUse D)))).

Theorem seg_hdr_map : forall crc op f16 bit L d s,
  0 <= crc < 4294967296 -> 0 <= op < 16777216 -> op <= 10 + 100000 * d_bs100k d ->
  (forall j, 0 <= j < 16 -> f16 j = 0 \/ f16 j = 1) ->
  dfeed (ws_blk_hdr crc op ++ ws_bits16 16 f16 0 ++ ws_rows 16 f16 bit 0) (DGo 14 L d s) =
  Some (let D := map_d f16 bit crc op d in
        let L1 := sv_set_i (if anyrow 16 0 f16 then sv_set_j L 16 else L) 16 in
        if d_nInUse D =? 0 then DRet BZ_DATA_ERROR L1 D s else DGo 30 (sv_set_alphaSize L1 (d_nInUse D + 2)) D s).
Proof.
  intros crc op f16 bit L d s Hc Hop Hcap Hf.
  rewrite dfeed_app, seg_blk_hdr by assumption.
  rewrite dfeed_app, (seg_map1 16 f16 0) by (try reflexivity; try lia; exact Hf). cbv zeta.
  rewrite (seg_map2 16 17 f16 bit 0); try lia.
  2:{ intros i' Hi'. cbn [d_inUse16 d_set_inUse d_set_inUse16 d_set_state]. rewrite zsets_get.
      replace ((0 <=? i') && (i' <? 0 + Z.of_nat 16))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
      reflexivity. }
  cbv zeta. unfold map_d.
  replace (sv_set_i (if anyrow 16 0 f16 then sv_set_j (sv_set_i (sv_set_i L 0) 256) 16 else sv_set_i (sv_set_i L 0) 256) 16)
    with (sv_set_i (if anyrow 16 0 f16 then sv_set_j L 16 else L) 16) by (destruct (anyrow 16 0 f16); destruct L; reflexivity).
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition sels_d (msel : Z -> Z) (nS nG : Z) (d : dst) : dst :=
  let D := d_set_selMtf (d_set_state d 32) (zsets (Z.to_nat nS) 0 (fun k => Some (msel k)) (d_selMtf d)) in
  d_set_sel D (snd (sel_undo (Z.to_nat nS) 0 (pos_init (Z.to_nat nG) 0 znew) (d_selMtf D) (d_sel D))).
Definition lens_d (lnT : Z -> Z -> Z) (aS nG : Z) (d : dst) : dst :=
  d_set_len (d_set_state d 34) (ztabs (Z.to_nat nG) 0 (Z.to_nat aS) lnT (d_len d)).
Definition lens_L (msel : Z -> Z) (lnT : Z -> Z -> Z) (aS nG nS : Z) (L : dsv) : dsv :=
  sv_set_t (sv_set_i (sv_set_curr (sv_set_t (sv_set_i (sv_set_nSelectors (sv_set_j (sv_set_j (sv_set_i (sv_set_nSelectors (sv_set_nGroups L nG) nS) 0) 0) (msel (nS - 1))) nS) nS) 0)
    (lnT (nG - 1) (aS - 1))) aS) nG.

Theorem seg_sels_tabs : forall nG nS aS msel lnT L d s rest,
  sv_alphaSize L = aS -> 2 <= nG <= 6 -> 1 <= nS <= BZ_MAX_SELECTORS -> 1 <= aS ->
  (forall k, 0 <= k < nS -> 0 <= msel k < nG) ->
  (forall t v, 0 <= t < nG -> 0 <= v < aS -> 1 <= lnT t v <= 20) ->
  dfeed ([(3, nG); (15, nS)] ++ ws_unary (Z.to_nat nS) msel 0 ++ ws_dtables (Z.to_nat nG) lnT (Z.to_nat aS) 0 ++ rest) (DGo 30 L d s) =
  dfeed rest (let L4 := lens_L msel lnT aS nG nS L in let D4 := lens_d lnT aS nG (sels_d msel nS nG (d_set_state d 31)) in
              DGo 36 (tables_L L4 D4) (tables_d L4 D4) s).
Proof.
  intros nG nS aS msel lnT L d s rest HA HG HS HaS HM HL.
  rewrite dfeed_app, seg_sel_hdr by (unfold BZ_MAX_SELECTORS in HS; lia).
  rewrite dfeed_app, (seg_sels (Z.to_nat nS) msel 0); try (cbn [sv_i sv_j sv_nSelectors sv_nGroups sv_set_j sv_set_i sv_set_nSelectors sv_set_nGroups]; lia).
  2:{ intros k Hk. cbn [sv_nSelectors sv_nGroups sv_set_j sv_set_i sv_set_nSelectors sv_set_nGroups] in Hk |- *. apply HM. lia. }
  cbv zeta. cbn [sv_nSelectors sv_nGroups sv_set_j sv_set_i sv_set_nSelectors sv_set_nGroups d_selMtf d_sel d_set_selMtf d_set_state].
  rewrite (seg_tables (Z.to_nat nG) lnT 0 aS nG); try (cbn [sv_t sv_alphaSize sv_nGroups sv_set_t sv_set_i sv_set_nSelectors sv_set_j sv_set_nGroups]; lia).
  2:{ intros t' v Ht Hv. apply HL; lia. }
  rewrite after_tables_eq by (cbn [sv_nSelectors sv_set_t sv_set_i sv_set_curr sv_set_nSelectors sv_set_j sv_set_nGroups]; lia).
  cbv zeta. unfold lens_L, lens_d, sels_d. cbn [d_len d_set_sel d_set_selMtf d_set_state d_selMtf d_sel]. reflexivity.
Qed.
