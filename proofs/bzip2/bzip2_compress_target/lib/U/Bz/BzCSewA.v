(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCQsortM1 BzCQsortM2.

From Stdlib Require Permutation.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel BzArr BzCMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCShell. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCQsortM1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzCBudget.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCShell OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1.BzCGtU.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bytes_ok (a : zarr) : Prop := forall o, 0 <= zget a o < 256.
Definition X (a : zarr) : Z -> Z := fun p => rd32 a p.

Lemma rd32_range : forall a p, bytes_ok a -> 0 <= rd32 a p < 4294967296.
Proof. intros a p B. unfold rd32. pose proof (B (4*p)). pose proof (B (4*p+1)). pose proof (B (4*p+2)). pose proof (B (4*p+3)). lia. Qed.

Lemma bytes_ok_wr32 : forall a i v, bytes_ok a -> bytes_ok (wr32 a i v).
Proof.
  intros a i v B o. unfold wr32. rewrite !zget_zset.
  repeat (destruct (_ =? _); [apply Z.mod_pos_bound; lia|]). apply B.
Qed.

Lemma X_wr32 : forall a i v, bytes_ok a -> 0 <= v < 4294967296 -> forall p, X (wr32 a i v) p = zfupd (X a) i v p.
Proof.
  intros a i v B Hv p. unfold X. rewrite zfupd_eq. destruct (Z.eqb_spec p i) as [->|NE].
  - apply rd32_wr32_same. exact Hv.
  - apply rd32_wr32_other. exact NE.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Budget.
  Variables (a2 : zarr) (qoff n d : Z).
  Hypothesis Hn : 34 <= n <= 899990.
  Hypothesis Hd : 0 <= d <= 15.
  Hypothesis Bov : forall z, n <= z < n + 34 -> rd8 a2 z = rd8 a2 (z - n).
  Hypothesis Qov : forall z, n <= z < n + 34 -> qrd a2 qoff z = qrd a2 qoff (z - n).

  (* [comment removed for export] *)
  Definition gtbK (x y : Z) : bool := lexgtb (KEYLEN n) (kstream a2 qoff n (x + d)) (kstream a2 qoff n (y + d)).
  Lemma gtbK_gt_le : forall x y, gtbK x y = true -> le gtbK y x.
  Proof. intros x y H. unfold le, gtbK in *. apply lexgtb_asym. exact H. Qed.
  Lemma gtbK_le_trans : forall x y z, le gtbK x y -> le gtbK y z -> le gtbK x z.
  Proof. intros x y z. unfold le, gtbK. apply lexgtb_le_trans. Qed.

  Lemma mainGtU_gtbK : forall x y b, 0 <= x < n -> 0 <= y < n ->
    fst (mainGtU (x + d) (y + d) a2 qoff n b) = gtbK x y /\
    b - Z.of_nat (GT_N n) <= snd (mainGtU (x + d) (y + d) a2 qoff n b) <= b.
  Proof.
    intros x y b Hx Hy. unfold gtbK.
    apply (mainGtU_spec a2 qoff n ltac:(lia) Bov Qov); lia.
  Qed.

  Lemma GT_N_bound : Z.of_nat (GT_N n) <= 112501.
  Proof.
    unfold GT_N. assert ((n + 8) / 8 < 112500) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= (n + 8) / 8) by (apply Z.div_pos; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Definition prange (a1 : zarr) (lo hi : Z) : Prop := forall p, lo <= p <= hi -> 0 <= X a1 p < n.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mss_shift_sim : forall fuel a1 x h lo hi j v budget (cnt : nat),
    bytes_ok a1 -> prange a1 lo hi -> (forall p, X a1 p = x p) -> 0 <= v < n -> 0 < h -> lo + h <= j <= hi ->
    let '(a1', j', b') := mss_shift fuel a1 a2 qoff n d h lo j v budget in
    let '(x', j'', cnt') := shift gtbK fuel x lo h j v cnt in
    j' = j'' /\ (forall p, X a1' p = x' p) /\ bytes_ok a1' /\ prange a1' lo hi /\ (cnt <= cnt')%nat /\
    budget - Z.of_nat (GT_N n) * (Z.of_nat (cnt' - cnt) + 1) <= b' <= budget.
  Proof.
    induction fuel as [|fuel IH]; intros a1 x h lo hi j v budget cnt BY PR EX Hv Hh Hj.
    - cbn. split; [reflexivity|]. split; [exact EX|]. split; [exact BY|]. split; [exact PR|]. split; [lia|]. nia.
    - cbn [mss_shift shift].
      pose proof (PR (j - h) ltac:(lia)) as Rjh.
      pose proof (mainGtU_gtbK (X a1 (j - h)) v budget Rjh Hv) as [G1 G2].
      change (rd32 a1 (j - h)) with (X a1 (j - h)).
      destruct (mainGtU (X a1 (j - h) + d) (v + d) a2 qoff n budget) as [gt b1].
      cbn [fst snd] in G1, G2. subst gt.
      replace (gtbK (x (j - h)) v) with (gtbK (X a1 (j - h)) v) by (rewrite EX; reflexivity).
      destruct (gtbK (X a1 (j - h)) v) eqn:G.
      + pose proof (rd32_range a1 (j - h) BY) as WR. change (rd32 a1 (j - h)) with (X a1 (j - h)) in WR.
        assert (BY' : bytes_ok (wr32 a1 j (X a1 (j - h)))) by (apply bytes_ok_wr32; exact BY).
        assert (EX' : forall p, X (wr32 a1 j (X a1 (j - h))) p = zfupd x j (x (j - h)) p).
        { intros p. rewrite X_wr32 by assumption. rewrite !zfupd_eq. destruct (p =? j); [apply EX| apply EX]. }
        assert (PR' : prange (wr32 a1 j (X a1 (j - h))) lo hi).
        { intros p Hp. rewrite X_wr32 by assumption. rewrite zfupd_eq. destruct (p =? j); apply PR; lia. }
        destruct (Z.leb_spec (j - h) (lo + h - 1)) as [L|L].
        * split; [reflexivity|]. split; [exact EX'|]. split; [exact BY'|]. split; [exact PR'|]. split; [lia|].
          replace (Z.of_nat (S cnt - cnt)) with 1 by lia. lia.
        * specialize (IH (wr32 a1 j (X a1 (j - h))) (zfupd x j (x (j - h))) h lo hi (j - h) v b1 (S cnt) BY' PR' EX' Hv Hh ltac:(lia)).
          destruct (mss_shift fuel (wr32 a1 j (X a1 (j - h))) a2 qoff n d h lo (j - h) v b1) as [[a1' j'] b'].
          destruct (shift gtbK fuel (zfupd x j (x (j - h))) lo h (j - h) v (S cnt)) as [[x' j''] cnt'].
          cps_destruct IH as (A1 & A2 & A3 & A4 & A5 & A6).
          split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [lia|].
          replace (Z.of_nat (cnt' - cnt)) with (Z.of_nat (cnt' - S cnt) + 1) by lia. nia.
      + cbn. split; [reflexivity|]. split; [exact EX|]. split; [exact BY|]. split; [exact PR|]. split; [lia|].
        replace (cnt - cnt)%nat with 0%nat by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mss_ins_sim : forall a1 x h lo hi i budget,
    bytes_ok a1 -> prange a1 lo hi -> (forall p, X a1 p = x p) -> 0 < h -> lo + h <= i <= hi ->
    let '(a1', b') := mss_ins a1 a2 qoff n d h lo i budget in
    let '(x', s) := ins gtbK x lo h i in
    (forall p, X a1' p = x' p) /\ bytes_ok a1' /\ prange a1' lo hi /\
    budget - Z.of_nat (GT_N n) * (Z.of_nat s + 1) <= b' <= budget.
  Proof.
    intros a1 x h lo hi i budget BY PR EX Hh Hi. unfold mss_ins, ins.
    pose proof (PR i ltac:(lia)) as Ri.
    pose proof (mss_shift_sim (S (Z.to_nat (i - lo))) a1 x h lo hi i (X a1 i) budget 0 BY PR EX Ri Hh ltac:(lia)) as SIM.
    change (rd32 a1 i) with (X a1 i). rewrite <- (EX i).
    destruct (mss_shift (S (Z.to_nat (i - lo))) a1 a2 qoff n d h lo i (X a1 i) budget) as [[a1' j'] b'].
    destruct (shift gtbK (S (Z.to_nat (i - lo))) x lo h i (X a1 i) 0) as [[x' j''] cnt'].
    cps_destruct SIM as (A1 & A2 & A3 & A4 & A5 & A6). subst j''. cbn [fst snd].
    pose proof (rd32_range a1 i BY) as WR. change (rd32 a1 i) with (X a1 i) in WR.
    split; [|split; [apply bytes_ok_wr32; exact A3| split]].
    - intros p. rewrite X_wr32 by assumption. rewrite !zfupd_eq. destruct (p =? j'); [reflexivity| apply A2].
    - intros p Hp. rewrite X_wr32 by assumption. rewrite zfupd_eq. destruct (p =? j'); [exact Ri| apply A4; exact Hp].
    - rewrite Nat.sub_0_r in A6. exact A6.
  Qed.

  (* [comment removed for export] *)
  Theorem mss_ins_cost : forall (x0 : Z -> Z) a1 x h lo hi i budget,
    bytes_ok a1 -> prange a1 lo hi -> (forall p, X a1 p = x p) -> 0 < h -> lo + h <= i <= hi ->
    pass_inv gtbK x0 x lo h i ->
    let '(a1', b') := mss_ins a1 a2 qoff n d h lo i budget in
    budget - Z.of_nat (GT_N n) * ((i - lo) / h + 1) <= b' <= budget /\
    (hsorted gtbK x0 lo (hi + 1) (3 * h + 1) -> hsorted gtbK x0 lo (hi + 1) (9 * h + 4) ->
     budget - Z.of_nat (GT_N n) * (27 * h + 10) <= b').
  Proof.
    intros x0 a1 x h lo hi i budget BY PR EX Hh Hi PI.
    pose proof (mss_ins_sim a1 x h lo hi i budget BY PR EX Hh Hi) as SIM.
    pose proof (ins_shift_bound gtbK gtbK_gt_le gtbK_le_trans x0 x lo h i (hi + 1) Hh ltac:(lia) ltac:(lia) PI) as KB.
    pose proof (ins_result gtbK x lo h i Hh ltac:(lia)) as IR.
    destruct (mss_ins a1 a2 qoff n d h lo i budget) as [a1' b'].
    destruct (ins gtbK x lo h i) as [x' s]. cbn [snd] in KB. cps_destruct SIM as (_ & _ & _ & COST).
    destruct IR as (LO & _).
    (* [comment removed for export] *)
    assert (SC : Z.of_nat s <= (i - lo) / h).
    { apply Z.div_le_lower_bound; [lia|]. nia. }
    pose proof GT_N_bound as GB.
    split; [nia|]. intros SA SB. specialize (KB SA SB). nia.
  Qed.

  (* [comment removed for export] *)
  Definition CALLMAX : Z := 3277.
  Definition CI : Z := 112501 * CALLMAX.      (* [comment removed for export] *)
  Lemma five_CI_int32 : 5 * CI < 2147483648.
  Proof. unfold CI, CALLMAX. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac by_cases13 k tac :=
    let C := fresh "C" in
    assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia;
    repeat (destruct C as [C|C]; [rewrite C; tac|]); rewrite C; tac.
  Ltac leb_compute := apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity.
  (* [comment removed for export] *)

  Lemma incs_step : forall k, 0 <= k <= 12 -> incs_at (k + 1) = 3 * incs_at k + 1.
  Proof. intros k Hk. by_cases13 k ltac:(vm_compute; reflexivity). Qed.
  Lemma incs_pos : forall k, 0 <= k <= 12 -> 1 <= incs_at k.
  Proof. intros k Hk. by_cases13 k leb_compute. Qed.
  Lemma incs_13 : incs_at 13 = 2391484. Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma incs_callmax : forall k, 0 <= k <= 12 -> let h := incs_at k in
    (899989 / h + 1 <= CALLMAX) \/ (27 * h + 10 <= CALLMAX).
  Proof.
    intros k Hk. unfold CALLMAX. cbv zeta.
    by_cases13 k ltac:(first [right; leb_compute | left; leb_compute]).
  Qed.

  Lemma incs_mono : forall dn j, 0 <= j -> j + Z.of_nat dn <= 13 -> incs_at j <= incs_at (j + Z.of_nat dn).
  Proof.
    induction dn as [|dn IH]; intros j Hj Hdn.
    - rewrite Z.add_0_r. lia.
    - replace (j + Z.of_nat (S dn)) with (j + Z.of_nat dn + 1) by lia.
      rewrite incs_step by lia. pose proof (IH j Hj ltac:(lia)). pose proof (incs_pos (j + Z.of_nat dn) ltac:(lia)). lia.
  Qed.
  Lemma incs_le : forall j k, 0 <= j <= k -> k <= 13 -> incs_at j <= incs_at k.
  Proof.
    intros j k Hjk Hk. replace k with (j + Z.of_nat (Z.to_nat (k - j))) by lia. apply incs_mono; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Range.
  Variables (lo hi : Z).
  Hypothesis Hlh : 0 <= lo <= hi /\ hi - lo + 1 <= n.

  (* [comment removed for export] *)
  Definition cheap (x0 : Z -> Z) (h : Z) : Prop :=
    (hi - lo) / h + 1 <= CALLMAX \/
    (hsorted gtbK x0 lo (hi + 1) (3 * h + 1) /\ hsorted gtbK x0 lo (hi + 1) (9 * h + 4) /\ 27 * h + 10 <= CALLMAX).

  Lemma ins_cost_CI : forall (x0 : Z -> Z) a1 x h i budget,
    cheap x0 h -> bytes_ok a1 -> prange a1 lo hi -> (forall p, X a1 p = x p) -> 0 < h -> lo + h <= i <= hi ->
    pass_inv gtbK x0 x lo h i ->
    budget - CI <= snd (mss_ins a1 a2 qoff n d h lo i budget) <= budget.
  Proof.
    intros x0 a1 x h i budget CH BY PR EX Hh Hi PI.
    pose proof (mss_ins_cost x0 a1 x h lo hi i budget BY PR EX Hh Hi PI) as C.
    destruct (mss_ins a1 a2 qoff n d h lo i budget) as [a1' b']. cbn [snd]. destruct C as [C1 C2].
    pose proof GT_N_bound as GB. unfold CI.
    assert (DM : (i - lo) / h <= (hi - lo) / h) by (apply Z.div_le_mono; lia).
    assert (D0 : 0 <= (i - lo) / h) by (apply Z.div_pos; lia).
    destruct CH as [CH|(SA & SB & CH)].
    - split; [|lia]. nia.
    - specialize (C2 SA SB). split; [|lia]. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma hloop_sim : forall fuel a1 (x0 x : Z -> Z) h i budget,
    cheap x0 h -> 0 < h -> lo + h <= i <= hi + 1 -> bytes_ok a1 -> prange a1 lo hi -> (forall p, X a1 p = x p) ->
    pass_inv gtbK x0 x lo h i -> hi + 1 - i + 1 <= Z.of_nat fuel ->
    let '(a1', b', ex) := mss_hloop fuel a1 a2 qoff n d h lo hi i budget in
    bytes_ok a1' /\ prange a1' lo hi /\
    (ex = false -> (forall p, X a1' p = pass_upto gtbK (Z.to_nat (hi + 1 - i)) x lo h i p) /\
                   (if 3 <=? hi + 1 - i then - (2 * CI) <= b' else budget - 2 * CI <= b')) /\
    Z.min budget 0 - 3 * CI <= b'.
  Proof.
    induction fuel as [|fuel IH]; intros a1 x0 x h i budget CH Hh Hi BY PR EX PI HF; [cbn in HF; lia|].
    cbn [mss_hloop].
    pose proof five_CI_int32 as F5. assert (CI0 : 0 <= CI) by (unfold CI, CALLMAX; lia).
    destruct (Z.ltb_spec hi i) as [L1|L1].
    { split; [exact BY|]. split; [exact PR|]. split; [|lia]. intros _.
      replace (Z.to_nat (hi + 1 - i)) with 0%nat by lia. cbn [pass_upto]. split; [exact EX|].
      replace (3 <=? hi + 1 - i) with false by (symmetry; apply Z.leb_gt; lia). lia. }
    (* [comment removed for export] *)
    pose proof (ins_cost_CI x0 a1 x h i budget CH BY PR EX Hh ltac:(lia) PI) as C1.
    pose proof (mss_ins_sim a1 x h lo hi i budget BY PR EX Hh ltac:(lia)) as S1.
    pose proof (ins_preserves gtbK gtbK_gt_le x0 x lo h i Hh ltac:(lia) PI) as PI1.
    destruct (mss_ins a1 a2 qoff n d h lo i budget) as [a11 b1]. cbn [snd] in C1.
    destruct (ins gtbK x lo h i) as [x1 s1] eqn:INS1. cbn [fst] in PI1. cps_destruct S1 as (EX1 & BY1 & PR1 & _).
    destruct (Z.ltb_spec hi (i + 1)) as [L2|L2].
    { split; [exact BY1|]. split; [exact PR1|]. split; [|lia]. intros _.
      replace (Z.to_nat (hi + 1 - i)) with 1%nat by lia. cbn [pass_upto]. rewrite INS1. cbn [fst]. split; [exact EX1|].
      replace (3 <=? hi + 1 - i) with false by (symmetry; apply Z.leb_gt; lia). lia. }
    (* [comment removed for export] *)
    pose proof (ins_cost_CI x0 a11 x1 h (i + 1) b1 CH BY1 PR1 EX1 Hh ltac:(lia) PI1) as C2.
    pose proof (mss_ins_sim a11 x1 h lo hi (i + 1) b1 BY1 PR1 EX1 Hh ltac:(lia)) as S2.
    pose proof (ins_preserves gtbK gtbK_gt_le x0 x1 lo h (i + 1) Hh ltac:(lia) PI1) as PI2.
    destruct (mss_ins a11 a2 qoff n d h lo (i + 1) b1) as [a12 b2]. cbn [snd] in C2.
    destruct (ins gtbK x1 lo h (i + 1)) as [x2 s2] eqn:INS2. cbn [fst] in PI2. cps_destruct S2 as (EX2 & BY2 & PR2 & _).
    destruct (Z.ltb_spec hi (i + 1 + 1)) as [L3|L3].
    { split; [exact BY2|]. split; [exact PR2|]. split; [|lia]. intros _.
      replace (Z.to_nat (hi + 1 - i)) with 2%nat by lia. cbn [pass_upto]. rewrite INS1. cbn [fst]. rewrite INS2. cbn [fst]. split; [exact EX2|].
      replace (3 <=? hi + 1 - i) with false by (symmetry; apply Z.leb_gt; lia). lia. }
    (* [comment removed for export] *)
    pose proof (ins_cost_CI x0 a12 x2 h (i + 1 + 1) b2 CH BY2 PR2 EX2 Hh ltac:(lia) PI2) as C3.
    pose proof (mss_ins_sim a12 x2 h lo hi (i + 1 + 1) b2 BY2 PR2 EX2 Hh ltac:(lia)) as S3.
    pose proof (ins_preserves gtbK gtbK_gt_le x0 x2 lo h (i + 1 + 1) Hh ltac:(lia) PI2) as PI3.
    destruct (mss_ins a12 a2 qoff n d h lo (i + 1 + 1) b2) as [a13 b3]. cbn [snd] in C3.
    destruct (ins gtbK x2 lo h (i + 1 + 1)) as [x3 s3] eqn:INS3. cbn [fst] in PI3. cps_destruct S3 as (EX3 & BY3 & PR3 & _).
    replace (3 <=? hi + 1 - i) with true by (symmetry; apply Z.leb_le; lia).
    destruct (Z.ltb_spec b3 0) as [NEG|NNEG].
    { split; [exact BY3|]. split; [exact PR3|]. split; [discriminate| lia]. }
    (* [comment removed for export] *)
    specialize (IH a13 x0 x3 h (i + 1 + 1 + 1) b3 CH Hh ltac:(lia) BY3 PR3 EX3 PI3 ltac:(lia)).
    destruct (mss_hloop fuel a13 a2 qoff n d h lo hi (i + 1 + 1 + 1) b3) as [[a1' b'] ex].
    cps_destruct IH as (BY' & PR' & CF & LB).
    split; [exact BY'|]. split; [exact PR'|]. split; [|lia].
    intros Hex. destruct (CF Hex) as [XE BB]. split.
    - intros p. rewrite XE.
      replace (Z.to_nat (hi + 1 - i)) with (3 + Z.to_nat (hi + 1 - (i + 1 + 1 + 1)))%nat by lia.
      rewrite (pass_upto_app gtbK). cbn [pass_upto]. rewrite INS1. cbn [fst]. rewrite INS2. cbn [fst].
      replace (i + 1 + 1) with (i + 1 + 1) by lia. rewrite INS3. cbn [fst].
      replace (i + Z.of_nat 3) with (i + 1 + 1 + 1) by lia. reflexivity.
    - destruct (3 <=? hi + 1 - (i + 1 + 1 + 1)); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hps_sim : forall m a1 hp hp0 budget,
    0 <= hp0 <= 12 -> incs_at hp0 < hi - lo + 1 <= incs_at (hp0 + 1) ->
    0 <= hp <= hp0 -> Z.of_nat m = hp + 1 ->
    bytes_ok a1 -> prange a1 lo hi ->
    (hp + 1 <= hp0 -> hsorted gtbK (X a1) lo (hi + 1) (incs_at (hp + 1))) ->
    (hp + 2 <= hp0 -> hsorted gtbK (X a1) lo (hi + 1) (incs_at (hp + 2))) ->
    (hp = hp0 -> 0 <= budget) -> - (2 * CI) <= budget ->
    let '(a1', b', ex) := mss_hps m a1 a2 qoff n d lo hi hp budget in - (5 * CI) <= b'.
  Proof.
    induction m as [|m IH]; intros a1 hp hp0 budget H0 HB Hhp Hm BY PR S1 S2 B0 B2; [lia|].
    cbn [mss_hps]. pose proof five_CI_int32 as F5. assert (CI0 : 0 <= CI) by (unfold CI, CALLMAX; lia).
    set (h := incs_at hp).
    pose proof (incs_pos hp ltac:(lia)) as HP. fold h in HP.
    pose proof (incs_step hp ltac:(lia)) as ST. fold h in ST.
    pose proof (incs_step hp0 ltac:(lia)) as ST0.
    pose proof (incs_le hp hp0 ltac:(lia) ltac:(lia)) as LE0. fold h in LE0.
    (* [comment removed for export] *)
    assert (INS3 : hp <> hp0 -> 3 <= hi + 1 - (lo + h)).
    { intros NE. pose proof (incs_le (hp + 1) hp0 ltac:(lia) ltac:(lia)) as LE1. rewrite ST in LE1. lia. }
    (* [comment removed for export] *)
    assert (CH : cheap (X a1) h).
    { unfold cheap. destruct (Z_lt_le_dec (hp + 1) hp0) as [K|K].
      - destruct (incs_callmax hp ltac:(lia)) as [T|T]; fold h in T.
        + left. assert ((hi - lo) / h <= 899989 / h) by (apply Z.div_le_mono; lia). lia.
        + right. split; [|split; [|exact T]].
          * rewrite <- ST. apply S1. lia.
          * pose proof (incs_step (hp + 1) ltac:(lia)) as ST2. rewrite ST in ST2. replace (hp + 1 + 1) with (hp + 2) in ST2 by lia.
            replace (9 * h + 4) with (incs_at (hp + 2)) by lia. apply S2. lia.
      - left. unfold CALLMAX.
        assert (hi - lo < 9 * h + 4).
        { destruct (Z.eq_dec hp hp0) as [E|E].
          - rewrite <- E in HB, ST0. fold h in HB. lia.
          - assert (E1 : hp + 1 = hp0) by lia. rewrite E1 in ST. rewrite ST in ST0. rewrite <- E1 in HB at 2.
            replace (hp + 1 + 1) with (hp0 + 1) in HB by lia. lia. }
        assert ((hi - lo) / h < 13) by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (hloop_sim (S (Z.to_nat (hi - lo + 1))) a1 (X a1) (X a1) h (lo + h) budget CH ltac:(lia) ltac:(lia) BY PR
                  ltac:(intros; reflexivity) (pass_inv_init gtbK (X a1) lo h ltac:(lia)) ltac:(lia)) as HL.
    destruct (mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qoff n d h lo hi (lo + h) budget) as [[a1' b'] ex].
    cps_destruct HL as (BY' & PR' & CF & LB).
    destruct ex; [lia|].
    destruct (CF eq_refl) as [XE BB].
    assert (B2' : - (2 * CI) <= b').
    { destruct (Z.leb_spec 3 (hi + 1 - (lo + h))) as [T|T]; [exact BB|].
      destruct (Z.eq_dec hp hp0) as [E|E]; [specialize (B0 E); lia|]. specialize (INS3 E). lia. }
    destruct m as [|m'].
    { cbn [mss_hps]. lia. }
    pose proof (hpass_hsorted gtbK gtbK_gt_le (X a1) lo h (hi + 1) ltac:(lia) ltac:(lia)) as HS1. unfold hpass in HS1.
    apply (IH a1' (hp - 1) hp0 b' H0 HB ltac:(lia) ltac:(lia) BY' PR').
    - intros _. replace (hp - 1 + 1) with hp by lia. fold h.
      apply (hsorted_ext gtbK _ _ lo (hi + 1) h ltac:(intros p; symmetry; apply XE)). exact HS1.
    - intros K2. replace (hp - 1 + 2) with (hp + 1) by lia.
      apply (hsorted_ext gtbK _ _ lo (hi + 1) (incs_at (hp + 1)) ltac:(intros p; symmetry; apply XE)).
      pose proof (hpass_keeps_ksorted gtbK gtbK_gt_le gtbK_le_trans (X a1) lo h (hi + 1) (incs_at (hp + 1)) ltac:(lia)
                    ltac:(pose proof (incs_pos (hp + 1) ltac:(lia)); lia) ltac:(lia) (S1 ltac:(lia))) as HS.
      unfold hpass in HS. exact HS.
    - intros E. lia.
    - exact B2'.
  Qed.

  (* [comment removed for export] *)
  Lemma mss_hp_run : forall fuel bigN hp, 0 <= hp <= 13 -> bigN <= incs_at 13 -> (13 - hp < Z.of_nat fuel) ->
    let r := mss_hp fuel bigN hp in hp <= r <= 13 /\ bigN <= incs_at r /\ (hp < r -> incs_at (r - 1) < bigN).
  Proof.
    induction fuel as [|fuel IH]; intros bigN hp Hhp HN Hf; [change (Z.of_nat 0%nat) with 0 in Hf; lia|].
    cbn [mss_hp]. destruct (Z.ltb_spec (incs_at hp) bigN) as [L|L].
    - assert (hp < 13) by (destruct (Z.eq_dec hp 13) as [E|E]; [rewrite E in L; lia| lia]).
      specialize (IH bigN (hp + 1) ltac:(lia) HN ltac:(lia)). cbv zeta in IH. cps_destruct IH as (A & B0 & C).
      split; [lia|]. split; [exact B0|]. intros _. destruct (Z.eq_dec (hp + 1) (mss_hp fuel bigN (hp + 1))) as [E|E].
      + rewrite <- E. replace (hp + 1 - 1) with hp by lia. exact L.
      + apply C. lia.
    - split; [lia|]. split; [exact L| intros; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem mainSimpleSort_budget : forall a1 budget,
    bytes_ok a1 -> prange a1 lo hi -> 0 <= budget ->
    - (5 * CI) <= snd (mainSimpleSort a1 a2 qoff n lo hi d budget).
  Proof.
    intros a1 budget BY PR B0. unfold mainSimpleSort.
    pose proof five_CI_int32 as F5. assert (CI0 : 0 <= CI) by (unfold CI, CALLMAX; lia).
    destruct (Z.ltb_spec (hi - lo + 1) 2) as [S|S]; [cbn [snd]; lia|].
    pose proof (mss_hp_run 15 (hi - lo + 1) 0 ltac:(lia) ltac:(rewrite incs_13; lia) ltac:(cbn; lia)) as R. cbv zeta in R.
    set (r := mss_hp 15 (hi - lo + 1) 0) in *. cps_destruct R as (R1 & R2 & R3).
    assert (R0 : 0 < r).
    { destruct (Z.eq_dec r 0) as [E|E]; [|lia]. exfalso. rewrite E in R2. change (incs_at 0) with 1 in R2. lia. }
    specialize (R3 ltac:(lia)).
    pose proof (hps_sim (Z.to_nat (r - 1 + 1)) a1 (r - 1) (r - 1) budget ltac:(lia)
                  ltac:(replace (r - 1 + 1) with r by lia; lia) ltac:(lia) ltac:(lia) BY PR
                  ltac:(intros; lia) ltac:(intros; lia) ltac:(intros; lia) ltac:(lia)) as H.
    destruct (mss_hps (Z.to_nat (r - 1 + 1)) a1 a2 qoff n d lo hi (r - 1) budget) as [[a1' b'] ex]. cbn [snd]. exact H.
  Qed.

  Corollary mainSimpleSort_budget_int32 : forall a1 budget,
    bytes_ok a1 -> prange a1 lo hi -> 0 <= budget ->
    - 2147483648 < snd (mainSimpleSort a1 a2 qoff n lo hi d budget).
  Proof. intros a1 budget BY PR B0. pose proof (mainSimpleSort_budget a1 budget BY PR B0). pose proof five_CI_int32. lia. Qed.
  End Range.
End Budget.
End BzCBudget.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA.BzCBudget.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Lemma mswap_fswap : forall a x y, mswap a x y = fswap a x y.
Proof. reflexivity. Qed.
Lemma mvswap_S : forall f a1 p1 p2 n, mvswap (S f) a1 p1 p2 n = (if 0 <? n then mvswap f (mswap a1 p1 p2) (p1 + 1) (p2 + 1) (n - 1) else a1).
Proof. reflexivity. Qed.

Section SEWA.
  Variable nb : Z.
  Hypothesis NB : nb <= 4294967296.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mvswap_perm_frame : forall f a1 p1 p2 n lo hi,
    fm_perm a1 nb -> 0 <= lo -> hi < nb ->
    lo <= p1 -> p1 + n <= hi + 1 -> lo <= p2 -> p2 + n <= hi + 1 ->
    fm_perm (mvswap f a1 p1 p2 n) nb /\ frame_out a1 (mvswap f a1 p1 p2 n) lo hi.
  Proof.
    induction f as [|f IH]; intros a1 p1 p2 n lo hi PM Hlo Hhi A1 A2 B1 B2.
    - cbn [mvswap]. split; [exact PM | apply frame_out_refl].
    - rewrite mvswap_S. destruct (Z.ltb_spec 0 n) as [Hn|Hn]; [|split; [exact PM | apply frame_out_refl]].
      rewrite mswap_fswap.
      destruct (IH (fswap a1 p1 p2) (p1 + 1) (p2 + 1) (n - 1) lo hi) as [P F];
        [apply fm_perm_fswap; try assumption; lia | lia | lia | lia | lia | lia | lia |].
      split; [exact P|]. eapply frame_out_trans; [|exact F]. apply frame_out_fswap; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section MPart.
    Variables (a2 : zarr) (d med : Z).

    Definition MPB (lo hi : Z) (p : mpart) : Prop :=
      lo <= mp_ltLo p /\ mp_ltLo p <= mp_unLo p /\ mp_unHi p <= mp_gtHi p /\ mp_gtHi p <= hi.
    Definition MPF (a0 : zarr) (lo hi : Z) (p : mpart) : Prop :=
      MPB lo hi p /\ fm_perm (mp_a1 p) nb /\ frame_out a0 (mp_a1 p) lo hi.

    Lemma mpf_lo : forall f a0 lo hi p, 0 <= lo -> hi < nb -> MPF a0 lo hi p ->
      MPF a0 lo hi (mpart_lo f a2 d med p) /\ mp_unHi (mpart_lo f a2 d med p) = mp_unHi p /\ mp_gtHi (mpart_lo f a2 d med p) = mp_gtHi p.
    Proof.
      induction f as [|f IH]; intros a0 lo hi p Hlo Hhi HP.
      - cbn [mpart_lo]. split; [exact HP|split; reflexivity].
      - rewrite mpart_lo_S. cbv zeta. destruct (Z.ltb_spec (mp_unHi p) (mp_unLo p)) as [LT|GE]; [split; [exact HP|split; reflexivity]|].
        cps_destruct HP as ((A & B & D & E) & PM & FR).
        destruct (Z.eqb_spec (rd8 a2 (rd32 (mp_a1 p) (mp_unLo p) + d) - med) 0) as [EQ|NE].
        + match goal with |- MPF _ _ _ (mpart_lo f a2 d med ?q) /\ _ => destruct (IH a0 lo hi q Hlo Hhi) as (P1 & P2 & P3) end.
          { split; [unfold MPB; cbn; lia|]. cbn [mp_a1]. rewrite mswap_fswap. split.
            - apply fm_perm_fswap; try assumption; lia.
            - eapply frame_out_trans; [exact FR|]. apply frame_out_fswap; lia. }
          cbn [mp_unHi mp_gtHi] in P2, P3. split; [exact P1|split; assumption].
        + destruct (Z.ltb_spec 0 (rd8 a2 (rd32 (mp_a1 p) (mp_unLo p) + d) - med)) as [GT|LE].
          * split; [|split; reflexivity]. split; [unfold MPB; lia|]. split; assumption.
          * match goal with |- MPF _ _ _ (mpart_lo f a2 d med ?q) /\ _ => destruct (IH a0 lo hi q Hlo Hhi) as (P1 & P2 & P3) end.
            { split; [unfold MPB; cbn; lia|]. cbn [mp_a1]. split; assumption. }
            cbn [mp_unHi mp_gtHi] in P2, P3. split; [exact P1|split; assumption].
    Qed.

    Lemma mpf_hi : forall f a0 lo hi p, 0 <= lo -> hi < nb -> MPF a0 lo hi p ->
      MPF a0 lo hi (mpart_hi f a2 d med p) /\ mp_unLo (mpart_hi f a2 d med p) = mp_unLo p /\ mp_ltLo (mpart_hi f a2 d med p) = mp_ltLo p.
    Proof.
      induction f as [|f IH]; intros a0 lo hi p Hlo Hhi HP.
      - cbn [mpart_hi]. split; [exact HP|split; reflexivity].
      - rewrite mpart_hi_S. cbv zeta. destruct (Z.ltb_spec (mp_unHi p) (mp_unLo p)) as [LT|GE]; [split; [exact HP|split; reflexivity]|].
        cps_destruct HP as ((A & B & D & E) & PM & FR).
        destruct (Z.eqb_spec (rd8 a2 (rd32 (mp_a1 p) (mp_unHi p) + d) - med) 0) as [EQ|NE].
        + match goal with |- MPF _ _ _ (mpart_hi f a2 d med ?q) /\ _ => destruct (IH a0 lo hi q Hlo Hhi) as (P1 & P2 & P3) end.
          { split; [unfold MPB; cbn; lia|]. cbn [mp_a1]. rewrite mswap_fswap. split.
            - apply fm_perm_fswap; try assumption; lia.
            - eapply frame_out_trans; [exact FR|]. apply frame_out_fswap; lia. }
          cbn [mp_unLo mp_ltLo] in P2, P3. split; [exact P1|split; assumption].
        + destruct (Z.ltb_spec (rd8 a2 (rd32 (mp_a1 p) (mp_unHi p) + d) - med) 0) as [LTm|GEm].
          * split; [|split; reflexivity]. split; [unfold MPB; lia|]. split; assumption.
          * match goal with |- MPF _ _ _ (mpart_hi f a2 d med ?q) /\ _ => destruct (IH a0 lo hi q Hlo Hhi) as (P1 & P2 & P3) end.
            { split; [unfold MPB; cbn; lia|]. cbn [mp_a1]. split; assumption. }
            cbn [mp_unLo mp_ltLo] in P2, P3. split; [exact P1|split; assumption].
    Qed.

    Lemma mpf_loop : forall f sz a0 lo hi p, 0 <= lo -> hi < nb -> MPF a0 lo hi p -> MPF a0 lo hi (mpart_loop f sz a2 d med p).
    Proof.
      induction f as [|f IH]; intros sz a0 lo hi p Hlo Hhi HP.
      - cbn [mpart_loop]. exact HP.
      - rewrite mpart_loop_S. cbv zeta.
        cps_destruct (mpf_lo (S sz) a0 lo hi p Hlo Hhi HP) as (P1 & _ & _).
        cps_destruct (mpf_hi (S sz) a0 lo hi _ Hlo Hhi P1) as (P2 & _ & _).
        set (p2 := mpart_hi (S sz) a2 d med (mpart_lo (S sz) a2 d med p)) in *. clearbody p2.
        destruct (Z.ltb_spec (mp_unHi p2) (mp_unLo p2)) as [LT|GE]; [exact P2|].
        apply IH; [exact Hlo | exact Hhi |].
        cps_destruct P2 as ((A & B & D & E) & PM & FR).
        split; [unfold MPB; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]; lia|]. cbn [mp_a1]. rewrite mswap_fswap. split.
        + apply fm_perm_fswap; try assumption; lia.
        + eapply frame_out_trans; [exact FR|]. apply frame_out_fswap; lia.
    Qed.
  End MPart.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section MSS.
    Variables (a2 : zarr) (qoff nblock d : Z).

    Lemma mss_shift_S : forall f a1 h lo j v budget,
      mss_shift (S f) a1 a2 qoff nblock d h lo j v budget =
      (let '(gt, budget) := mainGtU (rd32 a1 (j - h) + d) (v + d) a2 qoff nblock budget in
       if gt then
         let a1 := wr32 a1 j (rd32 a1 (j - h)) in
         let j := j - h in
         if j <=? lo + h - 1 then (a1, j, budget) else mss_shift f a1 a2 qoff nblock d h lo j v budget
       else (a1, j, budget)).
    Proof. reflexivity. Qed.

    (* [comment removed for export] *)
    Definition filled (a1 : zarr) (j v : Z) : zarr := wr32 a1 j v.

    Lemma hole_move : forall a1 j h v, 0 < h -> 0 <= v < 4294967296 -> 0 <= rd32 a1 (j - h) < 4294967296 ->
      forall x, rd32 (filled (wr32 a1 j (rd32 a1 (j - h))) (j - h) v) x = rd32 (fswap (filled a1 j v) j (j - h)) x.
    Proof.
      intros a1 j h v Hh Hv Hj x. unfold filled, fswap.
      rewrite (rd32_wr32_other a1 j v (j - h)) by lia. rewrite rd32_wr32_same by lia.
      destruct (Z.eq_dec x (j - h)) as [->|N1].
      - rewrite !rd32_wr32_same by lia. reflexivity.
      - rewrite (rd32_wr32_other _ (j - h) v x) by lia. rewrite (rd32_wr32_other _ (j - h) v x) by lia.
        destruct (Z.eq_dec x j) as [->|N2].
        + rewrite !rd32_wr32_same by lia. reflexivity.
        + rewrite !rd32_wr32_other by lia. reflexivity.
    Qed.

    Lemma mss_shift_hole : forall f a1 h lo hi j v budget a0,
      0 < h -> 0 <= lo -> hi < nb -> lo + h <= j <= hi -> 0 <= v < 4294967296 ->
      fm_perm (filled a1 j v) nb -> frame_out a0 (filled a1 j v) lo hi ->
      let r := mss_shift f a1 a2 qoff nblock d h lo j v budget in
      lo <= snd (fst r) <= hi /\ fm_perm (filled (fst (fst r)) (snd (fst r)) v) nb /\ frame_out a0 (filled (fst (fst r)) (snd (fst r)) v) lo hi.
    Proof.
      induction f as [|f IH]; intros a1 h lo hi j v budget a0 Hh Hlo Hhi Hj Hv PM FR; cbv zeta.
      - cbn [mss_shift fst snd]. split; [lia|]. split; [exact PM| exact FR].
      - rewrite mss_shift_S. destruct (mainGtU _ _ _ _ _ _) as [gt budget']. destruct gt.
        2:{ cbn [fst snd]. split; [lia|]. split; [exact PM| exact FR]. }
        cbv zeta.
        assert (RJ : 0 <= rd32 a1 (j - h) < nb).
        { rewrite <- (rd32_wr32_other a1 j v (j - h)) by lia. apply (proj1 PM). lia. }
        assert (PM' : fm_perm (filled (wr32 a1 j (rd32 a1 (j - h))) (j - h) v) nb).
        { eapply fm_perm_ext. { apply (fm_perm_fswap _ nb j (j - h) PM NB); lia. } intros x Hx. apply hole_move; lia. }
        assert (FR' : frame_out a0 (filled (wr32 a1 j (rd32 a1 (j - h))) (j - h) v) lo hi).
        { eapply frame_out_trans; [exact FR|]. intros x Hx. rewrite hole_move by lia. apply (frame_out_fswap _ j (j - h) lo hi); lia. }
        destruct (Z.leb_spec (j - h) (lo + h - 1)) as [STOP|GO].
        + cbn [fst snd]. split; [lia|]. split; [exact PM'| exact FR'].
        + apply IH; try assumption; lia.
    Qed.

    Lemma mss_ins_perm_frame : forall a1 h lo hi i budget,
      0 < h -> 0 <= lo -> hi < nb -> lo + h <= i <= hi -> fm_perm a1 nb ->
      let r := mss_ins a1 a2 qoff nblock d h lo i budget in
      fm_perm (fst r) nb /\ frame_out a1 (fst r) lo hi.
    Proof.
      intros a1 h lo hi i budget Hh Hlo Hhi Hi PM. cbv zeta. unfold mss_ins.
      assert (Ri : 0 <= rd32 a1 i < nb) by (apply (proj1 PM); lia).
      assert (ID : forall x, rd32 (filled a1 i (rd32 a1 i)) x = rd32 a1 x).
      { intros x. unfold filled. destruct (Z.eq_dec x i) as [->|N]; [apply rd32_wr32_same; lia | apply rd32_wr32_other; lia]. }
      pose proof (mss_shift_hole (S (Z.to_nat (i - lo))) a1 h lo hi i (rd32 a1 i) budget a1 Hh Hlo Hhi Hi ltac:(lia)) as SH.
      cbv zeta in SH. cps_destruct SH as (A & B & C).
      { eapply fm_perm_ext; [exact PM|]. intros x Hx. apply ID. }
      { intros x Hx. apply ID. }
      destruct (mss_shift _ _ _ _ _ _ _ _ _ _ _) as [[a1' j'] b']. cbn [fst snd] in *. unfold filled in B, C. split; assumption.
    Qed.

    Lemma mss_hloop_perm_frame : forall f a1 h lo hi i budget,
      0 < h -> 0 <= lo -> hi < nb -> lo + h <= i -> fm_perm a1 nb ->
      let r := mss_hloop f a1 a2 qoff nblock d h lo hi i budget in
      fm_perm (fst (fst r)) nb /\ frame_out a1 (fst (fst r)) lo hi.
    Proof.
      induction f as [|f IH]; intros a1 h lo hi i budget Hh Hlo Hhi Hi PM; cbv zeta; cbn [mss_hloop].
      - cbn [fst]. split; [exact PM| apply frame_out_refl].
      - destruct (Z.ltb_spec hi i) as [L1|L1]; [cbn [fst]; split; [exact PM| apply frame_out_refl]|].
        pose proof (mss_ins_perm_frame a1 h lo hi i budget Hh Hlo Hhi ltac:(lia) PM) as I1. cbv zeta in I1.
        destruct (mss_ins a1 _ _ _ _ _ _ i budget) as [a11 b1]. cbn [fst] in I1. destruct I1 as [P1 F1].
        destruct (Z.ltb_spec hi (i + 1)) as [L2|L2]; [cbn [fst]; split; [exact P1| exact F1]|].
        pose proof (mss_ins_perm_frame a11 h lo hi (i + 1) b1 Hh Hlo Hhi ltac:(lia) P1) as I2. cbv zeta in I2.
        destruct (mss_ins a11 _ _ _ _ _ _ (i + 1) b1) as [a12 b2]. cbn [fst] in I2. destruct I2 as [P2 F2].
        destruct (Z.ltb_spec hi (i + 1 + 1)) as [L3|L3]; [cbn [fst]; split; [exact P2| eapply frame_out_trans; eassumption]|].
        pose proof (mss_ins_perm_frame a12 h lo hi (i + 1 + 1) b2 Hh Hlo Hhi ltac:(lia) P2) as I3. cbv zeta in I3.
        destruct (mss_ins a12 _ _ _ _ _ _ (i + 1 + 1) b2) as [a13 b3]. cbn [fst] in I3. destruct I3 as [P3 F3].
        destruct (Z.ltb_spec b3 0) as [L4|L4].
        + cbn [fst]. split; [exact P3|]. eapply frame_out_trans; [exact F1|]. eapply frame_out_trans; eassumption.
        + destruct (IH a13 h lo hi (i + 1 + 1 + 1) b3 Hh Hlo Hhi ltac:(lia) P3) as [P4 F4].
          split; [exact P4|]. eapply frame_out_trans; [exact F1|]. eapply frame_out_trans; [exact F2|]. eapply frame_out_trans; eassumption.
    Qed.

    Lemma mss_hps_perm_frame : forall n a1 lo hi hp budget,
      0 <= lo -> hi < nb -> 0 <= hp <= 12 -> (Z.of_nat n <= hp + 1) -> fm_perm a1 nb ->
      let r := mss_hps n a1 a2 qoff nblock d lo hi hp budget in
      fm_perm (fst (fst r)) nb /\ frame_out a1 (fst (fst r)) lo hi.
    Proof.
      induction n as [|n IH]; intros a1 lo hi hp budget Hlo Hhi Hhp Hn PM; cbv zeta; cbn [mss_hps].
      - cbn [fst]. split; [exact PM| apply frame_out_refl].
      - pose proof (incs_pos hp ltac:(lia)) as HP.
        pose proof (mss_hloop_perm_frame (S (Z.to_nat (hi - lo + 1))) a1 (incs_at hp) lo hi (lo + incs_at hp) budget ltac:(lia) Hlo Hhi ltac:(lia) PM) as HL.
        cbv zeta in HL. destruct (mss_hloop _ _ _ _ _ _ _ _ _ _ _) as [[a1' b'] ex]. cbn [fst] in HL. destruct HL as [P1 F1].
        destruct ex; [cbn [fst]; split; assumption|].
        destruct n as [|n'].
        + cbn [mss_hps fst]. split; assumption.
        + destruct (IH a1' lo hi (hp - 1) b' Hlo Hhi ltac:(lia) ltac:(lia) P1) as [P2 F2].
          split; [exact P2| eapply frame_out_trans; eassumption].
    Qed.

    Theorem mss_perm_frame : forall a1 lo hi budget,
      0 <= lo -> hi < nb -> hi - lo + 1 <= 2391484 -> fm_perm a1 nb ->
      let r := mainSimpleSort a1 a2 qoff nblock lo hi d budget in
      fm_perm (fst r) nb /\ frame_out a1 (fst r) lo hi.
    Proof.
      intros a1 lo hi budget Hlo Hhi Hsz PM. cbv zeta. unfold mainSimpleSort.
      destruct (Z.ltb_spec (hi - lo + 1) 2) as [SM|BIG]; [cbn [fst]; split; [exact PM| apply frame_out_refl]|].
      pose proof (mss_hp_run 15 (hi - lo + 1) 0 ltac:(lia) ltac:(rewrite incs_13; lia) ltac:(cbn; lia)) as HR. cbv zeta in HR.
      cps_destruct HR as (R1 & R2 & R3).
      set (hp := mss_hp 15 (hi - lo + 1) 0) in *.
      assert (HP1 : 1 <= hp). { destruct (Z.eq_dec hp 0) as [E|NE]; [|lia]. exfalso. rewrite E in R2. cbn in R2. lia. }
      pose proof (mss_hps_perm_frame (Z.to_nat (hp - 1 + 1)) a1 lo hi (hp - 1) budget Hlo Hhi ltac:(lia) ltac:(lia) PM) as HS.
      cbv zeta in HS. destruct (mss_hps _ _ _ _ _ _ _ _ _ _) as [[a1' b'] ex']. cbn [fst] in *. exact HS.
    Qed.
  End MSS.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section QS3.
    Variables (l0 r0 d0 : Z) (a2 : zarr) (qoff nblock : Z).
    Hypothesis HD0 : 0 <= d0 <= 14.
    Hypothesis Hl0 : 0 <= l0.
    Hypothesis Hr0 : r0 < nb.
    Hypothesis HN : r0 - l0 + 1 < 21 * 2 ^ 16.

    Lemma mq_a1_mpush : forall q lo hi d, mq_a1 (mpush q lo hi d) = mq_a1 q.
    Proof. reflexivity. Qed.
    Lemma mq_a1_PUSH3 : forall q, mq_a1 (PUSH3 q) = mq_a1 q.
    Proof. reflexivity. Qed.
    Lemma mq_a1_Q2 : forall q p, mq_a1 (Q2 q p) = A1V q p.
    Proof. reflexivity. Qed.

    Lemma iter_perm_frame : forall G q, GI l0 r0 d0 G q -> 0 < mq_sp q -> fm_perm (mq_a1 q) nb ->
      fm_perm (mq_a1 (mqs_iter a2 qoff nblock q)) nb /\ frame_out (mq_a1 q) (mq_a1 (mqs_iter a2 qoff nblock q)) l0 r0.
    Proof.
      intros G q GIq Hsp PM.
      destruct (flat G) as [|e F] eqn:HF.
      { destruct GIq as ([SP _] & _). rewrite HF in SP. cbn in SP. lia. }
      cps_pose GIq as (M & FA & CH). rewrite HF in M.
      pose proof (mst_top q e F M) as TOP.
      cps_destruct (GI_pop l0 r0 d0 G q e F GIq HF) as (G1 & p0 & F1 & FA1 & CH1 & SZ & SN & PN & NXT).
      destruct e as [[lo hi] d]. unfold ent in TOP. injection TOP as Td Thi Tlo.
      unfold sane, elo, ehi, ed in SN. unfold esz in SZ.
      rewrite mqs_iter_ITER. unfold ITER. unfold TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td.
      destruct (Sumbool.sumbool_of_bool ((hi - lo <? 20) || (14 <? d))) as [LF|NODE]; rewrite ?LF, ?NODE.
      - (* [comment removed for export] *)
        unfold LEAF. unfold TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td.
        pose proof (mss_perm_frame a2 qoff nblock d (mq_a1 q) lo hi (mq_budget q) ltac:(lia) ltac:(lia) ltac:(lia) PM) as MS. cbv zeta in MS.
        destruct (mainSimpleSort _ _ _ _ _ _ _ _) as [a1' b']. cbn [fst mq_a1] in *. destruct MS as [PX FX].
        split; [exact PX| eapply frame_out_widen; [exact FX| lia| lia]].
      - (* [comment removed for export] *)
        apply Bool.orb_false_iff in NODE. destruct NODE as [N1 N2]. apply Z.ltb_ge in N1. apply Z.ltb_ge in N2.
        set (med := MED a2 q).
        assert (HX : exists x, lo <= x <= hi /\ med = rd8 a2 (rd32 (mq_a1 q) x + d)).
        { subst med. unfold MED, TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td.
          pose proof (mmed3_in (rd8 a2 (rd32 (mq_a1 q) lo + d)) (rd8 a2 (rd32 (mq_a1 q) hi + d)) (rd8 a2 (rd32 (mq_a1 q) (Z.shiftr (lo + hi) 1) + d))) as MM.
          destruct MM as [E|[E|E]]; rewrite E.
          - exists lo. split; [lia| reflexivity].
          - exists hi. split; [lia| reflexivity].
          - exists (Z.shiftr (lo + hi) 1). split; [| reflexivity].
            rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
        cps_destruct HX as (x & Hx & Hmed).
        pose proof (mq_part a2 d med lo hi (mq_a1 q) x Hx ltac:(unfold key; exact Hmed)) as PP. cbv zeta in PP.
        unfold PART, TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td. fold med.
        pose proof (mpf_loop a2 d med (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) (mq_a1 q) lo hi (MP (mq_a1 q) lo hi lo hi) ltac:(lia) ltac:(lia)) as PFL.
        set (p := mpart_loop _ _ a2 d med _) in *.
        cps_destruct PFL as ((B1 & B2 & B3 & B4) & PMp & FRp). { split; [unfold MPB; cbn; lia|]. cbn [mp_a1]. split; [exact PM | apply frame_out_refl]. }
        cps_destruct PP as (A & B & C & D & E & F0).
        destruct (Z.ltb_spec (mp_gtHi p) (mp_ltLo p)) as [NOP|PUSH].
        { rewrite mq_a1_mpush. unfold Q1. cbn [mq_a1]. split; [exact PMp| eapply frame_out_widen; [exact FRp| lia| lia]]. }
        rewrite mq_a1_PUSH3. cps_destruct (net_spec (Q2 q p)) as (_ & _ & _ & _ & _ & _ & EA & _). rewrite EA, mq_a1_Q2.
        unfold A1V, TOPlo, TOPhi. rewrite ?Tlo, ?Thi, ?Td.
        set (n1 := mmin (mp_ltLo p - lo) (mp_unLo p - mp_ltLo p)).
        assert (Hn1 : 0 <= n1 /\ n1 <= mp_ltLo p - lo /\ n1 <= mp_unLo p - mp_ltLo p)
          by (subst n1; unfold mmin; destruct (_ <? _) eqn:X; [apply Z.ltb_lt in X|apply Z.ltb_ge in X]; lia).
        destruct (mvswap_perm_frame (S (Z.to_nat n1)) (mp_a1 p) lo (mp_unLo p - n1) n1 lo hi PMp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [PM1 FR1].
        set (a11 := mvswap (S (Z.to_nat n1)) (mp_a1 p) lo (mp_unLo p - n1) n1) in *.
        set (m1 := mmin (hi - mp_gtHi p) (mp_gtHi p - mp_unHi p)).
        assert (Hm1 : 0 <= m1 /\ m1 <= hi - mp_gtHi p /\ m1 <= mp_gtHi p - mp_unHi p)
          by (subst m1; unfold mmin; destruct (_ <? _) eqn:X; [apply Z.ltb_lt in X|apply Z.ltb_ge in X]; lia).
        destruct (mvswap_perm_frame (S (Z.to_nat m1)) a11 (mp_unLo p) (hi - m1 + 1) m1 lo hi PM1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [PM2 FR2].
        split; [exact PM2|].
        eapply frame_out_widen; [ eapply frame_out_trans; [exact FRp|]; eapply frame_out_trans; [exact FR1| exact FR2] | lia | lia ].
    Qed.

    Lemma loop_perm_frame : forall v G q, GI l0 r0 d0 G q -> fm_perm (mq_a1 q) nb ->
      fm_perm (mq_a1 (mqs_loop v a2 qoff nblock q)) nb /\ frame_out (mq_a1 q) (mq_a1 (mqs_loop v a2 qoff nblock q)) l0 r0.
    Proof.
      induction v as [|v IH]; intros G q GIq PM.
      - cbn [mqs_loop]. split; [exact PM| apply frame_out_refl].
      - rewrite mqs_loop_S. destruct (Z.ltb_spec 0 (mq_sp q)) as [P|NP]; cbn [andb]; [| split; [exact PM| apply frame_out_refl]].
        destruct (mq_exit q); cbn [negb]; [split; [exact PM| apply frame_out_refl]|].
        destruct (iter_perm_frame G q GIq P PM) as [P1 F1].
        cps_destruct (mqs_iter_GI l0 r0 d0 a2 qoff nblock HD0 G q GIq P) as (G' & GI' & _).
        destruct (IH G' _ GI' P1) as [P2 F2].
        split; [exact P2| eapply frame_out_trans; eassumption].
    Qed.

    Theorem mqs3_perm_frame : forall a1 budget l, fm_perm a1 nb -> l0 <= r0 ->
      let r := mainQSort3 a1 a2 qoff nblock l0 r0 d0 budget l in
      fm_perm (fst (fst r)) nb /\ frame_out a1 (fst (fst r)) l0 r0.
    Proof.
      intros a1 budget l PM HLR. cbv zeta. unfold mainQSort3.
      set (q0 := mpush _ l0 r0 d0).
      assert (GI0 : GI l0 r0 d0 [(r0 - l0 + 1, [(l0, r0, d0)])] q0).
      { split; [|split].
        - unfold flat; cbn [map concat app snd]. subst q0. apply mst_push. split; [reflexivity| intros k Hk; cbn in Hk; lia].
        - constructor; [|constructor]. split; [discriminate|]. split; [cbn; lia|]. split; [exact I|]. split; [cbn; split; [intros; tauto| exact I]|].
          split; [|lia]. intros e [<-|[]]. unfold esz, sane, elo, ehi, ed. lia.
        - exact I. }
      destruct (loop_perm_frame (mqs_fuel l0 r0) _ q0 GI0 ltac:(subst q0; rewrite mq_a1_mpush; cbn [mq_a1]; exact PM)) as [P F].
      subst q0. rewrite mq_a1_mpush in F. cbn [mq_a1 fst] in F |- *. split; [exact P| exact F].
    Qed.
  End QS3.
End SEWA.
