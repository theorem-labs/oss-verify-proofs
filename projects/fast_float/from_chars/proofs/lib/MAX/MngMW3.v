(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition in_maps (L : layout) (s : astate) (x : Z) : Prop :=
  exists r rg, region_of s r = Some rg /\ rg_live rg = true /\ rg_kind rg = RkMap /\ ly_reg L r <= x < ly_reg L r + rg_len rg.

Definition CHGX (UB0 : Z -> Prop) (sp0 K : Z) (s0 : astate) (L : layout) (s : astate) (x : Z) : Prop :=
  CHG sp0 K s0 L s x \/ (in_maps L s x /\ ~ UB0 x).

Definition GROWX (UB0 : Z -> Prop) (sp0 K : Z) (L : layout) (s : astate) (m : word -> option byte) (L' : layout) (s' : astate)
    (m' : word -> option byte) : Prop :=
  lext L L' s /\ RMONO s s' /\
  (forall c, In c (image s) -> exists c', In c' (image s') /\ cell_range L' c' = cell_range L c) /\
  SI m m' /\
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> CHGX UB0 sp0 K s L' s' x).

Lemma GROWX_of_GROW : forall UB0 sp0 K L s m L' s' m', GROW sp0 K L s m L' s' m' -> GROWX UB0 sp0 K L s m L' s' m'.
Proof.
  intros UB0 sp0 K L s m L' s' m' (E & RM & G & S & CH). split; [exact E|]. split; [exact RM|]. split; [exact G|]. split; [exact S|].
  intros x Hx Hne. left. exact (CH x Hx Hne).
Qed.

Lemma GROWX_refl : forall UB0 sp0 K L s m, GROWX UB0 sp0 K L s m L s m.
Proof. intros. apply GROWX_of_GROW. apply GROW_refl. Qed.

Lemma in_maps_mono : forall L s L' s' x, lext L L' s -> RMONO s s' -> in_maps L s x -> in_maps L' s' x.
Proof.
  intros L s L' s' x HE (RM1 & RM2) (r & rg & Hr & Hl & Hk & Hx). destruct (RM2 r rg Hr Hl) as (rg' & Hr' & Hl' & Hk' & Hlen).
  exists r, rg'. split; [exact Hr'|]. split; [exact Hl'|]. split; [rewrite Hk'; exact Hk|].
  rewrite (proj2 (proj2 (proj2 HE)) r (MngLt.region_lt s r rg Hr)). lia.
Qed.

Lemma CHGX_mono : forall UB0 sp0 K s0 s0' L s L' s' x,
  lext L L' s -> RMONO s s' -> (length (st_regions s0') <= length (st_regions s0))%nat ->
  (forall c, In c (image s) -> exists c', In c' (image s') /\ cell_range L' c' = cell_range L c) ->
  CHGX UB0 sp0 K s0 L s x -> CHGX UB0 sp0 K s0' L' s' x.
Proof.
  intros UB0 sp0 K s0 s0' L s L' s' x HE RM Hl0 HGR [H|(H & Hu)].
  - left. exact (CHG_mono sp0 K s0 s0' L s L' s' x HE RM Hl0 HGR H).
  - right. split; [exact (in_maps_mono L s L' s' x HE RM H) | exact Hu].
Qed.

Lemma GROWX_trans : forall UB0 sp0 K L1 s1 m1 L2 s2 m2 L3 s3 m3,
  GROWX UB0 sp0 K L1 s1 m1 L2 s2 m2 -> GROWX UB0 sp0 K L2 s2 m2 L3 s3 m3 -> GROWX UB0 sp0 K L1 s1 m1 L3 s3 m3.
Proof.
  intros UB0 sp0 K L1 s1 m1 L2 s2 m2 L3 s3 m3 (E12 & R12 & G12 & S12 & C12) (E23 & R23 & G23 & S23 & C23).
  split; [exact (lext_trans L1 L2 L3 s1 s2 E12 E23 (proj1 R12))|]. split; [exact (RMONO_trans s1 s2 s3 R12 R23)|].
  split.
  { intros c Hc. destruct (G12 c Hc) as (c2 & Hc2 & E2). destruct (G23 c2 Hc2) as (c3 & Hc3 & E3). exists c3. split; [exact Hc3 | congruence]. }
  split; [exact (SI_trans m1 m2 m3 S12 S23)|].
  intros x Hx Hne. destruct (decide (m2 (wa x) = m1 (wa x))) as [E|E].
  - rewrite <- E in Hne. exact (CHGX_mono UB0 sp0 K s2 s1 L3 s3 L3 s3 x (lext_refl L3 s3) (RMONO_refl s3) (proj1 R12)
      ltac:(intros c Hc; exists c; auto) (C23 x Hx Hne)).
  - exact (CHGX_mono UB0 sp0 K s1 s1 L2 s2 L3 s3 x E23 R23 (Nat.le_refl _) G23 (C12 x Hx E)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cells_stepX : forall L s s' (m m' : word -> option byte) (Cnew : list mcell) LIM (EX : Z -> Prop),
  Forall (cell_holds L (bview SEGS m)) (image s) ->
  (forall c, In c (image s') -> In c (image s) \/ In c Cnew) ->
  (forall c, In c Cnew -> In c (image s')) ->
  Forall (cell_holds L (bview SEGS m')) Cnew ->
  pairwise ranges_disjoint (map (cell_range L) (image s')) ->
  (forall c, In c (image s') -> loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= LIM) ->
  (forall x, EX x -> forall c, In c (image s) -> ~ in_rng (cell_range L c) x) ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> LIM <= x \/ (exists c', In c' Cnew /\ in_rng (cell_range L c') x) \/ EX x) ->
  Forall (cell_holds L (bview SEGS m')) (image s').
Proof.
  intros L s s' m m' Cnew LIM EX HC HCov HIn HNew HPW HLIM HEX HWO.
  apply Forall_forall. intros c Hc. destruct (In_dec mcell_eq_dec c Cnew) as [Hn|Hn]; [exact (proj1 (Forall_forall _ _) HNew c Hn)|].
  destruct (HCov c Hc) as [Hold|Hn']; [|contradiction].
  apply (cell_holds_frame L (bview SEGS m) (bview SEGS m') c (image_cell_width s c Hold) (proj1 (Forall_forall _ _) HC c Hold)).
  intros a Ha. pose proof Ha as Ha'. unfold in_rng, cell_range in Ha. cbn [fst snd] in Ha.
  destruct (Z_lt_le_dec a 0) as [Ha0|Ha0]; [unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia); reflexivity|].
  destruct (Z_lt_le_dec a (2^64)) as [Ha1|Ha1]; [|unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia); reflexivity].
  apply MngWb.bview_ext. destruct (decide (m' (wa a) = m (wa a))) as [E|E]; [exact E|]. exfalso.
  destruct (HWO a ltac:(lia) E) as [HL | [(c' & Hc' & Hac) | HX]].
  - pose proof (HLIM c Hc). lia.
  - assert (Hne : c <> c') by (intros ->; exact (Hn Hc')).
    destruct (pairwise_map_In _ (cell_range L) _ _ _ HPW Hc (HIn c' Hc') Hne) as [D|D];
      unfold ranges_disjoint, in_rng, cell_range in *; cbn [fst snd] in *; lia.
  - exact (HEX a HX c Hold Ha').
Qed.

(* [comment removed for export] *)
Theorem silent_stepX : forall UB0 HTOP X R U X' R' U' L s s' m m' sp0 K (Cnew : list mcell) (EX : Z -> Prop),
  CUT HTOP X R U L s m sp0 K ->
  Inv X' R' U' s' -> XNM X' s' -> st_regions s' = st_regions s ->
  (forall rg, In rg (footprint s') -> In rg (footprint s) \/ range_mapped L (bview SEGS m') rg) ->
  (forall c, In c (image s') -> In c (image s) \/ In c Cnew) -> (forall c, In c Cnew -> In c (image s')) ->
  (forall c, In c (image s) -> In c (image s') \/ exists c', In c' Cnew /\ cell_range L c' = cell_range L c) ->
  Forall (cell_holds L (bview SEGS m')) Cnew ->
  mem_grows m m' ->
  (forall x, EX x -> (forall c, In c (image s) -> ~ in_rng (cell_range L c) x) /\ in_maps L s x /\ ~ UB0 x) ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sp0 - K <= x < sp0) \/ (exists c', In c' Cnew /\ in_rng (cell_range L c') x) \/ EX x) ->
  CUT HTOP X' R' U' L s' m' sp0 K /\ GROWX UB0 sp0 K L s m L s' m'.
Proof.
  intros UB0 HTOP X R U X' R' U' L s s' m m' sp0 K Cnew EX C HI' HX' Erg HFP HCov HIn HRev HNew Hg HEX HWO.
  destruct C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEXC HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof HR as (HL & HPW & HCS & HFM).
  assert (HG' : rgeoA HTOP L s') by (intros r rg Hr Hl; unfold region_of in Hr; rewrite Erg in Hr; exact (HG r rg Hr Hl)).
  assert (HD' : rdisj L s') by (intros r1 r2 rg1 rg2 Hne H1 H2; unfold region_of in H1, H2; rewrite Erg in H1, H2; exact (HD r1 r2 rg1 rg2 Hne H1 H2)).
  pose proof (layout_of_geo HTOP HTB X' R' U' s' L HI' Hctx HG' HD') as HL'.
  pose proof (image_cells_disjoint_X X' R' U' s' L HI' (XNU_of_XNM X' s' HX') HL') as HPW'.
  assert (PLACE : forall c, In c Cnew -> (0x95ed8 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x96278) \/
                    loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x10000 \/ 0x97000 <= loc_addr L (mc_loc c)).
  { intros c Hc. exact (cells_place HTOP X' R' U' s' L HTB HI' HX' HG' HD' Hctx c (HIn c Hc)). }
  (* [comment removed for export] *)
  assert (EXP : forall x, EX x -> (x < 0x10000 \/ 0x97000 <= x) /\ x < sp0 - K).
  { intros x Hx. destruct (HEX x Hx) as (_ & (r & rg & Hr & Hl & _ & Hin) & _). destruct (HG r rg Hr Hl) as (G1 & _ & G3 & G4).
    unfold ranges_disjoint in G4. cbn [fst snd] in G4. split; [lia | lia]. }
  assert (STAT : forall x, 0x10000 <= x < 0x97000 -> ~ (0x95ed8 <= x < 0x96278) -> m' (wa x) = m (wa x)).
  { intros x Hx Hnc. destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
    destruct (HWO x ltac:(lia) E) as [A | [(c & Hc & Hin) | B]]; [lia| |].
    - pose proof (PLACE c Hc) as P. unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. lia.
    - pose proof (EXP x B). lia. }
  assert (HCS' : Forall (cell_holds L (bview SEGS m')) (image s')).
  { apply (cells_stepX L s s' m m' Cnew (sp0 - K) EX); [| exact HCov | exact HIn | exact HNew | exact HPW' | | |].
    - apply Forall_forall. intros c Hc. destruct (proj1 (Forall_forall _ _) HCS c Hc) as [[]|H]. exact H.
    - intros c Hc. exact (cells_below HTOP X' R' U' s' L (sp0 - K) HTB HI' HX' HG' HD' Hctx HT ltac:(lia) c Hc).
    - intros x Hx. exact (proj1 (HEX x Hx)).
    - intros x Hx Hne. destruct (HWO x Hx Hne) as [A|[B|D]]; [left; lia | right; left; exact B | right; right; exact D]. }
  assert (HFM' : Forall (range_mapped L (bview SEGS m')) (footprint s')).
  { apply Forall_forall. intros rg Hrg. destruct (HFP rg Hrg) as [Ho|Hn]; [|exact Hn].
    intros x Hx. apply (bview_grow_n m m' x Hg). exact (proj1 (Forall_forall _ _) HFM rg Ho x Hx). }
  assert (Henv' : nenv m').
  { destruct Henv as (E1 & E2 & can & Rc & E3). split; [|split].
    - rewrite (rdn_frame_n m m' 408992 8) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact E1.
    - intros sc Hsc. rewrite (rdn_frame_n m m' (98984 + 2 * sc) 2) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact (E2 sc Hsc).
    - exists can. split; [exact Rc|]. rewrite (rdn_frame_n m m' 613952 8) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact E3. }
  split.
  - constructor; try assumption.
    exact (NC_of_geo HTOP HTB X' R' U' s' L m' sp0 K HI' HX' HG' HD' Hctx HT HCS' HFM' Henv' (stk_ok_grows SEGS m m' (wa sp0) K HSTK Hg) HK1 Hsp1 Hsp2 Hsp3).
  - split; [apply lext_refl|]. split.
    { split; [rewrite Erg; lia|]. intros r rg Hr Hl. exists rg. unfold region_of in *. rewrite Erg. split; [exact Hr|]. split; [exact Hl|]. split; [reflexivity | lia]. }
    split.
    { intros c Hc. destruct (HRev c Hc) as [H|(c' & Hc' & E)]; [exists c; split; [exact H | reflexivity]|]. exists c'. split; [exact (HIn c' Hc') | exact E]. }
    split; [intros x Hx Hnc; exact (STAT x Hx Hnc)|].
    intros x Hx Hne. destruct (HWO x Hx Hne) as [A|[(c & Hc & Hin)|B]].
    + left. left. exact A.
    + left. right. left. exists c. split; [exact (HIn c Hc) | exact Hin].
    + right. destruct (HEX x B) as (_ & Hm & Hu). split; [|exact Hu].
      destruct Hm as (r & rg & Hr & Hl & Hk & Hin). exists r, rg. unfold region_of in *. rewrite Erg. split; [exact Hr|]. split; [exact Hl|]. split; [exact Hk | exact Hin].
Qed.
