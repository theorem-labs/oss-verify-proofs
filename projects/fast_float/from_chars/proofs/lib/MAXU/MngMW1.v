(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngNtfM MngNtfS MngMWP MngMW0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Record CUT (HTOP : Z) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (L : layout) (s : astate) (m : word -> option byte)
    (sp0 K : Z) : Prop := {
  ct_inv : Inv X R U s ;
  ct_xnm : XNM X s ;
  ct_nc : NC L [] [] s m sp0 K ;
  ct_geo : rgeoA HTOP L s ;
  ct_disj : rdisj L s ;
  ct_top : HTOP <= sp0 - K ;
  ct_T47 : HTOP <= 2^47 }.

(* [comment removed for export] *)
Definition SI (m0 m : word -> option byte) : Prop :=
  forall x, 0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) -> m (wa x) = m0 (wa x).

Lemma SI_refl : forall m, SI m m.
Proof. intros m x _ _. reflexivity. Qed.

Lemma SI_trans : forall m0 m1 m2, SI m0 m1 -> SI m1 m2 -> SI m0 m2.
Proof. intros m0 m1 m2 H1 H2 x A B. rewrite (H2 x A B). exact (H1 x A B). Qed.

(* [comment removed for export] *)
Definition RMONO (s s' : astate) : Prop :=
  (length (st_regions s) <= length (st_regions s'))%nat /\
  forall r rg, region_of s r = Some rg -> rg_live rg = true ->
    exists rg', region_of s' r = Some rg' /\ rg_live rg' = true /\ rg_kind rg' = rg_kind rg /\ rg_len rg <= rg_len rg'.

Lemma RMONO_refl : forall s, RMONO s s.
Proof. intros s. split; [lia|]. intros r rg H Hl. exists rg. split; [exact H|]. split; [exact Hl|]. split; [reflexivity | lia]. Qed.

Lemma RMONO_trans : forall s1 s2 s3, RMONO s1 s2 -> RMONO s2 s3 -> RMONO s1 s3.
Proof.
  intros s1 s2 s3 (A1 & B1) (A2 & B2). split; [lia|]. intros r rg H Hl.
  destruct (B1 r rg H Hl) as (rg2 & H2 & L2 & K2 & N2). destruct (B2 r rg2 H2 L2) as (rg3 & H3 & L3 & K3 & N3).
  exists rg3. split; [exact H3|]. split; [exact L3|]. split; [congruence | lia].
Qed.

(* [comment removed for export] *)
Definition CHG (sp0 K : Z) (s0 : astate) (L : layout) (s : astate) (x : Z) : Prop :=
  (sp0 - K <= x < sp0) \/ (exists c, In c (image s) /\ in_rng (cell_range L c) x) \/
  (exists r rg, region_of s r = Some rg /\ rg_live rg = true /\ (length (st_regions s0) <= r)%nat /\ ly_reg L r <= x < ly_reg L r + rg_len rg) \/
  in_regs L s x.

(* [comment removed for export] *)
Definition GROW (sp0 K : Z) (L : layout) (s : astate) (m : word -> option byte) (L' : layout) (s' : astate) (m' : word -> option byte) : Prop :=
  lext L L' s /\ RMONO s s' /\
  (forall c, In c (image s) -> exists c', In c' (image s') /\ cell_range L' c' = cell_range L c) /\
  SI m m' /\
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> CHG sp0 K s L' s' x).

Lemma GROW_refl : forall sp0 K L s m, GROW sp0 K L s m L s m.
Proof.
  intros sp0 K L s m. split; [apply lext_refl|]. split; [apply RMONO_refl|]. split; [intros c Hc; exists c; auto|].
  split; [apply SI_refl|]. intros x _ H. exfalso. exact (H eq_refl).
Qed.

Lemma CHG_mono : forall sp0 K s0 s0' L s L' s' x,
  lext L L' s -> RMONO s s' -> (length (st_regions s0') <= length (st_regions s0))%nat ->
  (forall c, In c (image s) -> exists c', In c' (image s') /\ cell_range L' c' = cell_range L c) ->
  CHG sp0 K s0 L s x -> CHG sp0 K s0' L' s' x.
Proof.
  intros sp0 K s0 s0' L s L' s' x HE (RM1 & RM2) Hl0 HGR H.
  destruct H as [H | [(c & Hc & Hin) | [(r & rg & Hr & Hlv & Hge & Hx) | (r & rg & Hr & Hlv & Hk & Hx)]]].
  - left. exact H.
  - right. left. destruct (HGR c Hc) as (c' & Hc' & E). exists c'. split; [exact Hc'|]. rewrite E. exact Hin.
  - right. right. left. destruct (RM2 r rg Hr Hlv) as (rg' & Hr' & Hlv' & _ & Hlen).
    exists r, rg'. split; [exact Hr'|]. split; [exact Hlv'|]. split; [lia|].
    rewrite (proj2 (proj2 (proj2 HE)) r (MngLt.region_lt s r rg Hr)). lia.
  - right. right. right. destruct (RM2 r rg Hr Hlv) as (rg' & Hr' & Hlv' & Hk' & Hlen).
    exists r, rg'. split; [exact Hr'|]. split; [exact Hlv'|]. split; [rewrite Hk'; exact Hk|].
    rewrite (proj2 (proj2 (proj2 HE)) r (MngLt.region_lt s r rg Hr)). lia.
Qed.

Lemma GROW_trans : forall sp0 K L1 s1 m1 L2 s2 m2 L3 s3 m3,
  GROW sp0 K L1 s1 m1 L2 s2 m2 -> GROW sp0 K L2 s2 m2 L3 s3 m3 -> GROW sp0 K L1 s1 m1 L3 s3 m3.
Proof.
  intros sp0 K L1 s1 m1 L2 s2 m2 L3 s3 m3 (E12 & R12 & G12 & S12 & C12) (E23 & R23 & G23 & S23 & C23).
  split; [exact (lext_trans L1 L2 L3 s1 s2 E12 E23 (proj1 R12))|]. split; [exact (RMONO_trans s1 s2 s3 R12 R23)|].
  split.
  { intros c Hc. destruct (G12 c Hc) as (c2 & Hc2 & E2). destruct (G23 c2 Hc2) as (c3 & Hc3 & E3). exists c3. split; [exact Hc3 | congruence]. }
  split; [exact (SI_trans m1 m2 m3 S12 S23)|].
  intros x Hx Hne. destruct (decide (m2 (wa x) = m1 (wa x))) as [E|E].
  - rewrite <- E in Hne. exact (CHG_mono sp0 K s2 s1 L3 s3 L3 s3 x (lext_refl L3 s3) (RMONO_refl s3) (proj1 R12)
      ltac:(intros c Hc; exists c; auto) (C23 x Hx Hne)).
  - exact (CHG_mono sp0 K s1 s1 L2 s2 L3 s3 x E23 R23 (Nat.le_refl _) G23 (C12 x Hx E)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cells_step : forall L s s' (m m' : word -> option byte) (Cnew : list mcell) LIM,
  Forall (cell_holds L (bview SEGS m)) (image s) ->
  (forall c, In c (image s') -> In c (image s) \/ In c Cnew) ->
  (forall c, In c Cnew -> In c (image s')) ->
  Forall (cell_holds L (bview SEGS m')) Cnew ->
  pairwise ranges_disjoint (map (cell_range L) (image s')) ->
  (forall c, In c (image s') -> loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= LIM) ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> LIM <= x \/ exists c', In c' Cnew /\ in_rng (cell_range L c') x) ->
  Forall (cell_holds L (bview SEGS m')) (image s').
Proof.
  intros L s s' m m' Cnew LIM HC HCov HIn HNew HPW HLIM HWO.
  apply Forall_forall. intros c Hc. destruct (In_dec mcell_eq_dec c Cnew) as [Hn|Hn]; [exact (proj1 (Forall_forall _ _) HNew c Hn)|].
  destruct (HCov c Hc) as [Hold|Hn']; [|contradiction].
  apply (cell_holds_frame L (bview SEGS m) (bview SEGS m') c (image_cell_width s c Hold) (proj1 (Forall_forall _ _) HC c Hold)).
  intros a Ha. unfold in_rng, cell_range in Ha. cbn [fst snd] in Ha.
  destruct (Z_lt_le_dec a 0) as [Ha0|Ha0]; [unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia); reflexivity|].
  destruct (Z_lt_le_dec a (2^64)) as [Ha1|Ha1]; [|unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia); reflexivity].
  apply MngWb.bview_ext. destruct (decide (m' (wa a) = m (wa a))) as [E|E]; [exact E|]. exfalso.
  destruct (HWO a ltac:(lia) E) as [HL | (c' & Hc' & Ha')].
  - pose proof (HLIM c Hc). lia.
  - assert (Hne : c <> c') by (intros ->; exact (Hn Hc')).
    destruct (pairwise_map_In _ (cell_range L) _ _ _ HPW Hc (HIn c' Hc') Hne) as [D|D];
      unfold ranges_disjoint, in_rng, cell_range in *; cbn [fst snd] in *; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cells_below : forall HTOP X R U s L LIM, HTOP <= 2^47 ->
  Inv X R U s -> XNM X s -> rgeoA HTOP L s -> rdisj L s -> ly_ctx L = 0x97c98 -> HTOP <= LIM -> 0x98038 <= LIM ->
  forall c, In c (image s) -> loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= LIM.
Proof.
  intros HTOP X R U s L LIM HTB HI HX HG HD Hctx HT HC c Hc.
  pose proof (layout_of_geo HTOP HTB X R U s L HI Hctx HG HD) as HL.
  destruct (image_in_footprint_X X R U s L c HI (XNU_of_XNM X s HX) HL Hc) as (rg & Hrg & Hinc).
  unfold range_incl, cell_range, crange in *. cbn [fst snd] in *.
  destruct (footprint_inv s rg Hrg) as [-> | [(a & Ha & ->) | (k & rgk & Hk & Kk & Lk & ->)]].
  - cbn [fst snd loc_addr] in Hinc. rewrite Hctx in Hinc. unfold CTX_SIZE in Hinc. lia.
  - destruct (area_range HTOP X R U s L a HI HG Ha) as (r & rg & _ & Hr & Hl & _ & B1 & B2 & _).
    destruct (HG r rg Hr Hl) as (G1 & _ & G3 & G4). cbn [fst snd] in Hinc. unfold PGSZ in *. lia.
  - destruct (HG k rgk Hk Lk) as (G1 & _ & G3 & G4). cbn [fst snd loc_addr] in Hinc. unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
Lemma NC_stackw : forall L s m m' sp0 K, NC L [] [] s m sp0 K -> mem_grows m m' ->
  (forall x, 0 <= x < 2^64 -> ~ (sp0 - K <= x < sp0) -> m' (wa x) = m (wa x)) -> NC L [] [] s m' sp0 K.
Proof.
  intros L s m m' sp0 K N Hg HO. pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof HR as (HL & HPW & HCS & HFM).
  constructor; try assumption.
  - split; [exact HL|]. split; [exact HPW|]. split.
    + apply Forall_forall. intros c Hc. destruct (proj1 (Forall_forall _ _) HCS c Hc) as [[]|H]. right.
      apply (cell_holds_frame L (bview SEGS m) (bview SEGS m') c (image_cell_width s c Hc) H).
      intros a Ha. pose proof (HC c Hc) as (P1 & P2 & _). unfold in_rng, cell_range in Ha. cbn [fst snd] in Ha.
      apply MngWb.bview_ext. apply HO; lia.
    + apply Forall_forall. intros rg Hrg x Hx. apply (bview_grow_n m m' x Hg). exact (proj1 (Forall_forall _ _) HFM rg Hrg x Hx).
  - destruct Henv as (E1 & E2 & can & Rc & E3). split; [|split].
    + rewrite (rdn_frame_n m m' 416600 8) by (try lia; intros x Hx; apply HO; cbn in Hx; lia). exact E1.
    + intros sc Hsc. rewrite (rdn_frame_n m m' (98984 + 2 * sc) 2) by (try lia; intros x Hx; apply HO; cbn in Hx; lia). exact (E2 sc Hsc).
    + exists can. split; [exact Rc|]. rewrite (rdn_frame_n m m' 621568 8) by (try lia; intros x Hx; apply HO; cbn in Hx; lia). exact E3.
  - exact (stk_ok_grows SEGS m m' (wa sp0) K HSTK Hg).
Qed.

(* [comment removed for export] *)
Lemma holds_wb : forall L m c v, (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
  0 <= loc_addr L (mc_loc c) -> loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 2^64 ->
  v mod 2^(8 * Z.of_nat (mc_w c)) = sval_num L (mc_val c) mod 2^(8 * Z.of_nat (mc_w c)) ->
  cell_holds L (bview SEGS (wbytes m (wa (loc_addr L (mc_loc c))) (word_to_le_bytes (mc_w c) (wa v)))) c.
Proof.
  intros L m c v Hv Hw H1 H2 Hm. apply holds_of_mem; [exact Hv | exact Hw | exact H1 | exact H2|].
  intros k Hk. rewrite (le_wa_eqm (mc_w c) v (sval_num L (mc_val c)) Hm Hw).
  apply MngWb.wbytes_at_wa; [exact H1 | rewrite length_N_to_le_bytes; exact H2 | rewrite length_N_to_le_bytes; exact Hk].
Qed.

(* [comment removed for export] *)
Lemma mupdate_new : forall l p x, ~ In p (map fst l) -> mupdate l p x = l ++ [(p, x)].
Proof.
  induction l as [|[q y] t IH]; intros p x H; cbn [mupdate]; [reflexivity|].
  destruct (sptr_eqb p q) eqn:E; [apply sptr_eqb_eq in E; subst; exfalso; apply H; left; reflexivity|].
  cbn [app]. f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma used_metas_raw_new : forall s m, ~ In m (keys s) -> used_metas (upd_meta m MRaw s) = used_metas s.
Proof.
  intros s m H. unfold used_metas, upd_meta. cbn [st_metas set_metas]. rewrite (mupdate_new _ _ _ H), flat_map_app. cbn. apply app_nil_r.
Qed.

Lemma areas_cells_ext : forall s s' l, (forall q, meta_slot_cells q (mlookup (st_metas s') q) = meta_slot_cells q (mlookup (st_metas s) q)) ->
  areas_cells s' l = areas_cells s l.
Proof.
  intros s s' l H. induction l as [|a t IH]; [reflexivity|]. cbn [areas_cells]. rewrite IH. f_equal. unfold area_cells. f_equal.
  apply flat_map_ext. intros k. apply H.
Qed.

(* [comment removed for export] *)
Lemma cells_place : forall HTOP X R U s L, HTOP <= 2^47 ->
  Inv X R U s -> XNM X s -> rgeoA HTOP L s -> rdisj L s -> ly_ctx L = 0x97c98 ->
  forall c, In c (image s) ->
    (0x97c98 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x98038) \/
    loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x10000 \/ 0x99000 <= loc_addr L (mc_loc c).
Proof.
  intros HTOP X R U s L HTB HI HX HG HD Hctx c Hc.
  pose proof (layout_of_geo HTOP HTB X R U s L HI Hctx HG HD) as HL.
  destruct (image_in_footprint_X X R U s L c HI (XNU_of_XNM X s HX) HL Hc) as (rg & Hrg & Hinc).
  unfold range_incl, cell_range, crange in *. cbn [fst snd] in *.
  destruct (footprint_inv s rg Hrg) as [-> | [(a & Ha & ->) | (k & rgk & Hk & Kk & Lk & ->)]].
  - cbn [fst snd loc_addr] in Hinc. rewrite Hctx in Hinc. unfold CTX_SIZE in Hinc. left. lia.
  - destruct (area_range HTOP X R U s L a HI HG Ha) as (r & rg & _ & Hr & Hl & _ & B1 & B2 & _).
    destruct (HG r rg Hr Hl) as (G1 & _ & G3 & G4). cbn [fst snd] in Hinc. unfold ranges_disjoint in G4. cbn [fst snd] in G4.
    unfold PGSZ in *. right. lia.
  - destruct (HG k rgk Hk Lk) as (G1 & _ & G3 & G4). cbn [fst snd loc_addr] in Hinc. unfold ranges_disjoint in G4. cbn [fst snd] in G4.
    unfold PGSZ in *. right. lia.
Qed.

(* [comment removed for export] *)
Theorem silent_step : forall HTOP X R U X' R' U' L s s' m m' sp0 K (Cnew : list mcell),
  CUT HTOP X R U L s m sp0 K ->
  Inv X' R' U' s' -> XNM X' s' -> st_regions s' = st_regions s ->
  (forall rg, In rg (footprint s') -> In rg (footprint s) \/ range_mapped L (bview SEGS m') rg) ->
  (forall c, In c (image s') -> In c (image s) \/ In c Cnew) -> (forall c, In c Cnew -> In c (image s')) ->
  (forall c, In c (image s) -> In c (image s') \/ exists c', In c' Cnew /\ cell_range L c' = cell_range L c) ->
  Forall (cell_holds L (bview SEGS m')) Cnew ->
  mem_grows m m' ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sp0 - K <= x < sp0) \/ exists c', In c' Cnew /\ in_rng (cell_range L c') x) ->
  CUT HTOP X' R' U' L s' m' sp0 K /\ GROW sp0 K L s m L s' m'.
Proof.
  intros HTOP X R U X' R' U' L s s' m m' sp0 K Cnew C HI' HX' Erg HFP HCov HIn HRev HNew Hg HWO.
  destruct C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof HR as (HL & HPW & HCS & HFM).
  assert (HG' : rgeoA HTOP L s') by (intros r rg Hr Hl; unfold region_of in Hr; rewrite Erg in Hr; exact (HG r rg Hr Hl)).
  assert (HD' : rdisj L s') by (intros r1 r2 rg1 rg2 Hne H1 H2; unfold region_of in H1, H2; rewrite Erg in H1, H2; exact (HD r1 r2 rg1 rg2 Hne H1 H2)).
  pose proof (layout_of_geo HTOP HTB X' R' U' s' L HI' Hctx HG' HD') as HL'.
  pose proof (image_cells_disjoint_X X' R' U' s' L HI' (XNU_of_XNM X' s' HX') HL') as HPW'.
  assert (PLACE : forall c, In c Cnew -> (0x97c98 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x98038) \/
                    loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x10000 \/ 0x99000 <= loc_addr L (mc_loc c)).
  { intros c Hc. exact (cells_place HTOP X' R' U' s' L HTB HI' HX' HG' HD' Hctx c (HIn c Hc)). }
  assert (WIDTH : forall c, In c Cnew -> (1 <= mc_w c)%nat) by (intros c Hc; exact (image_cell_width s' c (HIn c Hc))).
  (* [comment removed for export] *)
  assert (STAT : forall x, 0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) -> m' (wa x) = m (wa x)).
  { intros x Hx Hnc. destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
    destruct (HWO x ltac:(lia) E) as [A | (c & Hc & Hin)]; [lia|].
    pose proof (PLACE c Hc) as P. unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. lia. }
  assert (HCS' : Forall (cell_holds L (bview SEGS m')) (image s')).
  { apply (cells_step L s s' m m' Cnew (sp0 - K)); [| exact HCov | exact HIn | exact HNew | exact HPW' | |].
    3: { intros x Hx Hne. destruct (HWO x Hx Hne) as [A|B]; [left; lia | right; exact B]. }
    - apply Forall_forall. intros c Hc. destruct (proj1 (Forall_forall _ _) HCS c Hc) as [[]|H]. exact H.
    - intros c Hc. exact (cells_below HTOP X' R' U' s' L (sp0 - K) HTB HI' HX' HG' HD' Hctx HT ltac:(lia) c Hc). }
  assert (HFM' : Forall (range_mapped L (bview SEGS m')) (footprint s')).
  { apply Forall_forall. intros rg Hrg. destruct (HFP rg Hrg) as [Ho|Hn]; [|exact Hn].
    intros x Hx. apply (bview_grow_n m m' x Hg). exact (proj1 (Forall_forall _ _) HFM rg Ho x Hx). }
  assert (Henv' : nenv m').
  { destruct Henv as (E1 & E2 & can & Rc & E3). split; [|split].
    - rewrite (rdn_frame_n m m' 416600 8) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact E1.
    - intros sc Hsc. rewrite (rdn_frame_n m m' (98984 + 2 * sc) 2) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact (E2 sc Hsc).
    - exists can. split; [exact Rc|]. rewrite (rdn_frame_n m m' 621568 8) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact E3. }
  split.
  - constructor; try assumption.
    exact (NC_of_geo HTOP HTB X' R' U' s' L m' sp0 K HI' HX' HG' HD' Hctx HT HCS' HFM' Henv' (stk_ok_grows SEGS m m' (wa sp0) K HSTK Hg) HK1 Hsp1 Hsp2 Hsp3).
  - split; [apply lext_refl|]. split.
    { split; [rewrite Erg; lia|]. intros r rg Hr Hl. exists rg. unfold region_of in *. rewrite Erg. split; [exact Hr|]. split; [exact Hl|]. split; [reflexivity | lia]. }
    split.
    { intros c Hc. destruct (HRev c Hc) as [H|(c' & Hc' & E)]; [exists c; split; [exact H | reflexivity]|]. exists c'. split; [exact (HIn c' Hc') | exact E]. }
    split; [intros x Hx Hnc; exact (STAT x Hx Hnc)|].
    intros x Hx Hne. destruct (HWO x Hx Hne) as [A|(c & Hc & Hin)]; [left; exact A|]. right. left. exists c. split; [exact (HIn c Hc) | exact Hin].
Qed.

(* [comment removed for export] *)
Theorem silent_step' : forall HTOP X R U X' R' U' L s s' m m' sp0 K (Cnew : list mcell),
  CUT HTOP X R U L s m sp0 K ->
  Inv X' R' U' s' -> XNM X' s' -> rgeoA HTOP L s' -> rdisj L s' -> RMONO s s' ->
  (forall rg, In rg (footprint s') -> In rg (footprint s) \/ range_mapped L (bview SEGS m') rg) ->
  (forall c, In c (image s') -> In c (image s) \/ In c Cnew) -> (forall c, In c Cnew -> In c (image s')) ->
  (forall c, In c (image s) -> In c (image s') \/ exists c', In c' Cnew /\ cell_range L c' = cell_range L c) ->
  Forall (cell_holds L (bview SEGS m')) Cnew ->
  mem_grows m m' ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sp0 - K <= x < sp0) \/ exists c', In c' Cnew /\ in_rng (cell_range L c') x) ->
  CUT HTOP X' R' U' L s' m' sp0 K /\ GROW sp0 K L s m L s' m'.
Proof.
  intros HTOP X R U X' R' U' L s s' m m' sp0 K Cnew C HI' HX' HG' HD' RM HFP HCov HIn HRev HNew Hg HWO.
  destruct C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof HR as (HL & HPW & HCS & HFM).
  pose proof (layout_of_geo HTOP HTB X' R' U' s' L HI' Hctx HG' HD') as HL'.
  pose proof (image_cells_disjoint_X X' R' U' s' L HI' (XNU_of_XNM X' s' HX') HL') as HPW'.
  assert (PLACE : forall c, In c Cnew -> (0x97c98 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x98038) \/
                    loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x10000 \/ 0x99000 <= loc_addr L (mc_loc c)).
  { intros c Hc. exact (cells_place HTOP X' R' U' s' L HTB HI' HX' HG' HD' Hctx c (HIn c Hc)). }
  assert (WIDTH : forall c, In c Cnew -> (1 <= mc_w c)%nat) by (intros c Hc; exact (image_cell_width s' c (HIn c Hc))).
  (* [comment removed for export] *)
  assert (STAT : forall x, 0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) -> m' (wa x) = m (wa x)).
  { intros x Hx Hnc. destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
    destruct (HWO x ltac:(lia) E) as [A | (c & Hc & Hin)]; [lia|].
    pose proof (PLACE c Hc) as P. unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. lia. }
  assert (HCS' : Forall (cell_holds L (bview SEGS m')) (image s')).
  { apply (cells_step L s s' m m' Cnew (sp0 - K)); [| exact HCov | exact HIn | exact HNew | exact HPW' | |].
    3: { intros x Hx Hne. destruct (HWO x Hx Hne) as [A|B]; [left; lia | right; exact B]. }
    - apply Forall_forall. intros c Hc. destruct (proj1 (Forall_forall _ _) HCS c Hc) as [[]|H]. exact H.
    - intros c Hc. exact (cells_below HTOP X' R' U' s' L (sp0 - K) HTB HI' HX' HG' HD' Hctx HT ltac:(lia) c Hc). }
  assert (HFM' : Forall (range_mapped L (bview SEGS m')) (footprint s')).
  { apply Forall_forall. intros rg Hrg. destruct (HFP rg Hrg) as [Ho|Hn]; [|exact Hn].
    intros x Hx. apply (bview_grow_n m m' x Hg). exact (proj1 (Forall_forall _ _) HFM rg Ho x Hx). }
  assert (Henv' : nenv m').
  { destruct Henv as (E1 & E2 & can & Rc & E3). split; [|split].
    - rewrite (rdn_frame_n m m' 416600 8) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact E1.
    - intros sc Hsc. rewrite (rdn_frame_n m m' (98984 + 2 * sc) 2) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact (E2 sc Hsc).
    - exists can. split; [exact Rc|]. rewrite (rdn_frame_n m m' 621568 8) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact E3. }
  split.
  - constructor; try assumption.
    exact (NC_of_geo HTOP HTB X' R' U' s' L m' sp0 K HI' HX' HG' HD' Hctx HT HCS' HFM' Henv' (stk_ok_grows SEGS m m' (wa sp0) K HSTK Hg) HK1 Hsp1 Hsp2 Hsp3).
  - split; [apply lext_refl|]. split; [exact RM|].
    split.
    { intros c Hc. destruct (HRev c Hc) as [H|(c' & Hc' & E)]; [exists c; split; [exact H | reflexivity]|]. exists c'. split; [exact (HIn c' Hc') | exact E]. }
    split; [intros x Hx Hnc; exact (STAT x Hx Hnc)|].
    intros x Hx Hne. destruct (HWO x Hx Hne) as [A|(c & Hc & Hin)]; [left; exact A|]. right. left. exists c. split; [exact (HIn c Hc) | exact Hin].
Qed.


Lemma range_dec : forall x a n, {a <= x < a + n} + {~ (a <= x < a + n)}.
Proof. intros x a n. destruct (Z_le_dec a x); destruct (Z_lt_dec x (a + n)); [left; lia | right; lia | right; lia | right; lia]. Qed.

(* [comment removed for export] *)
Theorem effect_step : forall HTOP X R U X' R' U' L L' s s' m1 m1' m2 sp0 K (Cnew : list mcell) ea en,
  CUT HTOP X R U L s m1 sp0 K -> lext L L' s ->
  0 <= ea -> 0 <= en -> ea + en <= HTOP -> (ea + en <= 0x10000 \/ 0x99000 <= ea) ->
  (forall x, 0 <= x < 2^64 -> ~ (ea <= x < ea + en) -> m1' (wa x) = m1 (wa x)) ->
  (forall rg, In rg (footprint s) -> ranges_disjoint (ea, en) (crange L rg)) ->
  (exists r rg, region_of s' r = Some rg /\ rg_live rg = true /\ ((length (st_regions s) <= r)%nat \/ rg_kind rg <> RkMap) /\
      ly_reg L' r <= ea /\ ea + en <= ly_reg L' r + rg_len rg) ->
  Inv X' R' U' s' -> XNM X' s' -> rgeoA HTOP L' s' -> rdisj L' s' -> RMONO s s' ->
  (forall rg, In rg (footprint s') -> In rg (footprint s) \/ range_mapped L' (bview SEGS m2) rg) ->
  (forall c, In c (image s') -> In c (image s) \/ In c Cnew) -> (forall c, In c Cnew -> In c (image s')) ->
  (forall c, In c (image s) -> In c (image s') \/ exists c', In c' Cnew /\ cell_range L' c' = cell_range L' c) ->
  Forall (cell_holds L' (bview SEGS m2)) Cnew ->
  mem_grows m1' m2 ->
  (forall x, 0 <= x < 2^64 -> m2 (wa x) <> m1' (wa x) -> (sp0 - K <= x < sp0) \/ exists c', In c' Cnew /\ in_rng (cell_range L' c') x) ->
  CUT HTOP X' R' U' L' s' m2 sp0 K /\ GROW sp0 K L s m1 L' s' m2.
Proof.
  intros HTOP X R U X' R' U' L L' s s' m1 m1' m2 sp0 K Cnew ea en C HE Ha Hn Htop Himg Hout Hfp Hreg HI' HX' HG' HD' RM HFP HCov HIn HRev HNew Hg HWO.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_K _ _ _ _ _ _ _ N) as HK1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  destruct (NC_transport X R U s L L' HI HX HE HTOP m1 m1' sp0 K HTB N HG HD) as (N' & HGt & HDt).
  - intros rg Hrg x Hx. apply Hout; [pose proof (layout_of_geo HTOP HTB X R U s L HI (nc_ctx _ _ _ _ _ _ _ N) HG HD) as (_ & _ & _ & P);
                                     destruct (P rg Hrg) as (P1 & P2); unfold crange in P1, P2; cbn [fst snd] in P1, P2; lia|].
    pose proof (Hfp rg Hrg) as D. unfold ranges_disjoint, crange in D. cbn [fst snd] in D. lia.
  - intros x Hx. apply Hout; [lia | lia].
  - intros x Hx. apply Hout; [lia | lia].
  - assert (C' : CUT HTOP X R U L' s m1' sp0 K) by (constructor; assumption).
    destruct (silent_step' HTOP X R U X' R' U' L' s s' m1' m2 sp0 K Cnew C' HI' HX' HG' HD' RM HFP HCov HIn HRev HNew Hg HWO) as (CC & G2).
    split; [exact CC|].
    destruct G2 as (_ & _ & GR2 & SI2 & CH2).
    split; [exact HE|]. split; [exact RM|]. split.
    { intros c Hc. destruct (GR2 c Hc) as (c' & Hc' & E). exists c'. split; [exact Hc'|]. rewrite E. exact (cell_range_ext X R U s L L' HI HX HE c Hc). }
    split.
    { intros x Hx Hnc. rewrite (SI2 x Hx Hnc). apply Hout; [lia | lia]. }
    intros x Hx Hne. destruct (decide (m1' (wa x) = m1 (wa x))) as [E|E].
    + rewrite <- E in Hne. exact (CH2 x Hx Hne).
    + destruct (decide (ea <= x < ea + en)) as [Hin|Hnin]; [|exfalso; exact (E (Hout x Hx Hnin))].
      destruct Hreg as (r & rg & Hr & Hl & Hk & B1 & B2). right. right.
      destruct Hk as [Hk|Hk].
      * left. exists r, rg. split; [exact Hr|]. split; [exact Hl|]. split; [exact Hk | lia].
      * right. exists r, rg. split; [exact Hr|]. split; [exact Hl|]. split; [exact Hk | lia].
Qed.

(* [comment removed for export] *)
Lemma GROW_stack : forall sp0 K L s m m', (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> sp0 - K <= x < sp0) -> 2^20 <= sp0 - K ->
  GROW sp0 K L s m L s m'.
Proof.
  intros sp0 K L s m m' H Hsp. split; [apply lext_refl|]. split; [apply RMONO_refl|]. split; [intros c Hc; exists c; auto|].
  split.
  { intros x Hx Hnc. destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso. pose proof (H x ltac:(lia) E). lia. }
  intros x Hx Hne. left. exact (H x Hx Hne).
Qed.

Lemma CUT_stack : forall HTOP X R U L s m m' sp0 K, CUT HTOP X R U L s m sp0 K -> mem_grows m m' ->
  (forall x, 0 <= x < 2^64 -> ~ (sp0 - K <= x < sp0) -> m' (wa x) = m (wa x)) -> CUT HTOP X R U L s m' sp0 K.
Proof.
  intros HTOP X R U L s m m' sp0 K [HI HX N HG HD HT HTB] Hg HO. constructor; try assumption. exact (NC_stackw L s m m' sp0 K N Hg HO).
Qed.
