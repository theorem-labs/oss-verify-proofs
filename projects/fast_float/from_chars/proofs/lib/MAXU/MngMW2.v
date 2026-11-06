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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngNtfM MngNtfS MngMWP MngMW0 MngMW1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Record PCUT (HTOP : Z) (L : layout) (EXC : list loc) (s : astate) (m : word -> option byte) (sp0 K : Z) : Prop := {
  pc_cells : forall c, In c (image s) -> ~ In (mc_loc c) EXC -> cell_holds L (bview SEGS m) c ;
  pc_fp : Forall (range_mapped L (bview SEGS m)) (footprint s) ;
  pc_ctx : ly_ctx L = 0x97c98 ;
  pc_env : nenv m ;
  pc_stk : stk_ok SEGS m (wa sp0) K ;
  pc_K : 1024 <= K ;
  pc_sp1 : 2^20 <= sp0 - K ;
  pc_sp2 : sp0 <= 2^47 ;
  pc_sp3 : sp0 mod 16 = 0 ;
  pc_top : HTOP <= sp0 - K ;
  pc_T47 : HTOP <= 2^47 }.

Lemma PCUT_of_CUT : forall HTOP X R U L s m sp0 K, CUT HTOP X R U L s m sp0 K -> PCUT HTOP L [] s m sp0 K.
Proof.
  intros HTOP X R U L s m sp0 K [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof HR as (HL & HPW & HCS & HFM).
  constructor; try assumption.
  intros c Hc _. destruct (proj1 (Forall_forall _ _) HCS c Hc) as [[]|H]. exact H.
Qed.

Lemma PCUT_mono : forall HTOP L EXC EXC' s m sp0 K, PCUT HTOP L EXC s m sp0 K -> (forall l, In l EXC -> In l EXC') -> PCUT HTOP L EXC' s m sp0 K.
Proof.
  intros HTOP L EXC EXC' s m sp0 K [HCS HFM Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HT HTB] Hi. constructor; try assumption.
  intros c Hc Hn. apply HCS; [exact Hc | intros H; exact (Hn (Hi _ H))].
Qed.

(* [comment removed for export] *)
Theorem silent_pc : forall HTOP X' R' U' L EXC s s' m m' sp0 K (Cnew : list mcell),
  PCUT HTOP L EXC s m sp0 K ->
  (forall c, In c (image s') -> In (mc_loc c) EXC -> exists c', In c' Cnew /\ in_rng (cell_range L c') (loc_addr L (mc_loc c))) ->
  Inv X' R' U' s' -> XNM X' s' -> rgeoA HTOP L s' -> rdisj L s' -> RMONO s s' ->
  (forall rg, In rg (footprint s') -> In rg (footprint s) \/ range_mapped L (bview SEGS m') rg) ->
  (forall c, In c (image s') -> In c (image s) \/ In c Cnew) -> (forall c, In c Cnew -> In c (image s')) ->
  (forall c, In c (image s) -> In c (image s') \/ exists c', In c' Cnew /\ cell_range L c' = cell_range L c) ->
  Forall (cell_holds L (bview SEGS m')) Cnew ->
  mem_grows m m' ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sp0 - K <= x < sp0) \/ exists c', In c' Cnew /\ in_rng (cell_range L c') x) ->
  CUT HTOP X' R' U' L s' m' sp0 K /\ GROW sp0 K L s m L s' m'.
Proof.
  intros HTOP X' R' U' L EXC s s' m m' sp0 K Cnew P HEXC HI' HX' HG' HD' RM HFP HCov HIn HRev HNew Hg HWO.
  destruct P as [HCS0 HFM Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HT HTB].
  pose proof (layout_of_geo HTOP HTB X' R' U' s' L HI' Hctx HG' HD') as HL'.
  pose proof (image_cells_disjoint_X X' R' U' s' L HI' (XNU_of_XNM X' s' HX') HL') as HPW'.
  assert (PLACE : forall c, In c Cnew -> (0x97c98 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x98038) \/
                    loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x10000 \/ 0x99000 <= loc_addr L (mc_loc c)).
  { intros c Hc. exact (cells_place HTOP X' R' U' s' L HTB HI' HX' HG' HD' Hctx c (HIn c Hc)). }
  (* [comment removed for export] *)
  assert (STAT : forall x, 0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) -> m' (wa x) = m (wa x)).
  { intros x Hx Hnc. destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
    destruct (HWO x ltac:(lia) E) as [A | (c & Hc & Hin)]; [lia|].
    pose proof (PLACE c Hc) as Pl. unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. lia. }
  (* [comment removed for export] *)
  assert (HCov' : forall c, In c (image s') -> (In c (image s) /\ ~ In (mc_loc c) EXC) \/ In c Cnew).
  { intros c Hc. destruct (In_dec mcell_eq_dec c Cnew) as [Hn|Hn]; [right; exact Hn|]. left.
    destruct (HCov c Hc) as [Ho|Ho]; [|contradiction]. split; [exact Ho|]. intros HE.
    destruct (HEXC c Hc HE) as (c' & Hc' & Hin). assert (Hne : c <> c') by (intros ->; exact (Hn Hc')).
    pose proof (image_cell_width s' c Hc) as Hw.
    destruct (pairwise_map_In _ (cell_range L) _ _ _ HPW' Hc (HIn c' Hc') Hne) as [D|D];
      unfold ranges_disjoint, in_rng, cell_range in *; cbn [fst snd] in *; lia. }
  assert (HCS' : Forall (cell_holds L (bview SEGS m')) (image s')).
  { apply Forall_forall. intros c Hc. destruct (In_dec mcell_eq_dec c Cnew) as [Hn|Hn]; [exact (proj1 (Forall_forall _ _) HNew c Hn)|].
    destruct (HCov' c Hc) as [(Ho & Hne)|Hn2]; [|contradiction].
    apply (cell_holds_frame L (bview SEGS m) (bview SEGS m') c (image_cell_width s c Ho) (HCS0 c Ho Hne)).
    intros a Ha. unfold in_rng, cell_range in Ha. cbn [fst snd] in Ha.
    destruct (Z_lt_le_dec a 0) as [Ha0|Ha0]; [unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia); reflexivity|].
    destruct (Z_lt_le_dec a (2^64)) as [Ha1|Ha1]; [|unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia); reflexivity].
    apply MngWb.bview_ext. destruct (decide (m' (wa a) = m (wa a))) as [E|E]; [exact E|]. exfalso.
    destruct (HWO a ltac:(lia) E) as [HL | (c' & Hc' & Ha')].
    - pose proof (cells_below HTOP X' R' U' s' L (sp0 - K) HTB HI' HX' HG' HD' Hctx HT ltac:(lia) c Hc). lia.
    - assert (Hne' : c <> c') by (intros ->; exact (Hn Hc')).
      destruct (pairwise_map_In _ (cell_range L) _ _ _ HPW' Hc (HIn c' Hc') Hne') as [D|D];
        unfold ranges_disjoint, in_rng, cell_range in *; cbn [fst snd] in *; lia. }
  clear HCov'.
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

(* [comment removed for export] *)
Lemma PCUT_frame : forall HTOP L EXC s m m' sp0 K, PCUT HTOP L EXC s m sp0 K -> mem_grows m m' ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (forall f, In f (footprint s) -> ~ in_rng (crange L f) x) /\
     ~ (0x10000 <= x < 0x99000)) ->
  (forall c, In c (image s) -> exists f, In f (footprint s) /\ range_incl (cell_range L c) (crange L f)) ->
  PCUT HTOP L EXC s m' sp0 K.
Proof.
  intros HTOP L EXC s m m' sp0 K P Hg HO HINC. destruct P as [HCS HFM Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HT HTB].
  assert (STAT : forall x, 0x10000 <= x < 0x99000 -> m' (wa x) = m (wa x)).
  { intros x Hx. destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso. destruct (HO x ltac:(lia) E) as (_ & C). lia. }
  constructor; try assumption.
  - intros c Hc Hne. pose proof (HCS c Hc Hne) as H.
    destruct (HINC c Hc) as (f & Hf & Hincl).
    apply (cell_holds_frame L (bview SEGS m) (bview SEGS m') c (image_cell_width s c Hc) H).
    intros a Ha. unfold in_rng, cell_range in Ha. cbn [fst snd] in Ha.
    destruct (Z_lt_le_dec a 0) as [Ha0|Ha0]; [unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia); reflexivity|].
    destruct (Z_lt_le_dec a (2^64)) as [Ha1|Ha1]; [|unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia); reflexivity].
    apply MngWb.bview_ext. destruct (decide (m' (wa a) = m (wa a))) as [E|E]; [exact E|]. exfalso.
    destruct (HO a ltac:(lia) E) as (A & _). apply (A f Hf). unfold range_incl, cell_range, in_rng in *. cbn [fst snd] in *. lia.
  - apply Forall_forall. intros rg Hrg x Hx. apply (bview_grow_n m m' x Hg). exact (proj1 (Forall_forall _ _) HFM rg Hrg x Hx).
  - destruct Henv as (E1 & E2 & can & Rc & E3). split; [|split].
    + rewrite (rdn_frame_n m m' 416600 8) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact E1.
    + intros sc Hsc. rewrite (rdn_frame_n m m' (98984 + 2 * sc) 2) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact (E2 sc Hsc).
    + exists can. split; [exact Rc|]. rewrite (rdn_frame_n m m' 621568 8) by (try lia; intros x Hx; apply STAT; cbn in Hx; lia). exact E3.
  - apply (stk_ok_grows SEGS m m' (wa sp0) K HSTK Hg).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma CUT_shift : forall HTOP X R U L s m sp0 K d, CUT HTOP X R U L s m sp0 K -> 0 <= d -> d mod 16 = 0 -> 1024 <= K - d ->
  CUT HTOP X R U L s m (sp0 - d) (K - d).
Proof.
  intros HTOP X R U L s m sp0 K d [HI HX N HG HD HT HTB] Hd Ad HK.
  pose proof N as [HR HEX HZU HKs Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  replace (sp0 - d - (K - d)) with (sp0 - K) by ring.
  constructor; try assumption; [|lia].
  constructor; try assumption.
  - apply stk_ok_shift; [exact HSTK | exact Hd | lia | lia].
  - replace (sp0 - d - (K - d)) with (sp0 - K) by ring. exact Hsp1.
  - lia.
  - clear - Hsp3 Ad. apply Z.mod_divide in Hsp3; [|lia]. apply Z.mod_divide in Ad; [|lia]. destruct Hsp3 as (k1 & ->). destruct Ad as (k2 & ->).
    replace (k1 * 16 - k2 * 16) with ((k1 - k2) * 16) by ring. apply Z.mod_mul. lia.
  - replace (sp0 - d - (K - d)) with (sp0 - K) by ring. exact HC.
  - replace (sp0 - d - (K - d)) with (sp0 - K) by ring. exact HMP.
Qed.

Lemma CUT_unshift : forall HTOP X R U L s m sp0 K d, CUT HTOP X R U L s m (sp0 - d) (K - d) -> 0 <= d ->
  stk_ok SEGS m (wa sp0) K -> sp0 <= 2^47 -> sp0 mod 16 = 0 -> CUT HTOP X R U L s m sp0 K.
Proof.
  intros HTOP X R U L s m sp0 K d [HI HX N HG HD HT HTB] Hd STK Hsp Asp.
  pose proof N as [HR HEX HZU HKs Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  replace (sp0 - d - (K - d)) with (sp0 - K) in * by ring.
  constructor; try assumption.
  constructor; try assumption. lia.
Qed.

Lemma GROW_unshift : forall sp0 K d L s m L' s' m', GROW (sp0 - d) (K - d) L s m L' s' m' -> 0 <= d -> GROW sp0 K L s m L' s' m'.
Proof.
  intros sp0 K d L s m L' s' m' (E & RM & G & SI & CH) Hd. split; [exact E|]. split; [exact RM|]. split; [exact G|]. split; [exact SI|].
  intros x Hx Hne. destruct (CH x Hx Hne) as [A|B]; [left; lia | right; exact B].
Qed.
