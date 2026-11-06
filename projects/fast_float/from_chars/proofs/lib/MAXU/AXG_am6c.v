(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM MngNtfS MngMWP MngMW0 MngMW1 MngMW2 MngShift.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_am1 AXG_am3 AXG_am4 AXG_am5 AXG_am6 AXG_am7 AXG_am6b AXG_amr0 AXG_amr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngShift OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt6z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am3 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am4 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am5 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am6 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am7 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am6b OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_amr0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_amr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_cur_facts : forall X R U s r p, Inv X R U s -> st_brk s = BrkCur r p ->
  exists rg, region_of s r = Some rg /\ rg_kind rg = RkBrk /\ rg_live rg = true /\ rg_len rg = PGSZ * p /\ 2 <= p.
Proof.
  intros X R U s r p HI Hb. pose proof (inv_areas HI) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10). rewrite Hb in A7.
  destruct A7 as (Hbr & rg & Hrg & Hl & Hlen & Hp).
  destruct (brk_regions_In s r ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
  rewrite Hrg in Hrg2. injection Hrg2 as <-. exists rg. auto.
Qed.

Lemma region_of_bcg' : forall s r p rg k, region_of s r = Some rg ->
  region_of (s_bcg s r p rg) k = if Nat.eqb k r then Some (mkRegion RkBrk (rg_len rg + PGSZ) [] true) else region_of s k.
Proof.
  intros s r p rg k Hr. unfold s_bcg, region_of. cbn [st_regions set_brk set_avail_meta_areas set_avail_meta_area_count set_regions].
  rewrite nth_error_lupd. rewrite (proj2 (Nat.ltb_lt _ _) (region_of_lt _ _ _ Hr)). rewrite andb_true_r. reflexivity.
Qed.

Lemma RMONO_bcg : forall s r p rg, region_of s r = Some rg -> rg_kind rg = RkBrk -> RMONO s (s_bcg s r p rg).
Proof.
  intros s r p rg Hr Hk. split.
  - unfold s_bcg. cbn [st_regions set_brk set_avail_meta_areas set_avail_meta_area_count set_regions]. rewrite length_lupd. lia.
  - intros k rgk Hrk Hl. rewrite (region_of_bcg' s r p rg k Hr). destruct (Nat.eqb k r) eqn:E.
    + apply Nat.eqb_eq in E. subst k. rewrite Hr in Hrk. injection Hrk as <-. eexists. split; [reflexivity|].
      cbn [rg_live rg_kind rg_len]. split; [reflexivity|]. split; [symmetry; exact Hk | unfold PGSZ; lia].
    + exists rgk. split; [exact Hrk|]. split; [exact Hl|]. split; [reflexivity | lia].
Qed.

Lemma live_pos : forall X R U s k rgk, Inv X R U s -> region_of s k = Some rgk -> rg_live rgk = true -> 0 < rg_len rgk.
Proof.
  intros X R U s k rgk HI Hk Hl. pose proof (inv_areas HI) as (_ & _ & _ & _ & _ & _ & _ & _ & A9 & _). exact (proj2 (A9 k rgk Hk) Hl).
Qed.

(* [comment removed for export] *)
Lemma rdisj_bcg : forall X R U L s r p rg, Inv X R U s -> region_of s r = Some rg -> rg_live rg = true -> rdisj L s ->
  (forall k rgk, region_of s k = Some rgk -> rg_live rgk = true -> ranges_disjoint (ly_reg L r + rg_len rg, PGSZ) (ly_reg L k, rg_len rgk)) ->
  rdisj L (s_bcg s r p rg).
Proof.
  intros X R U L s r p rg HI Hr Hl HD FR7 r1 r2 rg1 rg2 Hne H1 H2 L1 L2.
  rewrite (region_of_bcg' s r p rg r1 Hr) in H1. rewrite (region_of_bcg' s r p rg r2 Hr) in H2.
  destruct (Nat.eqb r1 r) eqn:E1; destruct (Nat.eqb r2 r) eqn:E2.
  - apply Nat.eqb_eq in E1, E2. congruence.
  - apply Nat.eqb_eq in E1. subst r1. injection H1 as <-. cbn [rg_len].
    pose proof (HD r r2 rg rg2 Hne Hr H2 Hl L2) as D1. pose proof (FR7 r2 rg2 H2 L2) as D2. pose proof (live_pos X R U s r2 rg2 HI H2 L2) as P2.
    clear - D1 D2 P2. unfold ranges_disjoint in *. cbn [fst snd] in *. unfold PGSZ in *. lia.
  - apply Nat.eqb_eq in E2. subst r2. injection H2 as <-. cbn [rg_len].
    assert (Hne' : r1 <> r) by (intros E; apply Hne; exact E).
    pose proof (HD r1 r rg1 rg Hne' H1 Hr L1 Hl) as D1. pose proof (FR7 r1 rg1 H1 L1) as D2. pose proof (live_pos X R U s r1 rg1 HI H1 L1) as P2.
    clear - D1 D2 P2. unfold ranges_disjoint in *. cbn [fst snd] in *. unfold PGSZ in *. lia.
  - exact (HD r1 r2 rg1 rg2 Hne H1 H2 L1 L2).
Qed.

Lemma rgeoA_bcg : forall HTOP L s r p rg, region_of s r = Some rg -> rgeoA HTOP L s -> rg_live rg = true ->
  ly_reg L r + rg_len rg + PGSZ <= HTOP -> ranges_disjoint (ly_reg L r + rg_len rg, PGSZ) (0x10000, 0x89000) ->
  rgeoA HTOP L (s_bcg s r p rg).
Proof.
  intros HTOP L s r p rg Hr HG Hl Htop Himg k rgk Hk Hlk. rewrite (region_of_bcg' s r p rg k Hr) in Hk. destruct (Nat.eqb k r) eqn:E.
  - apply Nat.eqb_eq in E. subst k. injection Hk as <-. destruct (HG r rg Hr Hl) as (G1 & G2 & G3 & G4). cbn [rg_len].
    split; [exact G1|]. split; [exact G2|]. split; [clear - Htop; lia|]. clear - G4 Himg. unfold ranges_disjoint in *. cbn [fst snd] in *. unfold PGSZ in *. lia.
  - exact (HG k rgk Hk Hlk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bcg_mem (m : word -> option byte) (nb : Z) : word -> option byte :=
  wbytes (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa nb))) (wa (0 + 621760)) (word_to_le_bytes 8 (wa 1)).

Section BCG.
Variables (HTOP : Z) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (L : layout) (s : astate).
Variables (m m' : word -> option byte) (sp0 K : Z) (r : nat) (p : Z) (rg : region) (nb : Z).
Hypothesis C : CUT HTOP X R U L s m sp0 K.
Hypothesis Hb : st_brk s = BrkCur r p.
Hypothesis Hr : region_of s r = Some rg.
Hypothesis Enb : nb = ly_reg L r + PGSZ * (p + 1).
Hypothesis Hnb : nb <= HTOP.
Hypothesis HFP : forall f, In f (footprint s) -> ranges_disjoint (nb - PGSZ, PGSZ) (crange L f).
Hypothesis HIMG : nb <= 0x10000 \/ 0x99000 <= nb - PGSZ.
Hypothesis Hg : mem_grows m m'.
Hypothesis HOUT : forall x, 0 <= x < 2^64 -> ~ (nb - PGSZ <= x < nb) -> m' (wa x) = m (wa x).

#[using="X R U s m sp0 K C Hb Hr"] Lemma bcg_geo : rg_kind rg = RkBrk /\ rg_live rg = true /\ rg_len rg = PGSZ * p /\ 2 <= p /\
  PGSZ <= ly_reg L r /\ ly_reg L r mod PGSZ = 0 /\ ly_reg L r + rg_len rg <= HTOP.
Proof. LiaFast.lf_pins (fun (X R U s m sp0 K C Hb Hr : LiaFast.U) => LiaFast.u0).
  pose proof C as [HI HX N HG HD HT HTB].
  destruct (brk_cur_facts X R U s r p HI Hb) as (rg' & Hr' & Hk & Hl & Hlen & Hp2). rewrite Hr in Hr'. injection Hr' as <-.
  destruct (HG r rg Hr Hl) as (G1 & G2 & G3 & G4). auto 10.
Qed.

#[using="HOUT"] Lemma bcg_mout : forall x, 0 <= x < 2^64 -> ~ (622640 <= x < 622648) -> ~ (621760 <= x < 621768) -> ~ (nb - PGSZ <= x < nb) ->
  bcg_mem m' nb (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (HOUT : LiaFast.U) => LiaFast.u0).
  intros x Hx H1 H2 H3. unfold bcg_mem. rewrite !MngWb.wbytes_out by side. exact (HOUT x Hx H3).
Qed.

#[using="X R U m C Hb Hr Enb HFP HIMG Hg HOUT"] Theorem pcut_bcg : PCUT HTOP L OEXC (s_bcg s r p rg) (bcg_mem m' nb) sp0 K.
Proof. LiaFast.lf_pins (fun (X R U m C Hb Hr Enb HFP HIMG Hg HOUT : LiaFast.U) => LiaFast.u0).
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK' Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HCe HMP HMD].
  pose proof bcg_geo as (Hk & Hl & Hlen & Hp2 & G1 & G2 & G3).
  pose proof (PCUT_of_CUT HTOP X R U L s m sp0 K C) as P0.
  pose proof (layout_of_geo HTOP HTB X R U s L HI Hctx HG HD) as HL.
  pose proof (image_cells_disjoint_X X R U s L HI (XNU_of_XNM X s HX) HL) as HPW.
  set (cb := MCell (LCtx CTX_brk) 8 (VP (SP r (PGSZ * p)))).
  set (ca := MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s))).
  assert (Icb : In cb (image s)).
  { apply ctx_in_image. unfold ctx_cells. apply in_app_iff. left. rewrite Hb. cbn [In]. unfold cb. memb. }
  assert (Ica : In ca (image s)) by (apply ctx_in_image; unfold ca; in_ctx13).
  assert (Rcb : cell_range L cb = (622640, 8)) by (unfold cb, cell_range; cbn [mc_loc mc_w loc_addr]; rewrite Hctx; reflexivity).
  assert (Rca : cell_range L ca = (621760, 8)) by (unfold ca, cell_range; cbn [mc_loc mc_w loc_addr]; rewrite Hctx; reflexivity).
  assert (Hgm : mem_grows m (bcg_mem m' nb)).
  { unfold bcg_mem. apply (mem_grows_trans m m'); [exact Hg|]. apply (mem_grows_trans m' (wbytes m' (wa (0 + 622640)) (word_to_le_bytes 8 (wa nb))));
    apply wbytes_grows. }
  (* [comment removed for export] *)
  assert (KEEP : forall c, In c (image s) -> mc_loc c <> LCtx CTX_brk -> mc_loc c <> LCtx CTX_avail_meta_area_count ->
                   cell_holds L (bview SEGS (bcg_mem m' nb)) c).
  { intros c Hc N1 N2. pose proof (pc_cells _ _ _ _ _ _ _ P0 c Hc ltac:(intros [])) as H0.
    assert (Dcb : ranges_disjoint (cell_range L c) (cell_range L cb) \/ ranges_disjoint (cell_range L cb) (cell_range L c)).
    { apply (pairwise_map_In _ (cell_range L) _ _ _ HPW Hc Icb). intros E. apply N1. rewrite E. reflexivity. }
    assert (Dca : ranges_disjoint (cell_range L c) (cell_range L ca) \/ ranges_disjoint (cell_range L ca) (cell_range L c)).
    { apply (pairwise_map_In _ (cell_range L) _ _ _ HPW Hc Ica). intros E. apply N2. rewrite E. reflexivity. }
    rewrite Rcb in Dcb. rewrite Rca in Dca.
    destruct (image_in_footprint_X X R U s L c HI (XNU_of_XNM X s HX) HL Hc) as (f & Hf & Hincl).
    pose proof (HFP f Hf) as Df.
    apply (cell_holds_frame L (bview SEGS m) (bview SEGS (bcg_mem m' nb)) c (image_cell_width s c Hc) H0).
    intros a Ha.
    destruct (Z_lt_le_dec a 0) as [Ha0|Ha0]; [unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia); reflexivity|].
    destruct (Z_lt_le_dec a (2^64)) as [Ha1|Ha1]; [|unfold bview; replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia); reflexivity].
    apply MngWb.bview_ext. apply bcg_mout; [lia | | |].
    - clear - Dcb Ha. unfold ranges_disjoint, in_rng in *. destruct (cell_range L c) as [lo n]. cbn [fst snd] in *. lia.
    - clear - Dca Ha. unfold ranges_disjoint, in_rng in *. destruct (cell_range L c) as [lo n]. cbn [fst snd] in *. lia.
    - clear - Df Hincl Ha. unfold ranges_disjoint, range_incl, in_rng in *. destruct (cell_range L c) as [lo n]. destruct (crange L f) as [lo' n'].
      cbn [fst snd] in *. unfold PGSZ in *. lia. }
  constructor.
  - intros c Hc Hne.
    assert (CASE : c = brk_cell (VP (SP r (PGSZ * (p + 1)))) \/ c = ac_cell 1 \/
                   (In c (image s) /\ mc_loc c <> LCtx CTX_brk /\ mc_loc c <> LCtx CTX_avail_meta_area_count)).
    { destruct (bcg_cov s r p rg c Hc) as [Ho | [E | [E | E]]].
      - destruct (loc_eq_dec (mc_loc c) (LCtx CTX_brk)) as [El|El]; [left; exact (proj1 (bcg_ctx_loc s r p rg c CTX_brk Hc El) eq_refl)|].
        destruct (loc_eq_dec (mc_loc c) (LCtx CTX_avail_meta_area_count)) as [El2|El2];
          [right; left; exact (proj2 (bcg_ctx_loc s r p rg c CTX_avail_meta_area_count Hc El2) eq_refl)|].
        right; right. auto.
      - left; exact E.
      - right; left; exact E.
      - exfalso. apply Hne. rewrite E. cbn [ama_cell mc_loc]. unfold OEXC. cbn [In]. right; right; left; reflexivity. }
    destruct CASE as [-> | [-> | (Ho & N1 & N2)]].
    + (* [comment removed for export] *)
      assert (H1 : cell_holds L (bview SEGS (wbytes m' (wa (0 + 622640)) (word_to_le_bytes 8 (wa nb)))) (brk_cell (VP (SP r (PGSZ * (p + 1)))))).
      { replace (wa (0 + 622640)) with (wa (loc_addr L (mc_loc (brk_cell (VP (SP r (PGSZ * (p + 1)))))))) by (cbn [mc_loc brk_cell loc_addr]; rewrite Hctx; reflexivity).
        change 8%nat with (mc_w (brk_cell (VP (SP r (PGSZ * (p + 1)))))).
        apply holds_wb; cbn [mc_val mc_w mc_loc brk_cell loc_addr sval_num]; rewrite ?Hctx; unfold CTX_brk;
          first [ (intros z E; discriminate E) | (rewrite Enb; reflexivity) | lia ]. }
      apply (cell_holds_frame L _ _ (brk_cell (VP (SP r (PGSZ * (p + 1))))) ltac:(cbn; lia) H1). intros a Ha. unfold in_rng, cell_range in Ha. cbn [fst snd mc_loc mc_w brk_cell loc_addr] in Ha.
      rewrite Hctx in Ha. unfold CTX_brk in Ha. unfold bcg_mem. apply MngWb.bview_ext. rewrite MngWb.wbytes_out by side. reflexivity.
    + (* [comment removed for export] *)
      unfold bcg_mem.
      replace (wa (0 + 621760)) with (wa (loc_addr L (mc_loc (ac_cell 1)))) by (cbn [mc_loc ac_cell loc_addr]; rewrite Hctx; reflexivity).
      change 8%nat with (mc_w (ac_cell 1)).
      apply holds_wb; cbn [mc_val mc_w mc_loc ac_cell loc_addr sval_num]; rewrite ?Hctx; unfold CTX_avail_meta_area_count;
        first [ (intros z E; discriminate E) | lia | reflexivity ].
    + exact (KEEP c Ho N1 N2).
  - apply Forall_forall. intros f Hf x Hx. apply (bview_grow_n m (bcg_mem m' nb) x Hgm).
    exact (proj1 (Forall_forall _ _) (pc_fp _ _ _ _ _ _ _ P0) f (bcg_footprint s r p rg f Hr Hk Hf) x Hx).
  - exact Hctx.
  - destruct Henv as (E1 & E2 & can & Rc & E3). split; [|split].
    + rewrite (rdn_frame_n m (bcg_mem m' nb) 416600 8) by (try lia; intros x Hx; cbn in Hx; apply bcg_mout; clear - Hx HIMG; unfold PGSZ in *; lia). exact E1.
    + intros sc Hsc. rewrite (rdn_frame_n m (bcg_mem m' nb) (98984 + 2 * sc) 2) by (try lia; intros x Hx; cbn in Hx; apply bcg_mout; clear - Hx Hsc HIMG; unfold PGSZ in *; lia).
      exact (E2 sc Hsc).
    + exists can. split; [exact Rc|]. rewrite (rdn_frame_n m (bcg_mem m' nb) 621568 8) by (try lia; intros x Hx; cbn in Hx; apply bcg_mout; clear - Hx HIMG; unfold PGSZ in *; lia). exact E3.
  - exact (stk_ok_grows SEGS m (bcg_mem m' nb) (wa sp0) K HSTK Hgm).
  - exact HK1.
  - exact Hsp1.
  - exact Hsp2.
  - exact Hsp3.
  - exact HT.
  - exact HTB.
Qed.

#[using="HTOP X R U C Hb Hr Enb HIMG HOUT"] Theorem grow_bcg : GROW sp0 K L s m L (s_bcg s r p rg) (bcg_mem m' nb).
Proof. LiaFast.lf_pins (fun (HTOP X R U C Hb Hr Enb HIMG HOUT : LiaFast.U) => LiaFast.u0).
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  pose proof bcg_geo as (Hk & Hl & Hlen & Hp2 & G1 & G2 & G3).
  pose proof (bcg_cells_in s r p rg) as (I1 & I2 & I3).
  split; [apply lext_refl|]. split; [exact (RMONO_bcg s r p rg Hr Hk)|].
  split.
  { intros c Hc. destruct (bcg_rev s r p rg c Hc) as [H|(El & Ew)]; [exists c; split; [exact H | reflexivity]|].
    destruct El as [El|[El|El]].
    - exists (brk_cell (VP (SP r (PGSZ * (p + 1))))). split; [exact I1|]. unfold cell_range. rewrite El, Ew. reflexivity.
    - exists (ac_cell 1). split; [exact I2|]. unfold cell_range. rewrite El, Ew. reflexivity.
    - exists (ama_cell (SP r (PGSZ * p))). split; [exact I3|]. unfold cell_range. rewrite El, Ew. reflexivity. }
  split.
  { intros x Hx Hnc. apply bcg_mout; clear - Hx Hnc HIMG; unfold PGSZ in *; lia. }
  intros x Hx Hne.
  destruct (decide (622640 <= x < 622648)) as [D1|D1].
  { right. left. exists (brk_cell (VP (SP r (PGSZ * (p + 1))))). split; [exact I1|]. unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w brk_cell loc_addr].
    rewrite Hctx. unfold CTX_brk. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
  destruct (decide (621760 <= x < 621768)) as [D2|D2].
  { right. left. exists (ac_cell 1). split; [exact I2|]. unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w ac_cell loc_addr].
    rewrite Hctx. unfold CTX_avail_meta_area_count. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
  destruct (decide (nb - PGSZ <= x < nb)) as [D3|D3].
  { right. right. right. exists r, (mkRegion RkBrk (rg_len rg + PGSZ) [] true). split; [rewrite (region_of_bcg' s r p rg r Hr), Nat.eqb_refl; reflexivity|].
    cbn [rg_live rg_kind rg_len]. split; [reflexivity|]. split; [discriminate|]. clear - D3 Enb Hlen Hp2. subst nb. rewrite Hlen. unfold PGSZ in *. lia. }
  exfalso. apply Hne. exact (bcg_mout x Hx D1 D2 D3).
Qed.
End BCG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ecall_51a2c : exists w, fetch_word SEGS (wa 0x53b8c) = Some w /\ is_ecall w = true.
Proof. eexists. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

Lemma add4_51a2c : bv_add (wa 0x53b8c) (w64 4) = wa 0x53b90.
Proof. apply bv_eq. reflexivity. Qed.

Lemma kout_brk_grow : forall FORB HTOP L s n eff ans L', koutcome FORB HTOP L s (KBrkGrow n) eff ans L' ->
  (eff = mkEffect (w64 (brk_cur L s)) [] [] /\ ans = 0 /\ L' = L) \/
  (fresh_range FORB HTOP L s (brk_cur L s) (PGSZ * n) /\
   eff = mkEffect (w64 (brk_cur L s + PGSZ * n)) [] [(w64 (brk_cur L s), w64 (PGSZ * n))] /\ ans = 1 /\
   L' = match st_brk s with BrkNever => set_reg_addr L (length (st_regions s)) (ly_brk0 L) | _ => L end).
Proof. intros FORB HTOP L s n eff ans L' H. inversion H; subst; [left | right]; auto. Qed.

Section WKC.
Context {fx : FPState}.
Variable FORB : list (Z * Z).
Hypothesis HFORB : forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x89000).
Hypothesis WOR : forall HTOP X R U L0 s0 m0 (regs0 : bvmap 5 word) L s m Rg rom sp0 K can ra r o rg
    (Kt : Z -> itree astate (option sptr * astate)),
  CUT HTOP X R U L s m sp0 K -> GROW sp0 K L0 s0 m0 L s m -> 1152 <= K ->
  am_frame Rg m sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
    (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20)) ->
  getr regs0 1 = wa ra -> getr regs0 2 = wa sp0 -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rg (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
  getr Rg 1 = wa 343320 -> getr Rg 9 = wa (ly_reg L r + o) -> getr Rg 10 = wa (ly_reg L r + o) ->
  getr Rg 11 = wa 4096 -> getr Rg 12 = wa 3 ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> 0 < st_avail_meta_area_count s ->
  st_avail_meta_areas s = SP r o -> region_of s r = Some rg ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  Kt 1 = IRet (Some (padd (SP r o) AREA_HDR), s_opn (SP r o) (s_res1 s r rg o)) ->
  wk SEGS FORB HTOP rom L Rg (wa 0x551cc) m (IAsk (KMprotect (SP r o)) s Kt)
     (am_qpost HTOP X R U L0 s0 m0 regs0 sp0 K ra).

#[using="HFORB WOR"] Theorem wk_bc : forall HTOP X R U L s m (regs : bvmap 5 word) rom sp0 K ra r p,
  CUT HTOP X R U L s m sp0 K -> 1152 <= K -> getr regs 2 = wa sp0 -> getr regs 1 = wa ra -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> st_avail_meta_area_count s = 0 ->
  st_brk s = BrkCur r p ->
  wk SEGS FORB HTOP rom L regs (wa 0x53a60) m (alloc_meta s) (am_qpost HTOP X R U L s m regs sp0 K ra).
Proof. LiaFast.lf_pins (fun (HFORB WOR : LiaFast.U) => LiaFast.u0).
  intros HTOP X R U L s m regs rom sp0 K ra r p C HK R2 R1 Hra Mpg Hi Hf Hc Hac Hb.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  destruct (brk_cur_facts X R U s r p HI Hb) as (rg & Hr & Hk & Hl & Hlen & Hp2).
  destruct (HG r rg Hr Hl) as (G1 & G2 & G3 & G4).
  destruct (alloc_meta_bc s r p rg Hi Hf Hc Hac Hb Hr) as (Kb & K1 & K2 & Et & EKb1 & EKb0 & EK1 & EK2). rewrite Et.
  change (hide (ra = 0x542a0 \/ ra = 0x53ec4)) in Hra.
  set (bk := ly_reg L r + PGSZ * p).
  assert (Ebk : brk_cur L s = bk) by (unfold brk_cur; rewrite Hb; reflexivity).
  assert (Rbk : 4096 + 8192 <= bk /\ bk mod 4096 = 0 /\ bk <= HTOP).
  { clear - G1 G2 G3 Hlen Hp2. unfold bk, PGSZ in *. rewrite Hlen in G3. split; [lia|]. split; [|lia].
    apply Z.mod_divide in G2; [|lia]. destruct G2 as (k1 & E1). rewrite E1.
    replace (k1 * 4096 + 4096 * p) with ((k1 + p) * 4096) by ring. apply Z.mod_mul. lia. }
  destruct Rbk as (Rbk1 & Rbk2 & Rbk3).
  assert (Rbk4 : bk + 4096 <= 2^47).
  { assert (bk <= 2^47 - 1024) by (clear - Rbk3 HT Hsp2 HK; lia). clear - H Rbk2. 
    assert (E : bk = 4096 * (bk / 4096)) by (pose proof (Z.div_mod bk 4096 ltac:(lia)); lia).
    assert (bk / 4096 <= 2^35 - 1) by lia. lia. }
  (* [comment removed for export] *)
  destruct (seg_amp L s m regs rom sp0 K N R2) as (Rg & can & Hms1 & F1 & Kp1 & MO1 & MG1).
  set (m1 := am_mem0 m regs sp0 can) in *.
  assert (C1 : CUT HTOP X R U L s m1 sp0 K) by (apply (CUT_stack HTOP X R U L s m m1 sp0 K C MG1); intros x Hx Hn; apply MO1; [exact Hx | clear - Hn HK; lia]).
  assert (GR1 : GROW sp0 K L s m L s m1).
  { apply GROW_stack; [|clear - Hsp1; lia]. intros x Hx Hne. destruct (range_dec x (sp0 - 56) 56) as [I|I]; [clear - I HK; lia|]. exfalso. apply Hne. apply MO1; [exact Hx | clear - I; lia]. }
  assert (Mpg1 : rdn SEGS m1 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m m1 621648 8) by (try lia; intros x Hx; apply MO1; cbn in Hx; lia). exact Mpg. }
  destruct (seg_amq HTOP X R U L s m1 Rg rom sp0 K sp0 can _ _ _ _ _ _ F1 C1 Hi Hf Hc Mpg1) as (Rq & Hms2 & Q8 & Fq & Kq).
  pose proof C1 as [_ _ N1 _ _ _ _].
  assert (Mac : rdn SEGS m1 (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s))) N1 ltac:(in_ctx13)
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx, Hac in H. exact H. }
  assert (Mbk : rdn SEGS m1 (wa (0 + 622640)) 8 = Some (word_to_le_bytes 8 (wa bk))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_brk) 8 (match st_brk s with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end))
                  N1 ltac:(in_ctx13) ltac:(rewrite Hb; intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, Hb in H. cbn [sval_num loc_addr] in H. exact H. }
  set (av := sval_num L (if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0) then VZ 0 else VP (st_avail_meta_areas s))).
  assert (Mar : rdn SEGS m1 (wa (0 + 621792)) 8 = Some (word_to_le_bytes 8 (wa (av mod 2^64)))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_avail_meta_areas) 8
        (if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0) then VZ 0 else VP (st_avail_meta_areas s)))
                  N1 ltac:(in_ctx13) ltac:(destruct (_ && _); intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx in H. fold av in H. rewrite (wa_mod64 av) in H. exact H. }
  assert (Msh : rdn SEGS m1 (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa (st_meta_alloc_shift s)))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_meta_alloc_shift) 8 (VZ (st_meta_alloc_shift s))) N1 ltac:(in_ctx13)
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. exact H. }
  pose proof (inv_ctx HI) as CT. unfold ctx_ok in CT. destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Csh & _).
  pose proof (shift_le_34 X R U s HTOP L HI HG HD HTB) as S34.
  assert (Rar : 0 <= av mod 2^64 <= 2^64-1) by (pose proof (Z.mod_pos_bound av (2^64) ltac:(lia)); lia).
  assert (Rsh : 0 <= st_meta_alloc_shift s <= 34) by lia.
  destruct (seg_bcx Rq m1 rom sp0 can _ _ _ _ _ _ (av mod 2^64) (st_meta_alloc_shift s) bk Fq Q8 Mac ltac:(clear - Rbk1 Rbk4; lia) Mbk Rar Mar Rsh Msh)
    as (Rb & Hms3 & B17 & B10 & B9 & B8 & B19 & Kb3).
  assert (Rra : bv_unsigned (getr regs 1) = ra) by (rewrite R1; apply u_wa_small; clear - Hra; unfold hide in Hra; lia).
  rewrite Rra in Fq.
  assert (KR : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rb (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. rewrite (Kb3 k ltac:(clear - Hk'; klist Hk')), (Kq k ltac:(clear - Hk'; klist Hk')), (Kp1 k ltac:(clear - Hk'; klist Hk')). reflexivity. }
  assert (Fb : am_frame Rb m1 sp0 can ra (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
                 (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))).
  { apply (am_frame_regs Rq Rb m1 sp0 can _ _ _ _ _ _ Fq).
    - regk Kb3 2%nat. reflexivity.
    - regk Kb3 18%nat. reflexivity.
    - rewrite B19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ Fq)). }
  (* [comment removed for export] *)
  cbn [wk]. exists Rb, (wa 0x53b8c), m1. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 Hms3))|]. split.
  { split; [exact ecall_51a2c|]. exists SYS_brk, [brk_cur L s + PGSZ * 1]. split; [reflexivity|].
    split; [rewrite B17; reflexivity|]. cbn [args_match]. split; [|exact I].
    rewrite Ebk. match type of B10 with getr _ ?r0 = _ => match goal with |- bv_unsigned (getr _ ?r1) = _ =>
      replace r1 with r0 by (apply bv_eq; reflexivity) end end.
    rewrite B10, u_wa; unfold PGSZ; f_equal; try ring. }
  intros eff ans L' Ho. destruct (kout_brk_grow FORB HTOP L s 1 eff ans L' Ho) as [(-> & -> & ->) | (FR & -> & -> & EL')].
  - (* [comment removed for export] *)
    rewrite EKb0, add4_51a2c. cbn [eff_ret]. rewrite Ebk.
    change (mem_after m1 (mkEffect (w64 bk) [] [])) with m1.
    set (Rq' := regupd Rb 10 (w64 bk)).
    assert (Q'8 : getr Rq' 8 = wa 4096) by (unfold Rq'; rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact B8).
    assert (Q'9 : getr Rq' 9 = wa (bk + 4096)) by (unfold Rq'; rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact B9).
    assert (Q'10 : getr Rq' 10 = wa bk) by (unfold Rq'; rewrite getr_same by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); reflexivity).
    assert (Fq' : am_frame Rq' m1 sp0 can ra (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
                 (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))).
    { apply (am_frame_regs Rb Rq' m1 sp0 can _ _ _ _ _ _ Fb); unfold Rq'; apply getr_other; intros E; apply (f_equal bv_unsigned) in E; discriminate E. }
    assert (KA : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rq' (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
    { intros k Hk'. unfold Rq'. rewrite getr_other; [exact (KR k Hk')|]. clear - Hk'. cbn [In] in Hk'.
      repeat (destruct Hk' as [<-|Hk']; [intros E; apply (f_equal bv_unsigned) in E; cbv in E; discriminate E|]). destruct Hk'. }
    apply (wk_bc_ref FORB HFORB WOR HTOP X R U L s m regs L s m1 Rq' rom sp0 K can ra K1 K2 bk (bk + 4096) C1 GR1 HK Fq' R1 R2 Hra Q'8 Q'9 Q'10
             ltac:(clear - Rbk1 Rbk4; lia) ltac:(clear - Rbk1 Rbk4; lia) ltac:(clear; lia) KA Hi Hf Hc Hac ltac:(rewrite Hb; discriminate) Mpg1 EK1 EK2).
  - (* [comment removed for export] *)
    rewrite Hb in EL'. subst L'.
    rewrite EKb1. cbn [wk]. rewrite add4_51a2c. cbn [eff_ret]. rewrite Ebk in FR |- *.
    set (m2 := mem_after m1 (mkEffect (w64 (bk + PGSZ * 1)) [] [(w64 bk, w64 (PGSZ * 1))])).
    pose proof FR as (FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & FR7).
    assert (HIMG : ranges_disjoint (bk, PGSZ * 1) (0x10000, 0x89000)) by (apply HFORB; [unfold PGSZ; lia | exact FR5]).
    unfold ranges_disjoint in HIMG. cbn [fst snd] in HIMG. unfold PGSZ in HIMG, FR4.
    assert (MA : forall x, 0 <= x < 2^64 -> m2 (wa x) = if (bk <=? x) && (x <? bk + PGSZ * 1) then Some (Z_to_bv 8 0) else m1 (wa x)).
    { intros x Hx. unfold m2. apply mem_after_zero; [clear - Rbk1 Rbk4; lia | clear; unfold PGSZ; lia | exact Hx]. }
    assert (HOUT2 : forall x, 0 <= x < 2^64 -> ~ (bk <= x < bk + 4096) -> m2 (wa x) = m1 (wa x)).
    { intros x Hx Hn. rewrite MA by exact Hx. replace ((bk <=? x) && (x <? bk + PGSZ * 1)) with false; [reflexivity|]. symmetry. apply andb_false_iff.
      unfold PGSZ. destruct (Z_le_gt_dec bk x); [right; apply Z.ltb_ge; clear - Hn l; lia | left; apply Z.leb_gt; clear - g; lia]. }
    assert (Hg2 : mem_grows m1 m2) by (unfold m2; apply mem_after_zero_grows; [clear - Rbk1 Rbk4; lia | clear; unfold PGSZ; lia]).
    assert (ZP2 : ZP m2 bk).
    { intros x Hx. rewrite MA by (clear - Hx Rbk1 Rbk4; unfold PGSZ in *; lia).
      replace ((bk <=? x) && (x <? bk + PGSZ * 1)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Hx; unfold PGSZ in *; lia. }
    (* [comment removed for export] *)
    set (Rg' := regupd Rb 10 (w64 (bk + PGSZ * 1))).
    assert (G'8 : getr Rg' 8 = wa 4096) by (unfold Rg'; rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact B8).
    assert (G'9 : getr Rg' 9 = wa (bk + 4096)) by (unfold Rg'; rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact B9).
    assert (G'10 : getr Rg' 10 = wa (bk + 4096)) by (unfold Rg'; rewrite getr_same by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); reflexivity).
    assert (G'19 : getr Rg' 19 = wa 621712) by (unfold Rg'; rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact B19).
    assert (OFF : forall x, (621568 <= x < 621576 \/ 621648 <= x < 621656 \/ 621760 <= x < 621776 \/ 622640 <= x < 622648 \/ sp0 - 1152 <= x < sp0) ->
                    ~ (bk <= x < bk + 4096)).
    { intros x Hx. clear - Hx HIMG FR4 HT HK. lia. }
    assert (M3 : rdn SEGS m2 (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0))).
    { rewrite (rdn_frame_n m1 m2) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply HOUT2; [lia | apply OFF; lia]) | lia]). exact Mac. }
    assert (M4 : rdn SEGS m2 (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa (st_meta_alloc_shift s)))).
    { rewrite (rdn_frame_n m1 m2) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply HOUT2; [lia | apply OFF; lia]) | lia]). exact Msh. }
    assert (W5 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m2 (wa (0 + 622640 + d)) k = true).
    { intros d k Hd Hk'. apply (store_ok_eqm k m1 m2); [rewrite u_wa_small by lia; lia| |].
      - intros x Hx. rewrite u_wa_small in Hx by lia. rewrite <- (wa_u x). apply HOUT2; [apply OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range | apply OFF; lia].
      - pose proof (nc_ctx_wr L s m1 sp0 K (MCell (LCtx CTX_brk) 8 (match st_brk s with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end))
          N1 ltac:(in_ctx13) ltac:(destruct (st_brk s); intros z E; discriminate E) d k Hd ltac:(cbn [mc_w]; lia)) as W.
        cbn [mc_loc loc_addr] in W. rewrite Hctx in W. exact W. }
    assert (W6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m2 (wa (0 + 621760 + d)) k = true).
    { intros d k Hd Hk'. apply (store_ok_eqm k m1 m2); [rewrite u_wa_small by lia; lia| |].
      - intros x Hx. rewrite u_wa_small in Hx by lia. rewrite <- (wa_u x). apply HOUT2; [apply OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range | apply OFF; lia].
      - exact (nc_acsh_wr L s m1 sp0 K d k N1 Hd ltac:(lia)). }
    destruct (seg_bcg Rg' m2 rom (bk + 4096) (st_meta_alloc_shift s) G'8 G'9 G'10 G'19 ltac:(clear - Rbk1 Rbk4; lia) Rsh M3 M4 W5 W6)
      as (R5 & Hms5 & A8 & A9 & A19 & Kb5).
    change (mt6_mem_pmt6g m2 Rg' (bk + 4096) (bk + 4096) (st_meta_alloc_shift s)) with (bcg_mem m2 (bk + 4096)) in Hms5.
    set (s1 := s_bcg s r p rg).
    assert (Enb : bk + 4096 = ly_reg L r + PGSZ * (p + 1)) by (unfold bk, PGSZ; ring).
    assert (HFP : forall f, In f (footprint s) -> ranges_disjoint (bk + 4096 - PGSZ, PGSZ) (crange L f)).
    { intros f Hf0. replace (bk + 4096 - PGSZ) with bk by (unfold PGSZ; ring). replace PGSZ with (PGSZ * 1) by ring. exact (FR6 f Hf0). }
    assert (HIMG' : bk + 4096 <= 0x10000 \/ 0x99000 <= bk + 4096 - PGSZ) by (clear - HIMG; unfold PGSZ; lia).
    assert (HOUT2' : forall x, 0 <= x < 2^64 -> ~ (bk + 4096 - PGSZ <= x < bk + 4096) -> m2 (wa x) = m1 (wa x)).
    { intros x Hx Hn. apply HOUT2; [exact Hx | unfold PGSZ in Hn; lia]. }
    pose proof (pcut_bcg HTOP X R U L s m1 m2 sp0 K r p rg (bk + 4096) C1 Hb Hr Enb HFP HIMG' Hg2 HOUT2') as P1.
    pose proof (grow_bcg HTOP X R U L s m1 m2 sp0 K r p rg (bk + 4096) C1 Hb Hr Enb HIMG' HOUT2') as GR2.
    fold s1 in P1, GR2.
    assert (HIo : Inv X R U (open_st (st_avail_meta_areas s1) s1)) by exact (Inv_open_brk_grow X R U s r p rg HI Hb Hac Hc Hi Hr).
    assert (HX1 : XNM X s1) by exact HX.
    assert (Ebk' : ly_reg L r + rg_len rg = bk) by (unfold bk; rewrite Hlen; reflexivity).
    assert (HG1 : rgeoA HTOP L s1).
    { apply (rgeoA_bcg HTOP L s r p rg Hr HG Hl); rewrite Ebk'; [clear - FR4; unfold PGSZ; lia|]. unfold ranges_disjoint. cbn [fst snd]. unfold PGSZ. clear - HIMG. lia. }
    assert (HD1 : rdisj L s1).
    { apply (rdisj_bcg X R U L s r p rg HI Hr Hl HD). intros k rgk Hk' Lk. rewrite Ebk'. replace PGSZ with (PGSZ * 1) by ring. exact (FR7 k rgk Hk' Lk). }
    pose proof (inv_areas HI) as (A1 & A2 & A3 & A4 & _).
    assert (Epa : loc_addr L (LMem (st_avail_meta_areas s1)) = bk) by reflexivity.
    assert (MOUT : forall x, 0 <= x < 2^64 -> ~ (622640 <= x < 622648) -> ~ (621760 <= x < 621768) -> ~ (bk <= x < bk + 4096) ->
                     bcg_mem m2 (bk + 4096) (wa x) = m1 (wa x)).
    { intros x Hx D1 D2 D3. unfold bcg_mem. rewrite !MngWb.wbytes_out by side. exact (HOUT2 x Hx D3). }
    assert (ZP1 : ZP (bcg_mem m2 (bk + 4096)) (loc_addr L (LMem (st_avail_meta_areas s1)))).
    { rewrite Epa. intros x Hx. unfold bcg_mem. rewrite !MngWb.wbytes_out by (first [side | (clear - Hx HIMG; unfold PGSZ in *; lia)]). exact (ZP2 x Hx). }
    assert (F5 : am_frame R5 (bcg_mem m2 (bk + 4096)) sp0 can ra (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
                   (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))).
    { apply (am_frame_mem R5 m1); [|intros x Hx; apply MOUT; [lia | lia | lia | apply OFF; lia] | intros x Hx; apply MOUT; [lia | lia | lia | apply OFF; lia]].
      apply (am_frame_regs Rb R5 m1 sp0 can _ _ _ _ _ _ Fb).
      - regk Kb5 2%nat. unfold Rg'. apply getr_other. intros E; apply (f_equal bv_unsigned) in E; discriminate E.
      - regk Kb5 18%nat. unfold Rg'. apply getr_other. intros E; apply (f_equal bv_unsigned) in E; discriminate E.
      - rewrite A19. exact (eq_sym B19). }
    assert (R59 : getr R5 9 = wa (loc_addr L (LMem (st_avail_meta_areas s1)))) by (rewrite A9, Epa; f_equal; ring).
    destruct (open_tail HTOP X R U L s1 (bcg_mem m2 (bk + 4096)) R5 rom sp0 K can ra _ _ _ _ _ P1 HK HIo HX1 HG1 HD1 Hi ltac:(cbn; lia) A3 A4 ZP1 F5 R59 Hra)
      as (R6 & m3 & Hms6 & Q1 & Q2 & Q8' & Q9' & Q10' & Q18' & Q19' & Q20' & QK & CC & GG).
    exists R6, (wa ra), m3. split; [exact (msteps_trans SEGS _ _ _ Hms5 Hms6)|].
    exists (padd (SP r (PGSZ * p)) AREA_HDR), (s_opn (SP r (PGSZ * p)) s1). split; [reflexivity|]. split; [reflexivity|]. split; [exact Q10'|].
    split.
    { assert (KK : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R6 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
      { intros k Hk'. rewrite (QK k Hk'), (Kb5 k ltac:(clear - Hk'; klist Hk')). unfold Rg'. rewrite getr_other; [exact (KR k Hk')|]. clear - Hk'. cbn [In] in Hk'.
        repeat (destruct Hk' as [<-|Hk']; [intros E; apply (f_equal bv_unsigned) in E; cbv in E; discriminate E|]). destruct Hk'. }
      intros k Hk'. cbn [In] in Hk'.
      destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]].
      - litr2 Q1. exact (eq_sym R1).
      - litr2 Q2. exact (eq_sym R2).
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - litr2 Q8'. apply wa_u.
      - litr2 Q9'. apply wa_u.
      - litr2 Q18'. apply wa_u.
      - litr2 Q19'. apply wa_u.
      - litr2 Q20'. apply wa_u.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb.
      - apply KK. cbn [In]. memb. }
    split; [exact CC|].
    exact (GROW_trans sp0 K L s m L s m1 L _ _ GR1 (GROW_trans sp0 K L s m1 L s1 (bcg_mem m2 (bk + 4096)) L _ _ GR2 GG)).
Qed.
End WKC.
