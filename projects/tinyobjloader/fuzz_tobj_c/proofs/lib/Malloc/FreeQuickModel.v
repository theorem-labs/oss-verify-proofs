(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "MCell"; "LMem"; "VZ"; "WF"; "image"; "used_metas"; "VP"; "VSec"; "frames"; "CTX_secret"; "LCtx"; "META_avail"; "META_bits"; "META_freed"; "META_mem"; "frame_ptr"; "hdr_byte3"; "hdr_off16"; "masks_ok"; "meta_bits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "ameta"; "padd"; "frame"; "astate"; "am_avail"; "am_freed"; "am_last"; "AREA_HDR"; "FUser"; "METAS_PER_AREA"; "META_SIZE"; "am_mem"; "fkind"; "fr_kind"; "fr_n"; "nth_slot"; "ss_fr"; "st_areas"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "Some"; "option"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "slot_end"; "frame_footer_cells"; "reserved_of"; "trailing_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel"; "frame_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfSurgery MallocWfGeom MallocWfRepr MallocWfMain
  MallocLayout MallocFooter MallocFooterLemmas MallocIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record frame_facts (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame) : Prop := FF {
  ff_used : usedX [] s g am;
  ff_MT : MT s g = Some (MUsed am);
  ff_i : 0 <= i <= am_last am;
  ff_slot : ss_fr (nth_slot am i) = Some fr;
  ff_last : 0 <= am_last am <= 31;
  ff_n : 0 <= fr_n fr;
  ff_off : 0 <= fr_off fr <= 255;
  ff_fit : UNIT * fr_off fr + fr_n fr <= stride_of am - IB;
  ff_h16 : 0 <= hdr_off16 am i fr <= 65535;
  ff_avail_nn : 0 <= am_avail am < 2 ^ 32;
  ff_freed_nn : 0 <= am_freed am < 2 ^ 32;
  ff_avail_i : Z.testbit (am_avail am) i = false;
  ff_freed_i : Z.testbit (am_freed am) i = false;
  ff_maplen : 0 <= am_maplen am;
  ff_stride_pos : 16 <= stride_of am;
  ff_stride16 : stride_of am mod 16 = 0;
  ff_mem16 : poff (am_mem am) mod 16 = 0;
  ff_sc : (0 <= am_sc am < 48 /\ (am_last am <> 0 -> stride_of am = class_size (am_sc am)))
          \/ (am_sc am = 63 /\ am_last am = 0 /\ 1 <= am_maplen am);
  ff_ext : stride_of am * (am_last am + 1) < 2 ^ 20 \/ am_sc am = 63;
  ff_region : exists rg, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
               0 <= poff (am_mem am) /\ poff (am_mem am) + group_extent am + IB <= rg_len rg /\
               (0 < am_maplen am -> poff (am_mem am) = 0 /\ rg_len rg = am_maplen am * PGSZ);
  ff_area : exists a k, In a (st_areas s) /\ 0 <= k < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * k)
            /\ poff a mod PGSZ = 0 /\ PGSZ <= poff a
            /\ exists rga, region_of s (prid a) = Some rga /\ rg_live rga = true /\ poff a + PGSZ <= rg_len rga
                          /\ rg_kind rga <> RkMap;
  ff_init : st_init_done s = true;

  ff_rsv32 : reserved_of am fr < 2 ^ 32
}.

Lemma masks_bound : ltac2:(tb__ "0|4|
S1bS18R1A1S1S1S32Z0M0S1fR2A1M1A2S33G1S36Z2Z20A2M2A2A2S1S32G0S20R2A1M3A2S33G3G2A2A2A2F_;Fam;").
Proof.
  intros am (Hl & _ & _ & Ha & Hf & _ & Hhi & _).
  assert (B : forall m, 0 <= m -> (forall k, am_last am < k -> Z.testbit m k = false) -> m < 2 ^ 32).
  { intros m Hm Hk. destruct (Z_lt_dec m (2 ^ 32)) as [|Hge]; [assumption|]. exfalso.
    assert (Hb : exists k, 32 <= k /\ Z.testbit m k = true).
    { destruct (Z.eq_dec m 0) as [->|Hnz]; [cbn in Hge; lia|].
      exists (Z.log2 m). split.
      - apply Z.log2_le_pow2; lia.
      - apply Z.bit_log2. lia. }
    destruct Hb as (k & Hk32 & Hbk). rewrite (Hk k) in Hbk by lia. discriminate. }
  split; split; try assumption; apply B; try assumption; intros k Hk; apply (Hhi k Hk).
Qed.

Theorem frame_facts_of : ltac2:(tb__ "0|2|
S1eS1aS1bS2dS1dS9R5A1S0S2fS2fS2fS1aS1bA2M0S2dA2M1S1dA2S2eG1S1dS2eG0S2dS2eS1aS1bR5R4A4R3A4R2A4SeR6A1A3S3cR7R6R5R4R3A5F_;F_;Ffr;Fi;Fam;Fg;Fs;").
Proof.
  intros s g am i fr HW Hfr.
  destruct (frames_inv s g am i fr HW Hfr) as (Hu & Hi & Hsl).
  pose proof (usedX_MT _ _ _ _ Hu) as [HMT _].
  pose proof (inv_groups HW g am Hu) as G.
  pose proof G as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof (Gsl i Hi) as (S1 & S2 & S3). rewrite Hsl in S3. destruct S3 as (Hal & _ & (Nf & Of & Bf & H16 & _) & _).
  pose proof (masks_bound am Gm) as [Bav Bfr].
  pose proof Gm as (Glast & _).
  unfold allocated in Hal. apply Bool.negb_true_iff in Hal. rewrite Z.lor_spec in Hal.
  apply Bool.orb_false_iff in Hal as [Ha0 Hf0].
  pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof (stride_mod16 _ _ _ _ _ _ HW Hu) as S16.
  pose proof (used_group_aligned [] None U0 s HW _ g am Hu (PeanoNat.Nat.le_refl _)) as M16.
  destruct (used_group_region [] None U0 s g am HW Hu) as (rg & Hr & Hkd & Hlv & Ho & Hext & Hz).
  split; try assumption.
  -   split; [|exact H16]. unfold hdr_off16. apply Z.add_nonneg_nonneg; [|lia].
    apply Z.div_pos; unfold UNIT; nia.
  -   destruct Gcl as [(C63 & Cl & Cm & _) | (Csc & Csmall & _ & Cext)].
    + right. auto.
    + left. split; [exact Csc|]. intros Hl0. unfold stride_of.
      replace ((am_last am =? 0) && negb (am_maplen am =? 0))%bool with false; [reflexivity|].
      symmetry. apply Bool.andb_false_iff. left. apply Z.eqb_neq. exact Hl0.
  - destruct Gcl as [(C63 & _) | (_ & _ & _ & Cext)]; [right; exact C63 | left; exact Cext].
  - exists rg. repeat (split; [assumption|]). intros Hm. split; [exact (Hz Hm)|].
    destruct (Gmp Hm) as (r' & rg' & Em & Hr' & _ & _ & Len & _).
    rewrite Em in Hr. cbn [prid] in Hr. rewrite Hr' in Hr. injection Hr as ->. exact Len.
  -
    destruct (meta_in_area s g (MUsed am) HW ltac:(unfold MT in HMT; apply In_of_mlookup; exact HMT)) as (a & k & Ha & Hk & E).
    exists a, k. split; [exact Ha|]. split; [exact Hk|]. split; [exact E|].
    destruct (proj1 (proj2 (inv_areas HW)) a Ha) as (r & o & rga & -> & Ho0 & Hpg & Hra & Hla & Hfit & Hkind).
    cbn [poff prid]. split; [exact Ho0|]. split; [exact Hpg|].
    exists rga. repeat (split; [assumption|]). destruct (rg_kind rga); [discriminate|discriminate|destruct Hkind].
  -
    destruct (st_init_done s) eqn:E; [reflexivity|]. exfalso.
    destruct (inv_ctx HW) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinit & _).
    destruct (Hinit E) as (Hm & _). unfold MT in HMT. rewrite Hm in HMT. cbn in HMT. discriminate.
  -
    unfold reserved_of.
    destruct Gcl as [(C63 & Cl & Cm & _ & _ & [CR | (fr0 & Hfr0 & _ & _ & Crsv)]) | (Csc & Csmall & _ & Cext)].
    + discriminate CR.
    + replace i with 0 in Hsl by lia. rewrite Hsl in Hfr0. injection Hfr0 as <-.
      unfold stride_of. rewrite Cl, Z.eqb_refl. replace (am_maplen am =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [andb negb]. unfold PGSZ, UNIT, IB in *. lia.
    + unfold IB, UNIT in *. nia.
Qed.

Lemma footer_cells_frame : ltac2:(tb__ "0|0|
S1eS1aS1bS2dS1dS5S0S2fS1aS1bA2S2eS1aS1bR5R4A4SbR6A1A3S1S32Z0R4A2S32R4S21R5A1A2A2S2S31S1dA1S2bS2aR6R5A2A1S30S1dR4A2A3S0S5R4S39R7R6R5A3A3S0S5R5S37RaA1A3F_;F_;F_;F_;Fc;Ffr;Fi;Fam;Fg;Fs;").
Proof.
  intros s g am i fr c Hg Hi Hsl Hc. unfold footer_cells. apply in_flat_map. exists (g, am). split; [exact Hg|].
  cbn [snd]. unfold group_footer_cells. right. apply in_flat_map. exists i. split; [apply In_zseq; lia|].
  rewrite Hsl. exact Hc.
Qed.

Lemma footer_cells_trailing : ltac2:(tb__ "0|0|
S1eS1aS1bS0S2fS1aS1bA2S2eS1aS1bR2R1A4SbR3A1A3S0S5S3bR2A1S37R4A1A3F_;Fam;Fg;Fs;").
Proof.
  intros s g am Hg. unfold footer_cells. apply in_flat_map. exists (g, am). split; [exact Hg|]. left. reflexivity.
Qed.

Lemma end_byte_cell : ltac2:(tb__ "0|2|
S1eS1aS1bS2dS9R4A1S0S2fS1aS1bA2S2eS1aS1bR4R3A4SbR5A1A3S1S32Z0M0R3A2S32R3S21R4A1A2A2S4S0S5S6S7S38R5R4A2A1U1S8G0A1A3M1SaR7A1A3S0S5G1S37R7A1A3A2F_;F_;F_;Fi;Fam;Fg;Fs;").
Proof.
  intros s g am i HW Hg Hi.
  destruct (Z_lt_dec i (am_last am)) as [Hlt|Hge].
  - left. replace (slot_end am i) with (padd (slot_start am (i + 1)) (-4)).
    + apply (proj1 (slot_start_cells s g am (i + 1) HW Hg ltac:(lia))).
    + unfold slot_end, slot_start, padd. destruct (am_mem am) as [r o]. f_equal. unfold IB. lia.
  - right. replace i with (am_last am) by lia. rewrite <- trailing_is_last_end. apply (footer_cells_trailing s g am Hg).
Qed.

Theorem quick_cells : ltac2:(tb__ "0|f|
S1eS1aS1bS2dS1dS9R5A1S0S2fS2fS2fS1aS1bA2M0S2dA2M1S1dA2S2eG1S1dS2eG0S2dS2eS1aS1bR5R4A4R3A4R2A4SeR6A1A3S2S27S28R3A1S23A3S15R6R5R4A3S1aS38R7R6A2S1aS3aR8R6A2S2dS1S0S5S6S7S1cR3N4A2A1M2U1M3S8Z0M4A1M5A3SaRbA1M6A3S1S0S5S6S7S1cR3N3A2A1G3S8S16R9R8R7A3A1A3G6A3S1S0S5S6S7S1cR3N2A2A1U2S8S17R9R8R7A3A1A3G6A3S1S0S5S6S7S26R9A1M7A1U8M8ScRaA1A3G6A3S1S0S5S6S7S1cRaS14A2A1G8ScG7A1A3G6A3S1S0S5S6S7S1cRaS11A2A1U4M9S8S1fR9A1A1A3G6A3S1S0S5S6S7S1cRaS13A2A1G9S8S20R9A1A1A3G6A3S1S0S5S6S7S1cRaS12A2A1G8S8S19R9A1A1A3G6A3S1S3S1aS1aS3S2dS2dS1S0S1aR2S2cRdA1A3S1S1S32G4R1A2S33R1S24A2A2S1S2S1aRcS1cR2S34S22S35S25R1A2A2A2A3S1S0S5S6S7R2A1MaG8SdA3SaRdA1MbA3S0S5S6S10SfA1G8SdA3GbA3A2A2A2A2Lk;A2La;A2S1S4S0S5S6GaG3G5A3McG6A3S0S5GcS37RbA1A3A2S1S33G4R1A2S0S5S6S7S1cR4S29R8A1A2A1G3G5A3S37RcA1MdA3F_;S1S32Z5MeR1A2S0S5S6G2G9S8R2A1A3GdA3F_;S33GeR1A2S0S5S6S7S1cR3N5A2A1G3G5A3GdA3F_;A2A2A2A2A2A2A2A2A2A2A2A2Tr;Te;Tp;F_;F_;F_;Ffr;Fi;Fam;Fg;Fs;").
Proof.
  intros s g am i fr HW Hfr Hk p e r.
  pose proof (get_meta_ok s g am i fr HW Hfr) as GM. cbn beta in GM.
  destruct GM as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _ & C10 & _).
  destruct (in_frames_inv s g am i fr Hfr) as (Hg & Hi & Hsl).
  assert (FC : forall c, In c (frame_footer_cells am i fr) -> In c (footer_cells s)).
  { intros c Hc. exact (footer_cells_frame s g am i fr c Hg Hi Hsl Hc). }
  unfold frame_footer_cells in FC. rewrite Hk in FC. fold p e r in FC.
  repeat (split; [assumption|]).
  split; [exact (end_byte_cell s g am i HW Hg Hi)|].
  split; [|split]; intros Hr; apply FC; rewrite !in_app_iff.
  - left. replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia). left. reflexivity.
  - right. left. replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). left. reflexivity.
  - right. right. replace (5 <? r) with true by (symmetry; apply Z.ltb_lt; lia). left. reflexivity.
Qed.
