(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "iff"; "ex"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "region"; "st_mmap_counter"; "UNIT"; "mslot"; "st_seq"; "IB"; "MUsed"; "st_regions"; "st_active"; "st_area_head"; "st_area_tail"; "st_areas"; "st_avail_meta"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_avail_meta_count"; "st_bounces"; "st_brk"; "st_free_meta_head"; "st_init_done"; "st_meta_alloc_shift"; "st_metas"; "st_unmap_seq"; "st_usage"; "MMAP_THRESHOLD"; "PGSZ"; "ameta"; "astate"; "FUser"; "brkst"; "set_seq"; "size_overflows"; "RkMap"; "am_mem"; "enframe"; "frame"; "kreq"; "mkFrame"; "mkRegion"; "mkSlot"; "mupdate"; "padd"; "prid"; "set_regions"; "set_unmap_seq"; "slot_start"; "sptr_eqb"; "stride_of"; "upd_slot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost.Direct"; "md_s2"; "md_s6"; "md_off"; "md_am4"; "md_stride"; "md_off0"; "md_r"; "md_rg"; "md_s5"; "md_slack"; "md_am6"; "md_ctr1"; "md_s1"; "md_s4"; "md_p"; "md_fr"; "md_hdr"; "md_rsv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "add"; "mul"; "lt"; "pow"; "eqb"; "modulo"; "div"; "land"; "leb"; "@Corelib.Init.Datatypes"; "bool"; "nil"; "prod"; "list"; "Some"; "option"; "cons"; "pair"; "None"; "app"; "true"; "false"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "Inv"; "U0"; "usedX"; "keys"; "region_of"; "MT"; "footprint"; "user_blocks"; "loc"; "yields"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost"; "direct_case"; "md_len"; "md_maplen"; "ovf_case"; "md_needed"; "@Corelib.Lists.ListDef"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "ub_same"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "direct_am"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfGroup MallocWfSlot MallocWfMalloc MallocWfMain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition ovf_case (n : Z) : Prop := 2 ^ 63 - 4097 <= n.

Definition direct_case (n : Z) : Prop := ltac2:(tb__ "0|0|
S0S4aS1fVn;A2S4eVn;S4bS4fZ2Z3fA2Z1001A2A2A2").

Lemma ovf_case_b : ltac2:(tb__ "0|0|
S5S2S6fR1A1S1S55S26R1A1S5fA3A2Fn;").
Proof. intros n. unfold ovf_case, size_overflows. rewrite Z.leb_le. tauto. Qed.
Lemma direct_case_b : ltac2:(tb__ "0|0|
S5S6cR1A1S0S1S55S26R2A1S60A3S1S55S54S1fR2A2S5fA3A2F_;Fn;").
Proof. intros n [H1 H2]. unfold size_overflows. split; [apply Z.leb_gt; lia | apply Z.leb_le; exact H1]. Qed.
Lemma size_cases : ltac2:(tb__ "0|1|
S5S4aZ0M0R1A2S4S6fR2A1S4S6cR2A1S0S4aG0R2A2S4eR2S1fA2A2A2A2F_;Fn;").
Proof. intros n Hn. unfold ovf_case, direct_case. lia. Qed.

Definition md_needed (n : Z) : Z := ltac2:(tb__ "0|0|
S4cS4cVn;ScA2S9A2").
Definition md_len (n : Z) : Z := page_round (md_needed n).
Definition md_maplen (n : Z) : Z := md_len n / PGSZ.

Lemma md_len_facts : ltac2:(tb__ "0|3|
S5S6cR1A1S0S0S4aS70R2A1M0S6dR2A1M1A2S4eG1S4cG0S20A2A2A2S0S1S5S51G1S20A2Z0A3S0S1S5G1S4dS6eR2A1M2S20A2A3S0S4aZ20G2A2S4aG1S4fZ2Z3fA2A2A2A2A2A2F_;Fn;").
Proof.
  intros n [H1 H2]. unfold md_maplen, md_len, md_needed, page_round, MMAP_THRESHOLD, IB, UNIT, PGSZ in *.
  set (q := (n + 4 + 16 + 4096 - 1) / 4096).
  assert (Hq : 4096 * q <= n + 4 + 16 + 4096 - 1 < 4096 * (q + 1)).
  { subst q. split; [apply Z.mul_div_le; lia|]. pose proof (Z.mul_succ_div_gt (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). lia. }
  replace (q * 4096 / 4096) with q by (symmetry; apply Z.div_mul; lia).
  assert (M : (q * 4096) mod 4096 = 0) by apply Z_mod_mult.
  repeat split; lia.
Qed.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocWfMeta MallocWfGeom MallocWfRingOps MallocFastPost Zones2 ImageUpd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Direct.
Variables (s : astate) (n : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S62S56S6A1S5dS57S6S5A2A1S63Vs;A4").
Hypothesis Hn : direct_case n.

Definition md_r : nat := length (st_regions s).
Definition md_rg : region := ltac2:(tb__ "0|0|
S2dS27S6dVn;A1S56S5A1S5fA4").

Definition md_s1 : astate := ltac2:(tb__ "0|0|
S32S5eS7SeVs;A1S5bS7S3fS56S7A1A3A3Vs;A2").

Definition md_s2 : astate := ltac2:(tb__ "0|2|
S55S22L_;S50SbVs;A1M0ZffA2S25Z1M1S33S71S5Z0U20A3S44A2A2S25S4cG0G1A2S44A2X55x2").

Lemma Inv_s1 : ltac2:(tb__ "0|0|
S62S56S6A1S5dS57S6S5A2A1S63S44A4").
Proof using HI Hn. unfold md_s1, md_rg. apply Inv_new_map; [exact HI|]. pose proof (md_len_facts n Hn). unfold md_needed in *. lia. Qed.
Lemma Inv_s2 : ltac2:(tb__ "0|0|
S62S56S6A1S5dS57S6S5A2A1S63S38A4").
Proof using HI Hn.
  unfold md_s2. pose proof (inv_ctx Inv_s1) as (_&_&_&_&_&_&_&C8&_). cbn [md_s1 st_seq set_regions] in C8.
  destruct (st_seq s =? 255) eqn:E.
  - apply Inv_set_seq; [|lia]. destruct repeat0_32_range as [A B]. apply Inv_set_unmap_seq; [exact Inv_s1 | exact A | exact B].
  - apply Z.eqb_neq in E. apply Inv_set_seq; [exact Inv_s1 |]. unfold md_s1 in *. destruct s; cbn in *; lia.
Qed.
Lemma s2_shape : ltac2:(tb__ "0|5|
S0S1S58S57S6SaA2A1S1cS38A1S1cVs;A1A3S0S1S58S6A1S12S38A1S12Vs;A1A3S0S1S58S7A1SeS38A1S5eS7SeVs;A1S5bS7S3fS56S7A1A3A3A3S0S1S5S8S38A1S8Vs;A1A3S0S1S55S1aS38A1S1aVs;A1A3S0S1S58S5aS6A1M0A1SfS38A1SfVs;A1A3S0S1S58S5A1M1S1eS38A1S1eVs;A1A3S0S1S5SbS38A1S55S5L_;S50SbVs;A1M2ZffA2M3Z1M4S4cG2G4A2X55x2A3S0S1G1S1dS38A1S55G1L_;G3S71S5Z0U20A3S1dVs;A1X55x2A3S0S1G1S17S38A1S17Vs;A1A3S0S1S24S18S38A1S18Vs;A1A3S0S1G0S19S38A1S19Vs;A1A3S0S1S6S13S38A1S13Vs;A1A3S0S1S5S16S38A1S16Vs;A1A3S0S1S5S14S38A1S14Vs;A1A3S0S1S5S1bS38A1S1bVs;A1A3S0S1G0S10S38A1S10Vs;A1A3S0S1G0S11S38A1S11Vs;A1A3S1S6S15S38A1S15Vs;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using HI. unfold md_s2, md_s1. destruct (st_seq s =? 255); destruct s; cbn; repeat split; reflexivity. Qed.
Lemma region_s2 : ltac2:(tb__ "0|0|
S1S5aS7A1S66S38S3eA2S59S7S3fA2A3").
Proof using HI. unfold region_of, md_r. rewrite (proj1 (proj2 (proj2 s2_shape))). rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.
Lemma regions_old_s2 : ltac2:(tb__ "0|1|
S61S7S1S5aS7A1M0S66Vs;R2A2S59S7R1A2A3S1G0S66S38R3A2S59S7R2A2A3F_;Frg;Fk;").
Proof using HI. intros k rg Hk. pose proof (region_of_lt s k rg Hk) as Hlt. unfold region_of in *. rewrite (proj1 (proj2 (proj2 s2_shape))). rewrite nth_error_app1; [exact Hk | exact Hlt]. Qed.
Lemma usedX_s2 : ltac2:(tb__ "0|1|
S6S21S2S64S56S6A1M0S38R2R1A4S64G0Vs;R2R1A4A2Fa;Fq;").
Proof using HI. intros q a. unfold usedX, MTX, MT. rewrite (proj1 s2_shape). tauto. Qed.
Lemma fresh_s2 : ltac2:(tb__ "0|0|
S6S21S64S56S6A1S38R2R1A4S74S31S28R2A1A1S3eA2F_;Fa;Fq;").
Proof using HI. intros q a Hu. apply usedX_s2 in Hu. exact (used_group_prid_lt _ _ _ _ q a HI Hu). Qed.
Lemma ub_same_s2 : ub_same s md_s2.
Proof using HI. apply ub_same_metas. exact (proj1 s2_shape). Qed.
Lemma keys_s2 : ltac2:(tb__ "0|0|
S1S58S6A1S65S38A1S65Vs;A1A3"). Proof using HI. unfold keys. rewrite (proj1 s2_shape). reflexivity. Qed.

Variables (s3 : astate) (g : sptr).
Hypothesis HI3 : ltac2:(tb__ "0|0|
S62S5bS6Vg;S56S6A1A3S5dS57S6S5A2A1S63Vs3;A4").
Hypothesis Hraw : ltac2:(tb__ "0|0|
S76S5bS6Vg;S56S6A1A3Vs3;A2").
Hypothesis Hkey : In g (keys s3).
Hypothesis Hframe : am_frame md_s2 s3.
Hypothesis HusedX : ltac2:(tb__ "0|1|
S6S21S2S64S5bS6Vg;S56S6A1M0A3Vs3;R2R1A4S64G0S38R2R1A4A2Fa;Fq;").
Hypothesis Hub3 : ub_same md_s2 s3.
Hypothesis Hctr3 : ltac2:(tb__ "0|0|
S1S5S8Vs3;A1S8Vs;A1A3").

Definition md_am4 : ameta := ltac2:(tb__ "0|0|
S75S3eS6eVn;A1A2").
Definition md_s4 : astate := ltac2:(tb__ "0|0|
S72Vg;SdS3bA1Vs3;A3").
Lemma region_s3 : ltac2:(tb__ "0|0|
S1S5aS7A1S66Vs3;S3eA2S59S7S3fA2A3").
Proof using HI Hframe. destruct Hframe as (_ & _ & HR & _). apply HR; [exact region_s2 | reflexivity]. Qed.
Lemma s4_facts : ltac2:(tb__ "0|1|
S0S62S56S6A1M0S59S57S6S5A2S5cS6S5Vg;Z0A4A2S63S45A4S0S64G0S45Vg;S3bA4S73Vs3;S45A2A2A2").
Proof using HI HI3 Hframe Hn HusedX.
  pose proof (md_len_facts n Hn) as (L1 & L2 & L3 & L4 & L5).
  assert (T : itok (setm g md_am4 s3) (fun r => Inv [] (Some (g, 0)) U0 (snd r) /\ usedX [] (snd r) g md_am4 /\ ub_same s3 (snd r))).
  { unfold md_am4. eapply (install_direct_spec [] U0 s3 g md_r md_rg (md_maplen n)); [exact HI3 | reflexivity | exact region_s3 | reflexivity | reflexivity | exact L3 | lia | |].
    - intros q a Hu. apply HusedX in Hu. pose proof (fresh_s2 q a Hu). lia.
    - intros s' -> H1 H2 H3. cbn [snd]. auto. }
  exact (itok_yields _ _ [] (tt, md_s4) T (yields_setm s3 g md_am4)).
Qed.

Lemma ctr_range : ltac2:(tb__ "0|3|
S0S0S4aZ0M0S8Vs;A1M1A2S4eG1S4fZ2Z20A2A2A2S0S4aG0SbVs;A1M2A2S4aG2ZffA2A2A2").
Proof using HI. pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&C8&C9&_). split; [exact C9 | exact C8]. Qed.
Definition md_ctr1 : Z := ltac2:(tb__ "0|1|
S53S4cS8Vs;A1Z1M0A2S4bS4fZ2Z20A2G0A2A2").
Definition md_s5 : astate := set_mmap_counter md_ctr1 md_s4.
Lemma ctr1_eq : ltac2:(tb__ "0|2|
S0S4aZ0S8Vs;A1M0A2S4eG0S4fZ2Z20A2M1A2A2S1S5S43S51S4cG0Z1A2G1A2A3F_;").
Proof using . intros H. unfold md_ctr1. change (2 ^ 32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma Inv_s5 : ltac2:(tb__ "0|0|
S62S56S6A1S59S57S6S5A2S5cS6S5Vg;Z0A4A2S63S40A4").
Proof using HI HI3 Hframe Hn HusedX. unfold md_s5. pose proof ctr_range. apply Inv_set_mmap_counter; [exact (proj1 s4_facts) | apply land32_range; lia]. Qed.

Definition md_stride : Z := ltac2:(tb__ "0|0|
S4bS6dVn;A1S9A2").
Definition md_slack : Z := ltac2:(tb__ "0|0|
S52S4bS4bS3cScA2Vn;A2S9A2").
Definition md_off0 : Z := if md_slack =? 0 then 0 else Z.land md_ctr1 255.
Definition md_off : Z := fold_off md_slack md_off0.
Definition md_reserved : Z := ltac2:(tb__ "0|0|
S4bS4bS4bS3cScA2S4dS9S3aA2A2Vn;A2").
Definition md_rsv : Z := if 5 <=? md_reserved then 5 else md_reserved.
Definition md_hdr : Z * Z := ltac2:(tb__ "0|1|
S55S57S5S5A2L_;S50S3aZ0M0A2S5cS5S5S4dS49Z20A2G0A4S5cS5S5Ze0S3aA4X55x2").
Definition md_fr : frame := ltac2:(tb__ "0|0|
S2cS3aVn;S23A3").
Definition md_am6 : ameta := ltac2:(tb__ "0|0|
S37S3bZ0S2eS59S57S5S5A2S48A2S59S2aS47A2A2A3").
Definition md_s6 : astate := ltac2:(tb__ "0|0|
S72Vg;SdS42A1S40A3").
Definition md_p : sptr := ltac2:(tb__ "0|0|
S30S34S3bZ0A2S4dS9S3aA2A2").

Lemma stride_am4 : ltac2:(tb__ "0|0|
S1S5S36S3bA1S3cA3").
Proof using Hn.
  pose proof (md_len_facts n Hn) as (L1 & L2 & L3 & L4 & L5). unfold md_am4, direct_am, stride_of, md_stride. cbn [am_last am_maplen am_sc Z.eqb andb].
  destruct (md_maplen n =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. rewrite L3. unfold PGSZ. reflexivity.
Qed.
Lemma MT_s5_g : ltac2:(tb__ "0|0|
S1S5aSaA1S67S40Vg;A2S59SaSdS3bA1A2A3").
Proof using . unfold md_s5, MT. cbn [set_mmap_counter st_metas]. fold (MT md_s4 g). unfold md_s4. apply MT_upd_same. Qed.
Lemma slack_facts : ltac2:(tb__ "0|1|
S0S4aZ0M0S41A2S0S4aS4dS9S41A2S4bS4bS3cScA2Vn;A2A2S0S0S4aG0S3dA2S4aS3dZffA2A2S0S1S5S41G0A3S1S5S3dG0A3F_;S0S0S4aG0S3aA2S4aS3aS41A2A2S4aS3aS3dA2A2A2A2A2A2").
Proof using Hn.
  pose proof (md_len_facts n Hn) as (L1 & L2 & L3 & L4 & L5). unfold md_needed, IB, UNIT, PGSZ in *.
  assert (S0 : 0 <= md_slack) by (unfold md_slack, md_stride, UNIT, IB; apply Z.div_pos; lia).
  assert (S1 : 16 * md_slack <= md_stride - 4 - n) by (unfold md_slack, md_stride, UNIT, IB in *; pose proof (Z.mul_div_le (md_len n - 16 - 4 - n) 16 ltac:(lia)); lia).
  assert (O0 : 0 <= md_off0 <= 255).
  { unfold md_off0. destruct (md_slack =? 0); [lia|]. split; [apply Z.land_nonneg; right; lia|]. rewrite Z.land_comm. apply land_le_l. lia. }
  repeat split; try lia.
  - unfold md_off0. intros ->. reflexivity.
  - apply fold_off_ok; lia.
  - apply fold_off_ok; lia.
  - apply fold_off_le; lia.
Qed.

Lemma yields_enframe : ltac2:(tb__ "0|0|
S6bS57S6S22A2S29Vg;Z0Vn;S43S23S40A6S56S57S2bS5A2A1S5cS6S22S46S39A4A4").
Proof using Hn.
  pose proof (md_len_facts n Hn) as (L1 & L2 & L3 & L4 & L5). pose proof slack_facts as (S0 & S1 & O0 & Oz & OF & OL).
  unfold enframe. apply (yields_bind0 _ _ md_s5 [] md_am4 md_s5); [apply yields_getm; exact MT_s5_g|].
  unfold mcheck. replace ((0 <=? 0) && (0 <=? am_last md_am4))%bool with true by reflexivity.
  apply (yields_bind0 _ _ md_s5 [] tt md_s5); [apply yields_ret|].
  lazy zeta. rewrite stride_am4. change ((md_stride - IB - n) / UNIT) with md_slack.
  apply (yields_bind0 _ _ md_s5 [] md_off0 md_s5).
  { unfold md_off0. destruct (md_slack =? 0); [apply yields_ret|].
    change (ss_hdr (nth_slot md_am4 0)) with (Some (0, 0)). cbn [Z.eqb]. apply yields_ret. }
  change (if md_slack <? md_off0 then _ else md_off0) with md_off.
  unfold massert. replace (md_off <=? md_slack) with true by (symmetry; apply Z.leb_le; lia).
  apply (yields_bind0 _ _ md_s5 [] tt md_s5); [apply yields_ret|].
  apply (yields_bind0 _ _ md_s5 [] tt md_s6).
  { unfold md_s6, md_am6, md_hdr, md_fr, md_rsv, md_reserved. rewrite Z.mul_0_r, Z.add_0_l. change (0 / UNIT) with 0. apply yields_setm. }
  unfold md_p. apply yields_ret.
Qed.

Lemma Inv_s6 : ltac2:(tb__ "0|0|
S0S62S56S6A1S5dS57S6S5A2A1S63S39A4S0S0S4aZ0S3aA2S4aS3aZffA2A2S4aS4cS4dS9S3aA2Vn;A2S4bS3cScA2A2A2A2").
Proof using HI HI3 Hframe Hn HusedX.
  pose proof (md_len_facts n Hn) as (L1 & L2 & L3 & L4 & L5). pose proof slack_facts as (S0 & S1 & O0 & Oz & OF & OL). pose proof Hn as [N1 N2]. unfold md_needed, IB, UNIT, PGSZ in L1, L2, L3.
  assert (T : itok (enframe g 0 n md_ctr1 FUser md_s5) (fun r => Inv [] None U0 (snd r) /\ exists off, 0 <= off <= 255 /\ UNIT * off + n <= md_stride - IB /\ fst r = padd (slot_start md_am4 0) (UNIT * off))).
  { eapply (enframe_spec [] U0 md_s5 g 0 n md_ctr1 FUser md_am4).
    - exact Inv_s5.
    - unfold usedX, MTX. rewrite MT_s5_g. cbn. reflexivity.
    - lia.
    - rewrite stride_am4. unfold md_stride, IB, UNIT. lia.
    - unfold md_ctr1. pose proof ctr_range. apply Z.land_nonneg. left. lia.
    - discriminate.
    - intros _. split; [reflexivity|]. split; [exact N1|]. cbn [am_maplen md_am4 direct_am]. unfold md_needed, IB, UNIT, PGSZ in *. lia.
    - cbn. lia.
    - intros off s' hdr Hoff Hfit _ -> HI'. cbn [fst snd]. split; [exact HI'|]. exists off. rewrite stride_am4 in Hfit. auto. }
  destruct (itok_yields _ _ [] (md_p, md_s6) T yields_enframe) as [HI6 (off & Ho1 & Ho2 & Hp)]. cbn [fst snd] in HI6, Hp.
  split; [exact HI6|].
  assert (E : off = md_off).
  { unfold md_p in Hp. apply (f_equal poff) in Hp. rewrite !poff_padd in Hp. unfold UNIT in Hp. lia. }
  subst off. auto.
Qed.

Lemma ub_same_s5 : ub_same s md_s5.
Proof using HI HI3 Hframe Hn Hub3 HusedX.
  eapply ub_same_trans; [exact ub_same_s2|]. eapply ub_same_trans; [exact Hub3|].
  eapply ub_same_trans; [exact (proj2 (proj2 s4_facts))|]. apply ub_same_metas. reflexivity.
Qed.
Lemma blocks_s6 : ltac2:(tb__ "0|2|
S3S58S57S6S5A2M0A1M1G1S3G1G1S0S1G1S69S39A1S5eG0R2S5bG0S5cS6S5S46Vn;A4R1A3A3A3S1G1S69Vs;A1S5eG0R2R1A3A3A2Ll2;A2Ll1;A2").
Proof using HI HI3 Hframe Hn Hub3 HusedX.
  pose proof Inv_s6 as (HI6 & _). pose proof slack_facts as (S0 & S1 & O0 & Oz & OF & OL).
  destruct (enframe_inserts [] (Some (g, 0)) U0 s md_s5 g md_am4 0 (mkSlot (Some md_hdr) (Some md_fr)) md_p n Inv_s5 ub_same_s5 MT_s5_g
             ltac:(cbn; lia) eq_refl eq_refl ltac:(unfold slotst_block, md_fr, md_p; cbn [ss_fr fr_kind fr_off fr_n]; reflexivity)) as (l1 & l2 & E1 & E2).
  exists (map fst l1), (map fst l2).
  rewrite (user_blocks_ublist md_s6 (proj1 (inv_keys HI6))), (user_blocks_ublist s (proj1 (inv_keys HI))).
  unfold md_s6, md_am6. rewrite E1, E2, !map_app. cbn [map fst]. split; reflexivity.
Qed.

Lemma s6_shape : ltac2:(tb__ "0|3|
S0S1S58S7A1SeS39A1SeVs3;A1A3S0S1S58S6A1M0S12S39A1S12Vs3;A1A3S0S1S5S8S39A1S43A3S0S1S55S1aS39A1S1aVs3;A1A3S0S1S5SbS39A1SbVs3;A1A3S0S1S58S5A1M1S1dS39A1S1dVs3;A1A3S0S1G1S17S39A1S17Vs3;A1A3S0S1S58S5aS6A1M2A1SfS39A1SfVs3;A1A3S0S1G1S1eS39A1S1eVs3;A1A3S0S1S24S18S39A1S18Vs3;A1A3S0S1G2S19S39A1S19Vs3;A1A3S0S1S6S13S39A1S13Vs3;A1A3S0S1S5S16S39A1S16Vs3;A1A3S0S1S5S14S39A1S14Vs3;A1A3S0S1S5S1bS39A1S1bVs3;A1A3S0S1G2S10S39A1S10Vs3;A1A3S0S1G2S11S39A1S11Vs3;A1A3S0S1S6S15S39A1S15Vs3;A1A3S0S1S58S57S6SaA2A1S1cS39A1S2fS1cVs3;A1Vg;SdS42A1A3A3S1G0S65S39A1S65Vs3;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using HI3 Hctr3 Hframe Hkey Hraw Hub3 HusedX.
  assert (K4 : keys md_s4 = keys s3) by (unfold md_s4; apply keys_upd_In; exact Hkey).
  assert (K5 : keys md_s5 = keys s3) by (rewrite <- K4; reflexivity).
  assert (K : keys md_s6 = keys s3).
  { unfold md_s6. rewrite keys_upd_In; [exact K5|]. rewrite K5. exact Hkey. }
  unfold md_s6, md_s5, md_s4, upd_meta in *. destruct s3; cbn in *. repeat split; try reflexivity; [apply mupdate_mupdate_same | exact K].
Qed.
Lemma footprint_s6 : ltac2:(tb__ "0|0|
S1S58S57S6aS5A2A1S68S39A1S68Vs3;A1A3").
Proof using HI3 Hctr3 Hframe Hkey Hraw Hub3 HusedX. pose proof s6_shape as (R & A & _). unfold footprint, region_of. rewrite R, A. reflexivity. Qed.
Lemma MT_s6 : ltac2:(tb__ "0|1|
S6S1S5aSaA1M0S67S39R1A2S55G0L_;S35R1Vg;A2S59SaSdS42A1A2S67Vs3;R1A2X55x2A3Fq;").
Proof using .
  intros q. unfold md_s6. rewrite MT_upd. destruct (sptr_eqb q g) eqn:E; [reflexivity|].
  transitivity (MT md_s4 q); [reflexivity|]. unfold md_s4. rewrite MT_upd, E. reflexivity.
Qed.

End Direct.
