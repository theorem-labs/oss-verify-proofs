(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "sub"; "eqb"; "mul"; "lor"; "leb"; "ltb"; "testbit"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "cell_range"; "LMem"; "MCell"; "VZ"; "image"; "cell_holds"; "loc"; "ranges_disjoint"; "alloc_owned"; "frame_ptr"; "group_extent"; "meta_bits"; "META_freed"; "MT"; "VP"; "VSec"; "footprint"; "frames"; "hdr_byte3"; "hdr_off16"; "ly_ctx"; "usedX"; "yields"; "CTX_secret"; "LCtx"; "META_avail"; "META_bits"; "META_mem"; "WF"; "crange"; "le_byte"; "mc_w"; "range_incl"; "region_of"; "sval"; "used_metas"; "user_blocks"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "option"; "Some"; "bool"; "None"; "fst"; "snd"; "nil"; "unit"; "length"; "true"; "tt"; "andb"; "false"; "nat"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost.Gap"; "gzp"; "gzg"; "qs1"; "gn"; "qbv1"; "gze"; "gzm"; "gza"; "qblk"; "qwin"; "H16'"; "H3'"; "gp"; "Cfreed'"; "gst"; "qam2"; "qavoids"; "qbv0"; "qrv1"; "qrv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "frame"; "padd"; "fr_off"; "am_freed"; "ameta"; "astate"; "nth_slot"; "slotst"; "MUsed"; "bit"; "IB"; "am_mem"; "slot_start"; "am_avail"; "am_last"; "mslot"; "region"; "am_sc"; "mkSlot"; "ss_fr"; "ss_hdr"; "stride_of"; "AREA_HDR"; "META_SIZE"; "PGSZ"; "UNIT"; "am_aidx"; "am_maplen"; "am_next"; "am_prev"; "am_set_freed"; "am_slots"; "free"; "kreq"; "prid"; "FUser"; "METAS_PER_AREA"; "RkMap"; "SP"; "fkind"; "fr_kind"; "ones"; "rg_kind"; "rkind"; "st_areas"; "st_init_done"; "upd_slot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "reprO"; "slot_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "wz"; "addr_of"; "mc_img_hi"; "mc_img_lo"; "statics_ok"; "topL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost"; "free_quick_post"; "quick_case"; "release_slot_am"; "am_post"; "released_slot"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel"; "frame_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MInv"; "mkMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones"; "zone_range"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfSurgery MallocWfGeom MallocWfRepr MallocWfMain
  MallocLayout MallocFooter MallocFooterLemmas NestTier MallocIface MallocLaws FreeQuickModel Zones ImageUpd FpLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Definition quick_case (s : astate) (q : sptr) (g : sptr) (am : ameta) (i : Z) (fr : frame) : Prop := ltac2:(tb__ "0|4|
S1S48S39S39S39S5dS62A2M0S0A2M1S5eA2S38G1S5eS38G0S0S38S5dS62Vg;Vam;A4Vi;A4Vfr;A4S24Vs;A1A3S1S2S85S86Vfr;A1S81A3S1S2S5dVq;S1cVam;Vi;Vfr;A3A3S1S4S2S0S61Vam;A1M2Z0A3A1S1S4S2S0S6SdG2S6bVam;A1A2S67Vi;A1A2S87S6cVam;A1M3A1A3A1S1S8S6fVam;A1Z30A2S7Z1G3A2A2A2A2A2A2A2").

Definition released_slot (am : ameta) (i : Z) : slotst := ltac2:(tb__ "0|2|
S64Vam;Vi;A2S65S3aS5eA1S65Lx;S71R1A1S5eS3cS65L_;SbS60R1A1Z0M0A2S70S3bS39S0S0A2S38S0S0ZffG0A4A2S3dS5eA1M1A2S70S72R2A1G1A2X3cx2Lfr;R1X3ax2Tsl;").

Definition release_slot_am (am : ameta) (i : Z) : ameta := ltac2:(tb__ "0|0|
S8cVam;Vi;S9bVam;Vi;A2A3").

Definition free_quick_post (s : astate) (g : sptr) (am : ameta) (i : Z) : astate := ltac2:(tb__ "0|1|
S96Vg;S66S7cS6S61Vam;A1S67Vi;A1A2S99Vam;Vi;A2M0A2A1S96Vg;S66G0A1Vs;A3A3").

Definition am_post (am : ameta) (i : Z) : ameta := ltac2:(tb__ "0|0|
S7cS6S61Vam;A1S67Vi;A1A2S99Vam;Vi;A2A2").

Lemma free_quick_post_eq s g am i : ltac2:(tb__ "0|0|
S2S63S97Vs;Vg;Vam;Vi;A4S96Vg;S66S9aVam;Vi;A2A1Vs;A3A3").
Proof. unfold free_quick_post, am_post. apply upd_meta_twice. Qed.

Lemma free_quick_yields : ltac2:(tb__ "0|0|
S63S5dS5dS62S0S5eS2fR6A1S98R7R6R5R4R3R2A6S29S39S41S63A2S7eS3bS5dR7A2R8A2S40S39S7fS0A2A1S38S41S63S44S97R8R6R5R4A4A4A4F_;F_;Ffr;Fi;Fam;Fg;Fq;Fs;").
Proof.
  intros s q g am i fr HW (Hfr & Hk & -> & Hfz & Hall & Hsc & Hlast).
  pose proof (get_meta_ok s g am i fr HW Hfr) as GM. cbn beta in GM.
  destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfind).
  destruct (frames_inv s g am i fr HW Hfr) as (Hu & Hi & Hsl).
  pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as HMT. unfold MT in HMT.
  pose proof (inv_groups HW g am Hu) as (Gm & _ & Gsl & _).
  pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hsl in S3. destruct S3 as (Halloc & _).
  unfold allocated in Halloc. apply Bool.negb_true_iff in Halloc.
  assert (Hmask : Z.land (Z.lor (am_freed am) (am_avail am)) (bit i) = 0).
  { unfold bit. apply Z.bits_inj'. intros k Hk0. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec k i) as [->|Hne].
    - rewrite Z.lor_comm, Halloc. reflexivity.
    - rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r. }
  cbn -[find_frame_in free_quick_post mupdate mlookup Z.lor Z.land bit ones Z.eqb Z.add nontrivial_free release_slot getm setm massert].
  rewrite Hfind. cbn [ret ibind fst snd].
  unfold getm at 1. unfold bind, get. cbn [ibind]. rewrite HMT. cbn [ret ibind].
  unfold release_slot, getm, bind, get. cbn [ibind]. rewrite HMT. cbn [ret ibind]. unfold setm, modify. cbn [ibind].
  unfold massert. rewrite Hmask. cbn [Z.eqb ret ibind].
  replace (negb (am_freed am =? 0) && negb (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)))%bool with true
    by (symmetry; apply andb_true_intro; split; apply Bool.negb_true_iff, Z.eqb_neq; assumption).
  unfold getm, get. cbn [ibind]. cbn [st_metas set_metas]. rewrite mlookup_mupdate_same. cbn [ret ibind].
  reflexivity.
Qed.

Section PostMeta.
  Variables (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame).
  Hypothesis HW : WF s.
  Hypothesis FFx : ltac2:(tb__ "0|0|
S9eVs;Vg;Vam;Vi;Vfr;A5").

  Let am2 := am_post am i.

  Lemma am2_fields : ltac2:(tb__ "0|1|
S1S2S3aS5dA1M0S7bVam2;A1S7bVam;A1A3S1S2G0S7aVam2;A1S7aVam;A1A3S1S2S5dS69Vam2;A1S69Vam;A1A3S1S2S0S6bVam2;A1S6bVam;A1A3S1S2S0S61Vam2;A1S6S61Vam;A1S67Vi;A1A2A3S1S2S0S6cVam2;A1S6cVam;A1A3S1S2S0S6fVam2;A1S6fVam;A1A3S1S2S0S79Vam2;A1S79Vam;A1A3S2S0S78Vam2;A1S78Vam;A1A3A2A2A2A2A2A2A2A2").
  Proof using . repeat split; reflexivity. Qed.

  Lemma am2_stride : ltac2:(tb__ "0|0|
S2S0S73Vam2;A1S73Vam;A1A3").
  Proof using i. reflexivity. Qed.

  Lemma am2_slot_start j : ltac2:(tb__ "0|0|
S2S5dS6aVam2;Vj;A2S6aVam;Vj;A2A3").
  Proof using i. reflexivity. Qed.

  Lemma am2_bits : ltac2:(tb__ "0|0|
S2S0S1eVam2;A1S1eVam;A1A3").
  Proof using i. reflexivity. Qed.

  Lemma am2_extent : ltac2:(tb__ "0|0|
S2S0S1dVam2;A1S1dVam;A1A3").
  Proof using i. reflexivity. Qed.

  Lemma am2_slots_len : ltac2:(tb__ "0|0|
S2S47S42S65S7dVam2;A1A2S42S65S7dVam;A1A2A3").
  Proof using i. unfold am2, am_post, release_slot_am, upd_slot. cbn. apply length_lupd. Qed.

  Lemma am2_nth_slot j : ltac2:(tb__ "0|2|
S7Z0M0Vj;A2S2S65S64Vam2;Vj;A2S3cS65L_;SbVj;Vi;A2S70S3cS3aS39S0S0A2M1A1L_;SbS60Vfr;A1G0A2S3bG1S38S0S0ZffG0A4A2S72S64Vam;Vi;A2A1X3cx2S3dS5eA1A2S64Vam;Vj;A2X3cx2A3F_;").
  Proof using FFx HW.
    intros Hj. pose proof (ff_i _ _ _ _ _ FFx) as Hi. pose proof (ff_slot _ _ _ _ _ FFx) as Hsl.
    pose proof (ff_used _ _ _ _ _ FFx) as Hu.
    unfold am2, am_post, release_slot_am, upd_slot, nth_slot. cbn [am_slots am_set_freed am_set_slots].
    rewrite nth_lupd.
    assert (Hlen : length (am_slots am) = Z.to_nat (am_last am + 1)).
    { pose proof (inv_groups HW g am Hu) as ((_ & _ & L & _) & _). exact L. }
    destruct (j =? i) eqn:E.
    - apply Z.eqb_eq in E. subst j. rewrite Nat.eqb_refl.
      replace (Nat.ltb (Z.to_nat i) (length (am_slots am))) with true by (symmetry; apply Nat.ltb_lt; rewrite Hlen; lia).
      cbn [andb]. unfold released_slot, nth_slot. unfold nth_slot in Hsl. rewrite Hsl. destruct (fr_off fr =? 0); reflexivity.
    - apply Z.eqb_neq in E. replace (Nat.eqb (Z.to_nat j) (Z.to_nat i)) with false by (symmetry; apply Nat.eqb_neq; lia).
      reflexivity.
  Qed.
End PostMeta.

Section Gap.
  Variables (C : mconsts) (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame) (a : sptr) (k : Z).
  Variables (rd0 rd1 : word -> option byte) (wok0 wok1 : word -> bool) (vm : VmMaps).
  Hypothesis HMI : ltac2:(tb__ "0|0|
S9fVC;Sa0Vs;VL;A2Vrd0;Vwok0;Vvm;A5").
  Hypothesis FFx : ltac2:(tb__ "0|0|
S9eVs;Vg;Vam;Vi;Vfr;A5").
  Hypothesis HQ : ltac2:(tb__ "0|0|
S98Vs;S1cVam;Vi;Vfr;A3Vg;Vam;Vi;Vfr;A6").
  Hypothesis Har : ltac2:(tb__ "0|0|
S1S48S5dVa;S8aVs;A1A3S1S1S7Z0Vk;A2S8Vk;S82A2A2S2S5dVg;S5fVa;S6S74ScS75Vk;A2A2A2A3A2A2").
  Hypothesis HS : statics_in_image C.

  Definition gp : sptr := ltac2:(tb__ "0|0|
S1cVam;Vi;Vfr;A3").
  Definition gn : Z := fr_n fr.
  Definition gzp : Z := addr_of L gp.
  Definition gzg : Z := addr_of L g.
  Definition gst : Z := ltac2:(tb__ "0|0|
S91VL;S6aVam;Vi;A2A2").
  Definition gze : Z := ltac2:(tb__ "0|0|
S91VL;S8fVam;Vi;A2A2").
  Definition gzm : Z := ltac2:(tb__ "0|0|
S91VL;S69Vam;A1A2").
  Definition gza : Z := addr_of L a.
  Definition qs1 : astate := ltac2:(tb__ "0|0|
S97Vs;Vg;Vam;Vi;A4").
  Definition qam2 : ameta := am_post am i.

  Definition qbv0 : byteview := byteview_of rd0 wok0.
  Definition qbv1 : byteview := byteview_of rd1 wok1.
  Definition qrv0 : byteview := byteview_of rd0 (fun _ => true).
  Definition qrv1 : byteview := byteview_of rd1 (fun _ => true).

  Definition qwin (x : Z) : option Z := ltac2:(tb__ "0|4|
S3cS3aS0A1L_;M0SbSaS49Z3A2Vx;A2S3bS0ZffA2G0SbSaS49Z2M1A2Vx;A2S3bS0Z0A2M2G0SbSaS49Z1A2Vx;A2G2G0S45SeS6S4aZ1cA2M3Vx;A2SfVx;S6S4aZ20A2A2A2S3bS0S31S6S61Vam;A1S9G1Vi;A2A2U4S11SaVx;G3A2A1A3A2S3dS0A1X3cx2X3cx2X3cx2X3cx2").
  Definition qblk (x : Z) : Prop := ltac2:(tb__ "0|0|
S1S7S49Vx;A2S8Vx;S6S49S4cA2A2A2").

  Hypothesis V1 : ltac2:(tb__ "0|1|
S0S1S7Z0R1A2S8R1S9Z2Z40A2A2A2S4S51R2A1A1S2S3aS0A1S52R3A1S3dS0A1A3S1S2S3aS9cQ8A1A1Vrd1;S90R4A1M0A1Vrd0;G0A1A3S2S3cVwok1;G0A1Vwok0;G0A1A3A2F_;F_;F_;Fx;").
  Hypothesis V2 : ltac2:(tb__ "0|1|
S0S51R1A1S1S2S3cVwok1;S90R2A1A1S43A3S5S9cQ8A1M0G0S2S3aG0A1Vrd1;S90R3A1A1S3bG0R1A2A3Lb;A2A2F_;Fx;").
  Hypothesis V3 : ltac2:(tb__ "0|3|
S0S0S2S3aS0A1S52R2A1S3bS0R1A2A3S1S2S3cVwok1;S90R3A1M0A1S43A3S2S3aS9cQ8M1A1M2A1Vrd1;G0A1S3bG2S9dG1R2A2A2A3A2F_;Fb;Fx;").

  Lemma G_W : WF s. Proof using HMI. exact (proj1 HMI). Qed.
  Lemma G_fr : ltac2:(tb__ "0|2|
S48S39S39S39S5dS62A2M0S0A2M1S5eA2S38G1S5eS38G0S0S38S5dS62Vg;Vam;A4Vi;A4Vfr;A4S24Vs;A1A3"). Proof using HQ. exact (proj1 HQ). Qed.
  Lemma G_kind : fr_kind fr = FUser. Proof using HQ. exact (proj1 (proj2 HQ)). Qed.
  Lemma G_u : ltac2:(tb__ "0|0|
S28S40S5dA1Vs;Vg;Vam;A4"). Proof using FFx. exact (ff_used _ _ _ _ _ FFx). Qed.
  Lemma G_um : ltac2:(tb__ "0|0|
S48S39S5dS62A2S38S5dS62Vg;Vam;A4S36Vs;A1A3"). Proof using FFx HMI. apply (used_metas_usedX s g am G_W). apply G_u. Qed.
  Lemma G_i : ltac2:(tb__ "0|0|
S1S7Z0Vi;A2S7Vi;S6cVam;A1A2A2"). Proof using FFx. exact (ff_i _ _ _ _ _ FFx). Qed.
  Lemma G_sl : ltac2:(tb__ "0|0|
S2S3aS5eA1S71S64Vam;Vi;A2A1S3bS5eVfr;A2A3"). Proof using FFx. exact (ff_slot _ _ _ _ _ FFx). Qed.
  Lemma G_MT : ltac2:(tb__ "0|0|
S2S3aS6dA1S20Vs;Vg;A2S3bS6dS66Vam;A1A2A3"). Proof using FFx. exact (ff_MT _ _ _ _ _ FFx). Qed.
  Lemma G_ND : List.NoDup (keys s). Proof using HMI. exact (proj1 (inv_keys G_W)). Qed.
  Lemma G_repr : ltac2:(tb__ "0|0|
S8eVL;Vs;S5aA3"). Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 HMI)))). Qed.
  Lemma G_L : layout_ok L s. Proof using HMI. exact (proj1 (proj1 G_repr)). Qed.
  Lemma G_blk : ltac2:(tb__ "0|0|
S48S39S5dS0A2S38S5dS0S55S4cA4S37Vs;A1A3").
  Proof using FFx HMI HQ.
    unfold gp, gn, user_blocks. apply in_flat_map. exists (g, am). split; [exact G_um|]. cbn [snd].
    apply in_flat_map. exists i. split; [apply In_zseq; pose proof G_i; lia|]. rewrite G_sl, G_kind. left. reflexivity.
  Qed.
  Lemma G_s' : ltac2:(tb__ "0|0|
S2S63S4bS96Vg;S66S58A1Vs;A3A3"). Proof using . unfold qs1, qam2. apply free_quick_post_eq. Qed.
  Lemma G_y : ltac2:(tb__ "0|0|
S29S39S41S63A2S7eS3bS5dS55A2Vs;A2S40S39S7fS0A2A1S38S41S63S44S4bA4A4").
  Proof using HMI HQ. unfold qs1, gp. exact (free_quick_yields s _ g am i fr G_W HQ). Qed.
  Lemma G_W' : WF qs1.
  Proof using FFx HMI HQ. exact (free_wf s gp gn [] qs1 G_W G_blk G_y). Qed.
  Lemma G_L' : layout_ok L qs1. Proof using HMI. rewrite G_s'. exact G_L. Qed.
  Lemma G_MT' : ltac2:(tb__ "0|0|
S2S3aS6dA1S20S4bVg;A2S3bS6dS66S58A1A2A3"). Proof using . rewrite G_s', MT_upd_same. reflexivity. Qed.
  Lemma G_u' : ltac2:(tb__ "0|0|
S28S40S5dA1S4bVg;S58A4"). Proof using . apply usedX_intro; [reflexivity | exact G_MT']. Qed.
  Lemma G_sl' : ltac2:(tb__ "0|0|
S2S3aS5eA1S71S64S58Vi;A2A1S3dS5eA1A3").
  Proof using FFx HMI. unfold qam2. rewrite (am2_nth_slot s g am i fr G_W FFx i) by (pose proof G_i; lia). rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma G_hdr : ltac2:(tb__ "0|1|
S3S2S3aS39S0S0A2M0A1S72S64Vam;Vi;A2A1S3bG0S38S0S0S25Vam;Vi;Vfr;A3S26Vam;Vi;Vfr;A3A4A2A3S4S2S0S60Vfr;A1Z0A3A1A2").
  Proof using FFx HMI.
    pose proof (inv_groups G_W g am G_u) as (_ & _ & Gsl & _). pose proof (Gsl i G_i) as (_ & _ & S3). rewrite G_sl in S3.
    destruct S3 as (_ & _ & _ & H0). destruct (Z.eq_dec (fr_off fr) 0) as [E|E]; [left; exact (H0 E) | right; exact E].
  Qed.

  Lemma G_geom : ltac2:(tb__ "0|7|
S1S7Z10S73Vam;A1M0A2S1S7Z0M1S60Vfr;A1M2A2S1S7G1S4cA2S1S7S6ScS77G2A2M3S4cA2SaG0S68A2M4A2S1S2S0S57S6S6S4fS77A2ScG0Vi;A2A2A3S1S2S0S49S6S57G3A2A3S1S2S0S4eSaS6S57G0A2S68A2A3S1S2S39S0S0A2Sa1VL;Vam;Vi;A3S38S0S0SaS57Z3M5A2S6G4G5A2A4A3S1S8G1S4fA2S1S8S6S4eS68A2S9Z2Z3fA2A2S5S39S19S0A2M6G6S1S48G6R1S23Vs;A1A3S1S33S38S0S0S4fS6S1dVam;A1S68A2A4S30VL;R1A2A2S2S19S3eS19S0R1A3S14S84S80S69Vam;A1A1G1A2A1A3A2A2Lrg;A2A2A2A2A2A2A2A2A2A2A2").
  Proof using FFx HMI.
    pose proof (inv_groups G_W g am G_u) as G0. pose proof (stride_pos _ _ _ _ _ G0) as Sp.
    pose proof (ff_off _ _ _ _ _ FFx) as Ho. pose proof (ff_n _ _ _ _ _ FFx) as Hn. pose proof (ff_fit _ _ _ _ _ FFx) as Hfit.
    destruct (used_group_region [] None U0 s g am G_W G_u) as (rg & Hr & Hk & Hl & Ho0 & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
    pose proof G_L as (_ & _ & _ & POS). destruct (POS _ InR) as [P1 P2]. unfold crange, loc_addr in P1, P2. cbn [fst snd] in P1, P2.
    pose proof G_i as Hi.
    assert (E1 : gst = gzm + UNIT + stride_of am * i).
    { unfold gst, gzm, addr_of, loc_addr, slot_start. destruct (am_mem am); cbn [padd]. lia. }
    assert (E2 : gzp = gst + UNIT * fr_off fr).
    { unfold gzp, gst, gp, addr_of, loc_addr, frame_ptr, slot_start. destruct (am_mem am); cbn [padd]. lia. }
    assert (E3 : gze = gst + stride_of am - IB).
    { unfold gze, gst, addr_of, loc_addr, slot_end, slot_start. destruct (am_mem am); cbn [padd]. lia. }
    assert (Hsi : 0 <= stride_of am * i /\ stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by (split; nia).
    assert (Ezm : gzm = ly_reg L (prid (am_mem am)) + poff (am_mem am)) by (unfold gzm, addr_of, loc_addr; destruct (am_mem am); reflexivity).
    unfold gn. split; [exact Sp|]. split; [lia|]. split; [exact Hn|]. split; [exact Hfit|].
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    split; [unfold zone_range; rewrite E1; unfold gzm, addr_of; reflexivity|].
    split; [lia|]. split; [unfold group_extent in Hext; lia|].
    exists (LMem (SP (prid (am_mem am)) 0), rg_len rg). split; [exact InR|]. split; [|reflexivity].
    unfold range_incl, crange, loc_addr. cbn [fst snd]. lia.
  Qed.

  Lemma G_area_geom : ltac2:(tb__ "0|0|
S1S2S0S4aS6S6S50S74A2ScS75Vk;A2A2A3S1S8Z0S50A2S1S8S6S50S76A2S9Z2Z3fA2A2S1S48S39S19S0A2S38S19S0S14Va;A1S76A4S23Vs;A1A3S5S6eS6eS1S2S3aS6eA1S34Vs;S80Va;A1A2S3bS6eR1A2A3S4S2S89S88R1A1S83A3A1A2Lrga;A2A2A2A2A2").
  Proof using HMI Har.
    destruct Har as (Ha & Hk & Eg).
    assert (InA : In (LMem a, PGSZ) (footprint s)).
    { unfold footprint. right. apply in_app_iff. left. apply in_map_iff. exists a. auto. }
    pose proof G_L as (_ & _ & _ & POS). destruct (POS _ InA) as [P1 P2]. unfold crange, loc_addr in P1, P2. cbn [fst snd] in P1, P2.
    split; [unfold gzg, gza, addr_of, loc_addr; rewrite Eg; destruct a; cbn [padd]; lia|].
    assert (Eza : gza = match a with SP r o => ly_reg L r + o end) by (unfold gza, addr_of, loc_addr; reflexivity).
    destruct a as [ra oa]. split; [lia|]. split; [lia|]. split; [exact InA|].
    pose proof (inv_areas G_W) as (_ & A2 & _). destruct (A2 _ Ha) as (r & o & rga & Ea & _ & _ & Hra & _ & _ & Hkind).
    injection Ea as <- <-. exists rga. split; [exact Hra|]. destruct (rg_kind rga); [discriminate|discriminate|destruct Hkind].
  Qed.

  Lemma BV1 : ltac2:(tb__ "0|1|
S0S1S7Z0R1A2S8R1S9Z2Z40A2A2A2S4S51R2A1A1S2S3aS0A1M0S52R3A1S3dS0A1A3S1S2G0S4dR4A1S5aR4A1A3S2G0S5bR4A1S5cR4A1A3A2F_;F_;F_;Fx;").
  Proof using V1.
    intros x Hx Hb Hw. destruct (V1 x Hx Hb Hw) as [E1 E2].
    unfold qbv1, qbv0, qrv1, qrv0, byteview_of. unfold wz in E1, E2. rewrite E1, E2. split; reflexivity.
  Qed.

  Lemma BV2 : ltac2:(tb__ "0|0|
S0S1S7Z0R1A2S8R1S9Z2Z40A2A2A2S51R2A1S4S2S3aS0A1S4dR3A1S3dS0A1A3A1F_;F_;Fx;").
  Proof using V2.
    intros x Hx Hb. destruct (V2 x Hb) as [E1 [b E2]]. unfold qbv1, byteview_of. unfold wz in E1, E2.
    replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    cbn [andb]. rewrite E1, E2. discriminate.
  Qed.

  Lemma BV3 : ltac2:(tb__ "0|2|
S0S0S1S7Z0R2A2M0S8R2S9Z2Z40A2A2A2S1G0S8R2Z100A2A2S2S3aS0A1M1S52R4A1S3bS0R3A2A3S2G1S4dR5A1S3bS0R4A2A3F_;F_;F_;Fb;Fx;").
  Proof using V3.
    intros x b Hx Hb Hw. destruct (V3 x b Hw) as [E1 E2]. unfold qbv1, byteview_of. unfold wz in E1, E2.
    replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    cbn [andb]. rewrite E1, E2. f_equal. apply Z_to_bv_small. change (bv_modulus 8) with 256. lia.
  Qed.

  Definition qavoids (r : Z * Z) : Prop := ltac2:(tb__ "0|1|
S1S1aVr;S38S0S0SaS49Z3M0A2G0A4A2S1S1aVr;S38S0S0S6S4aZ1cA2Z4A4A2S1aVr;S38S0S0S49S4cA4A2A2A2").

  Lemma win_None x : ltac2:(tb__ "0|0|
S4S1S7SaS49Z3A2Vx;A2S8Vx;S49A2A2A1S4S1S7S6S4aZ1cA2Vx;A2S8Vx;S6S4aZ20A2A2A2A1S2S3aS0A1S52Vx;A1S3dS0A1A3F_;F_;").
  Proof using .
    intros H1 H2. unfold qwin.
    destruct (gzp - 3 =? x) eqn:E3; [apply Z.eqb_eq in E3; lia|].
    destruct (gzp - 2 =? x) eqn:E2; [apply Z.eqb_eq in E2; lia|].
    destruct (gzp - 1 =? x) eqn:E1; [apply Z.eqb_eq in E1; lia|].
    destruct ((gzg + 28 <=? x) && (x <? gzg + 32))%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [Ea Eb]. apply Z.leb_le in Ea. apply Z.ltb_lt in Eb. lia.
  Qed.

  Lemma avoids_bytes lo w : ltac2:(tb__ "0|2|
S59S38S0S0Vlo;Vw;A4A1S8Z0Vlo;A2S8S6Vlo;Vw;A2M0S9Z2Z3fA2A2S0S1S7Vlo;R1A2S8R1G0A2A2S1S2S3aS0A1M1S4dR2A1S5aR2A1A3S2G1S5bR2A1S5cR2A1A3A2F_;Fx;F_;F_;F_;").
  Proof using V1.
    intros (D1 & D2 & D3) Hlo Hhi x Hx. unfold ranges_disjoint in D1, D2, D3. cbn [fst snd] in D1, D2, D3.
    apply BV1; [lia | unfold qblk; lia | apply win_None; lia].
  Qed.

  Lemma cell_transfer c : ltac2:(tb__ "0|2|
S18VL;S5aVc;A3S59S13VL;Vc;A2M0A1Sa2U0S32Vc;A1A2S8Z0S3eS0S0G0A3M1A2S8S6G1S3fS0S0G0A3A2S9Z2Z3fA2A2S18VL;S4dVc;A3F_;F_;F_;F_;F_;").
  Proof using V1.
    intros Hc Hav Hw Hlo Hhi. unfold cell_range in *. cbn [fst snd] in Hlo, Hhi.
    pose proof (avoids_bytes _ _ Hav Hlo Hhi) as B.
    unfold cell_holds in *. destruct (mc_val c).
    - intros j Hj. rewrite (proj1 (B (loc_addr L (mc_loc c) + Z.of_nat j) ltac:(lia))). exact (Hc j Hj).
    - intros j Hj. rewrite (proj1 (B (loc_addr L (mc_loc c) + Z.of_nat j) ltac:(lia))). exact (Hc j Hj).
    - destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm].
      rewrite (proj1 (B (loc_addr L (mc_loc c)) ltac:(lia))). exact Hb.
    - intros j Hj. rewrite (proj1 (B (loc_addr L (mc_loc c) + Z.of_nat j) ltac:(lia))). exact (Hc j Hj).
  Qed.

  Lemma image_cell_span c : ltac2:(tb__ "0|2|
S48S12Vc;S17Vs;A1A3S1S8Z0S3eS0S0S13VL;Vc;A2M0A3M1A2S8S6G1S3fS0S0G0A3A2S9Z2Z3fA2A2A2F_;").
  Proof using HMI.
    intros Hin. destruct (image_in_footprint s L c G_W G_L Hin) as (rg & Hrg & [I1 I2]).
    pose proof G_L as (_ & _ & _ & POS). destruct (POS rg Hrg) as [P1 P2].
    assert (0 <= snd (cell_range L c)) by (unfold cell_range; cbn; lia). lia.
  Qed.

  Lemma footer_cell_span c : ltac2:(tb__ "0|2|
S48S12Vc;S8dVs;A1A3S1S8Z0S3eS0S0S13VL;Vc;A2M0A3M1A2S8S6G1S3fS0S0G0A3A2S9Z2Z3fA2A2A2F_;").
  Proof using HMI.
    intros Hin. destruct (footer_in_footprint s L c G_W G_L Hin) as (rg & Hrg & [I1 I2]).
    pose proof G_L as (_ & _ & _ & POS). destruct (POS rg Hrg) as [P1 P2].
    assert (0 <= snd (cell_range L c)) by (unfold cell_range; cbn; lia). lia.
  Qed.

  Definition Cfreed' : mcell := ltac2:(tb__ "0|0|
S15S14S5fVg;S1fA2A1U4S16S6S61Vam;A1S67Vi;A1A2A1A3").
  Definition H3' : mcell := ltac2:(tb__ "0|0|
S15S14S5fS6aVam;Vi;A2N3A2A1U1S16ZffA1A3").
  Definition H16' : mcell := ltac2:(tb__ "0|0|
S15S14S5fS6aVam;Vi;A2N2A2A1U2S16Z0A1A3").

  Lemma image'_cases c : ltac2:(tb__ "0|0|
S48S12Vc;S17S4bA1A3S3S2S12Vc;S56A3S3S1S2S0S60Vfr;A1Z0A3S3S2S12Vc;S54A3S2S12Vc;S53A3A2A2S48S12Vc;S17Vs;A1A3A2A2F_;").
  Proof using FFx HMI Har.
    intros Hin. rewrite G_s' in Hin.
    destruct (upd_image_In s g am qam2 G_ND G_MT c Hin) as [Hold | [Hm | Hgr]].
    - right; right. exact Hold.
    -
      unfold meta_slot_cells in Hm. cbn in Hm.
      assert (OLD : forall c', In c' (meta_slot_cells g (Some (MUsed am))) -> In c' (image s)).
      { intros c' Hc'. exact (meta_cells_in_image s g am c' G_W G_u Hc'). }
      unfold meta_slot_cells in OLD.
      destruct Hm as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
      1,2,3,4,6: right; right; apply OLD; cbn; tauto.
      left. reflexivity.
    - unfold group_cells in Hgr. apply in_app_iff in Hgr as [Hh|Hsl].
      + right; right. apply (In_image_group s g am c G_um). unfold group_cells. apply in_app_iff. left. exact Hh.
      + apply in_flat_map in Hsl as [j [Hj Hc]]. apply In_zseq in Hj. change (am_last qam2) with (am_last am) in Hj.
        unfold slot_cells in Hc. unfold qam2 in Hc. rewrite (am2_nth_slot s g am i fr G_W FFx j) in Hc by lia.
        change (slot_start (am_post am i) j) with (slot_start am j) in Hc.
        destruct (j =? i) eqn:Eji.
        * apply Z.eqb_eq in Eji. subst j. cbn [ss_hdr ss_fr] in Hc. rewrite app_nil_r in Hc.
          apply in_app_iff in Hc as [Hc|Hc].
          -- right; right. destruct Hc as [<-|[]]. exact (proj1 (slot_start_cells s g am i G_W G_um G_i)).
          -- destruct (fr_off fr =? 0) eqn:E0.
             ++ apply Z.eqb_eq in E0. right; left. split; [exact E0|]. destruct Hc as [<-|[<-|[]]]; [left|right]; reflexivity.
             ++ right; right. pose proof (slot_start_cells s g am i G_W G_um G_i) as [_ SC].
                destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hc].
                destruct SC as [S1 S2]. destruct Hc as [<-|[<-|[]]]; assumption.
        * right; right. apply (In_image_group s g am c G_um). apply (In_group_slot g am j); [lia|]. exact Hc.
  Qed.

  Lemma Cfreed'_range : ltac2:(tb__ "0|0|
S2S39S0S0A2S13VL;S56A2S38S0S0S6S4aZ1cA2Z4A4A3").
  Proof using FFx HQ Har. unfold cell_range, Cfreed', gzg, addr_of, loc_addr, META_freed. destruct g; cbn [mc_loc mc_w padd]. f_equal; lia. Qed.

  Lemma H3'_range : ltac2:(tb__ "0|0|
S2S0S60Vfr;A1Z0A3S2S39S0S0A2S13VL;S54A2S38S0S0SaS49Z3A2Z1A4A3F_;").
  Proof using FFx HMI.
    intros E0. pose proof G_geom as (_ & _ & _ & _ & E1 & E2 & _). unfold cell_range, H3'. cbn [mc_loc mc_w].
    fold (addr_of L (padd (slot_start am i) (-3))). f_equal. rewrite E2, E0. unfold gst, addr_of, loc_addr. destruct (slot_start am i); cbn [padd]. lia.
  Qed.

  Lemma H16'_range : ltac2:(tb__ "0|1|
S2S0S60Vfr;A1Z0A3S2S39S0S0A2S13VL;S53A2S38S0S0SaS49Z2M0A2G0A4A3F_;").
  Proof using FFx HMI.
    intros E0. pose proof G_geom as (_ & _ & _ & _ & E1 & E2 & _). unfold cell_range, H16'. cbn [mc_loc mc_w].
    fold (addr_of L (padd (slot_start am i) (-2))). f_equal. rewrite E2, E0. unfold gst, addr_of, loc_addr. destruct (slot_start am i); cbn [padd]. lia.
  Qed.

  Lemma Cfreed'_in : In Cfreed' (image qs1).
  Proof using FFx HMI HQ.
    rewrite G_s'. apply (upd_image_meta s g qam2). { rewrite <- G_s'. exact G_W'. }
    unfold meta_slot_cells. cbn. do 4 right. left. reflexivity.
  Qed.

  Lemma H'_in : ltac2:(tb__ "0|1|
S2S0S60Vfr;A1Z0A3S1S48S12S54S17S4bA1M0A3S48S12S53G0A3A2F_;").
  Proof using FFx HMI.
    intros E0. rewrite G_s'.
    assert (K : forall c, In c (slot_cells qam2 i) -> In c (image (upd_meta g (MUsed qam2) s))).
    { intros c Hc. apply (upd_image_group s g am qam2 G_ND G_MT). apply (In_group_slot g qam2 i); [pose proof G_i; exact G_i | exact Hc]. }
    unfold slot_cells in K. unfold qam2 in K. rewrite (am2_nth_slot s g am i fr G_W FFx i) in K by (pose proof G_i; lia).
    rewrite Z.eqb_refl in K. replace (fr_off fr =? 0) with true in K by (symmetry; apply Z.eqb_eq; exact E0). cbn [ss_hdr ss_fr app] in K.
    split; apply K; cbn; auto.
  Qed.

  Lemma zone_covers : ltac2:(tb__ "0|4|
S39S0S0A2M0S3S1S2S0S3eS0S0R1A3M1SaS49Z3M2A2A3S2S0S3fS0S0R1A3M3G2A3A2S1S2S0G1S49A3S2S0G3S4cA3A2A2G0S1aR1Sa1VL;Vam;Vi;A3A2S1aR2R4A2F_;Fq;F_;Fr;").
  Proof using FFx HMI.
    intros r Hr q D. pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & E3 & EZ & _).
    rewrite EZ in D. unfold ranges_disjoint in *. cbn [fst snd] in D. unfold UNIT, IB in *.
    destruct Hr as [[-> ->]|[-> ->]]; lia.
  Qed.

  Lemma old_cell_avoids c : ltac2:(tb__ "0|0|
S48S12Vc;S17Vs;A1A3S48S12Vc;S17S4bA1A3S4S2S12Vc;S56A3A1S4S1S2S0S60Vfr;A1Z0A3S3S2S12Vc;S54A3S2S12Vc;S53A3A2A2A1S59S13VL;Vc;A2A1F_;F_;F_;F_;").
  Proof using FFx HMI HQ Har.
    intros Hin Hin' Hnf Hnh. pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & E3 & EZ & _).
    assert (DM : ranges_disjoint (cell_range L c) (gzg + 28, 4)).
    { destruct (pairwise_In_cases ranges_disjoint (cell_range L) (image qs1) c Cfreed' (image_cells_disjoint qs1 L G_W' G_L') Hin' Cfreed'_in) as [E|[D|D]].
      - exfalso. exact (Hnf E).
      - rewrite Cfreed'_range in D. exact D.
      - rewrite Cfreed'_range in D. apply ranges_disjoint_sym. exact D. }
    assert (DB : ranges_disjoint (cell_range L c) (gzp, gn)).
    { exact (image_outside_user_blocks s L c _ G_W G_L Hin G_blk). }

    assert (DZ : ranges_disjoint (cell_range L c) (zone_range L am i) -> qavoids (cell_range L c)).
    { intros D. split; [|split; [exact DM | exact DB]]. apply (zone_covers (gzp - 3, 3)); [left; split; reflexivity | exact D]. }
    destruct (zone_image_addr s L g am i G_W G_L G_u G_i ltac:(intros f Hf; rewrite G_sl in Hf; injection Hf as <-; exact G_kind) c Hin) as [Hown | D]; [|exact (DZ D)].

    assert (Hng' : forall f, ss_fr (nth_slot qam2 i) = Some f -> fr_kind f = FUser) by (intros f Hf; rewrite G_sl' in Hf; discriminate).
    destruct (zone_image_addr qs1 L g qam2 i G_W' G_L' G_u' G_i Hng' c Hin') as [Hown' | D'].
    2:{ apply DZ. change (zone_range L am i) with (zone_range L qam2 i). exact D'. }

    unfold own_hdr in Hown'. rewrite G_sl' in Hown'. rewrite app_nil_r in Hown'.
    unfold qam2 in Hown'. rewrite (am2_nth_slot s g am i fr G_W FFx i) in Hown' by (pose proof G_i; lia). rewrite Z.eqb_refl in Hown'.
    cbn [ss_hdr] in Hown'. change (slot_start (am_post am i) i) with (slot_start am i) in Hown'.
    destruct (fr_off fr =? 0) eqn:E0.
    { exfalso. apply Z.eqb_eq in E0. apply Hnh. split; [exact E0|]. destruct Hown' as [<-|[<-|[]]]; [left|right]; reflexivity. }
    apply Z.eqb_neq in E0.
    destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hown'].
    assert (LOC : fst (cell_range L c) = gst - 3 /\ snd (cell_range L c) = 1 \/ fst (cell_range L c) = gst - 2 /\ snd (cell_range L c) = 2).
    { unfold cell_range, gst, addr_of, loc_addr. destruct Hown' as [<-|[<-|[]]]; cbn [mc_loc mc_w fst snd]; destruct (slot_start am i); cbn [padd]; [left|right]; split; lia. }
    split; [|split; [exact DM | exact DB]].
    unfold ranges_disjoint. cbn [fst snd]. unfold UNIT in *. destruct LOC as [[-> ->]|[-> ->]]; left; lia.
  Qed.

  Lemma footer'_old c : ltac2:(tb__ "0|0|
S48S12Vc;S8dS4bA1A3S48S12Vc;S8dVs;A1A3F_;").
  Proof using FFx HMI.
    intros Hin. rewrite G_s' in Hin.
    destruct (upd_footer_In s g am qam2 G_ND G_MT c Hin) as [H|H]; [exact H|].
    unfold footer_cells. apply in_flat_map. exists (g, am). split; [exact G_um|]. cbn [snd].
    unfold group_footer_cells in *. destruct H as [<-|H]; [left; reflexivity|]. right.
    apply in_flat_map in H as [j [Hj H]]. apply In_zseq in Hj. change (am_last qam2) with (am_last am) in Hj.
    unfold qam2 in H. rewrite (am2_nth_slot s g am i fr G_W FFx j) in H by lia.
    destruct (j =? i) eqn:Eji; [destruct H|].
    apply in_flat_map. exists j. split; [apply In_zseq; lia|].
    destruct (ss_fr (nth_slot am j)) as [f|]; [|destruct H].

    exact H.
  Qed.

  Lemma footer_avoids c : ltac2:(tb__ "0|0|
S48S12Vc;S8dVs;A1A3S59S13VL;Vc;A2A1F_;").
  Proof using FFx HMI HQ Har.
    intros Hin. pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & E3 & EZ & Pm & Pe & (rg & Hrg & RI & Erg)).
    pose proof G_area_geom as (Eg & Pa & Pa2 & InA & (rga & Hra & Hka)).
    split; [|split].
    -
      destruct (zone_footer_addr s L g am i G_W G_L G_u G_i ltac:(intros f Hf; rewrite G_sl in Hf; injection Hf as <-; exact G_kind) c Hin) as [(f & Hf & Hc) | D].
      + rewrite G_sl in Hf. injection Hf as <-.
        pose proof (ff_n _ _ _ _ _ FFx) as Nn.
        assert (Hr : 0 <= reserved_of am fr) by (unfold reserved_of; pose proof (ff_fit _ _ _ _ _ FFx); lia).
        destruct (frame_footer_above_block am i fr c Sp Nn Hr Hc) as (d & E & Lo & Hi).
        unfold cell_range. rewrite E. unfold ranges_disjoint. cbn [fst snd]. right.
        unfold gzp, gp, addr_of in E2 |- *. unfold loc_addr. destruct (frame_ptr am i fr); cbn [padd]. cbn [loc_addr] in E2. lia.
      + apply (zone_covers (gzp - 3, 3)); [left; split; reflexivity | exact D].
    -
      destruct (In_footer_cells_inv s c Hin) as (g' & am' & Hg' & Hc).
      apply (used_metas_usedX s g' am' G_W) in Hg'.
      destruct (used_group_region [] None U0 s g' am' G_W Hg') as (rg' & Hr' & Hk' & Hl' & Ho' & Hext' & _).
      destruct (In_group_footer_cells [] None U0 s g' am' c G_W Hg' Hc) as (d & E & Hd & Hw & _).
      pose proof G_L as (_ & _ & PW & _).
      assert (Hne : (LMem (SP (prid (am_mem am')) 0), rg_len rg') <> (LMem a, PGSZ)).
      { intros X. injection X as Ea _. rewrite <- Ea in Hra. cbn [prid] in Hra. rewrite Hr' in Hra. injection Hra as <-. exact (Hka Hk'). }
      destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW (footprint_region_In s _ _ Hr' Hk' Hl') InA Hne) as [D|D];
        unfold crange, loc_addr, ranges_disjoint in D; cbn [fst snd] in D;
        unfold cell_range, ranges_disjoint; rewrite E; cbn [fst snd]; unfold loc_addr; destruct (am_mem am') as [r o]; cbn [padd prid poff] in *;
        unfold gza, addr_of, loc_addr in Eg; destruct a as [ra oa]; unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *; lia.
    - exact (footer_outside_user_blocks s L c _ G_W G_L Hin G_blk).
  Qed.

  Lemma lor_lt_pow2 x y nb : ltac2:(tb__ "0|3|
S1S7Z0M0Vx;A2S8Vx;S9Z2Vnb;A2M1A2A2S1S7G0Vy;A2S8Vy;G1A2A2S8G0Vnb;A2S1S7G0SdVx;Vy;A2M2A2S8G2G1A2A2F_;F_;F_;").
  Proof using .
    intros Ha Hb Hn. split; [apply Z.lor_nonneg; lia|].
    destruct (Z.eq_dec x 0) as [->|Za]; [rewrite Z.lor_0_l; lia|].
    destruct (Z.eq_dec y 0) as [->|Zb]; [rewrite Z.lor_0_r; lia|].
    assert (0 < Z.lor x y).
    { pose proof (Z.lor_nonneg x y). assert (Z.lor x y <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia). lia. }
    apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
  Qed.

  Lemma add_bit_nocarry m kk : ltac2:(tb__ "0|2|
S7Z0M0Vm;A2S7G0Vkk;A2S2S3cS10Vm;Vkk;A2S46A3S2S0S6Vm;S9Z2Vkk;A2M1A2SdVm;G1A2A3F_;F_;F_;").
  Proof using .
    intros Hm Hk Hb.
    assert (HL : Z.land m (2 ^ kk) = 0).
    { apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
      destruct (Z.eqb_spec kk j) as [<-|]; [rewrite Hb; reflexivity | apply Bool.andb_false_r]. }
    rewrite <- Z.lxor_lor by exact HL. apply Z.add_nocarry_lxor. exact HL.
  Qed.

  Lemma freed'_range : ltac2:(tb__ "0|1|
S1S7Z0S6S61Vam;A1S67Vi;A1A2M0A2S8G0S9Z2Z20A2A2A2").
  Proof using FFx.
    pose proof (ff_freed_nn _ _ _ _ _ FFx) as F. pose proof (ff_freed_i _ _ _ _ _ FFx) as Fi. pose proof G_i as Hi.
    pose proof (ff_last _ _ _ _ _ FFx) as Hl. unfold bit.
    rewrite (add_bit_nocarry (am_freed am) i) by (try lia; exact Fi).
    assert (0 <= 2 ^ i < 2 ^ 32) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    apply lor_lt_pow2; lia.
  Qed.

  Lemma W_sane : ltac2:(tb__ "0|4|
S1S8Z0M0SaS49Z4A2A2S1S7S6S49S4cA2S4eA2S1S8S6S4eS68A2M1S9Z2Z3fA2M2A2S1S8G0S4aA2S1S8S6S4aZ28A2M3G2A2S1S7S6S4fZ10A2S49A2S3S7G3S4fA2S7G1S4aA2A2A2A2A2A2A2A2").
  Proof using FFx HMI Har.
    pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & E3 & EZ & Pm & Pe & (rg & Hrg & RI & Erg)).
    pose proof G_area_geom as (Eg & Pa & Pa2 & InA & (rga & Hra & Hka)). destruct Har as (_ & Hk & _).
    pose proof G_i as Hi. assert (0 <= stride_of am * i /\ stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by (split; nia).
    unfold UNIT, IB, AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
    repeat (split; [lia|]).

    pose proof G_L as (_ & _ & PW & _).
    destruct (used_group_region [] None U0 s g am G_W G_u) as (rg0 & Hr0 & Hk0 & Hl0 & _).
    assert (Hne : rg <> (LMem a, 4096)).
    { intros ->. cbn [fst] in Erg. injection Erg as Ea. rewrite Ea in Hra. cbn [prid] in Hra. rewrite Hr0 in Hra. injection Hra as <-. exact (Hka Hk0). }
    destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW Hrg InA Hne) as [D|D];
      unfold gza, addr_of in Eg; destruct a as [ra oa];
      unfold crange, ranges_disjoint, range_incl in D, RI; cbn [fst snd] in D, RI; rewrite Erg in D, RI; unfold loc_addr in D, RI; destruct RI as [RI1 RI2];
      cbn [loc_addr] in Eg; unfold gzm, addr_of, loc_addr in *; destruct (am_mem am) as [rm om]; cbn [prid poff] in *;
      unfold group_extent, UNIT, IB in *; lia.
  Qed.

  Lemma new_cells_hold : ltac2:(tb__ "0|0|
S1S18VL;S4dS56A3S2S0S60Vfr;A1Z0A3S1S18VL;S4dS54A3S18VL;S4dS53A3A2F_;A2").
  Proof using FFx HMI HQ Har V3.
    pose proof W_sane as (S1 & S2 & S3 & S4 & S5 & S7 & S6). pose proof freed'_range as R.
    pose proof G_geom as (_ & _ & Hn & _). unfold IB in *.
    split.
    - unfold cell_holds, Cfreed'. cbn [mc_val mc_loc mc_w sval_num].
      pose proof (f_equal fst Cfreed'_range) as CR. unfold cell_range, Cfreed' in CR. cbn [mc_loc mc_w fst] in CR.
      rewrite CR. intros j Hj. apply BV3.
      + unfold IB in *. lia.
      + unfold le_byte. apply Z.mod_pos_bound. lia.
      + unfold qwin.
        destruct (gzp - 3 =? gzg + 28 + Z.of_nat j) eqn:X3; [apply Z.eqb_eq in X3; exfalso; unfold IB in *; lia|].
        destruct (gzp - 2 =? gzg + 28 + Z.of_nat j) eqn:X2; [apply Z.eqb_eq in X2; exfalso; unfold IB in *; lia|].
        destruct (gzp - 1 =? gzg + 28 + Z.of_nat j) eqn:X1; [apply Z.eqb_eq in X1; exfalso; unfold IB in *; lia|].
        replace ((gzg + 28 <=? gzg + 28 + Z.of_nat j) && (gzg + 28 + Z.of_nat j <? gzg + 32))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        f_equal. unfold bit. f_equal. lia.
    - intros E0. pose proof (f_equal fst (H3'_range E0)) as R3. pose proof (f_equal fst (H16'_range E0)) as R16.
      unfold cell_range, H3', H16' in R3, R16 |- *. cbn [mc_loc mc_w fst] in R3, R16.
      unfold cell_holds. cbn [mc_val mc_loc mc_w sval_num]. rewrite R3, R16. split.
      + intros j Hj. assert (j = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
        change (le_byte 255 1 0) with 255. apply BV3; [lia | lia |].
        unfold qwin. rewrite Z.eqb_refl. reflexivity.
      + intros j Hj.
        assert (EB : le_byte 0 2 j = 0) by (unfold le_byte; rewrite Z.mod_0_l, Z.shiftr_0_l by (cbn; lia); reflexivity).
        rewrite EB. apply BV3; [lia | lia |].
        unfold qwin.
        destruct (gzp - 3 =? gzp - 2 + Z.of_nat j) eqn:X3; [apply Z.eqb_eq in X3; lia|].
        assert (j = 0%nat \/ j = 1%nat) as [->| ->] by lia.
        * cbn [Z.of_nat]. rewrite Z.add_0_r, Z.eqb_refl. reflexivity.
        * replace (gzp - 2 + Z.of_nat 1) with (gzp - 1) by lia.
          destruct (gzp - 2 =? gzp - 1) eqn:X2; [apply Z.eqb_eq in X2; lia|]. rewrite Z.eqb_refl. reflexivity.
  Qed.

  Theorem reprP_post : ltac2:(tb__ "0|0|
S8eVL;S4bS4dA3").
  Proof using FFx HMI HQ Har V1 V2 V3.
    pose proof G_repr as [[HL0 [HI HR]] HF].
    split; [split; [exact G_L'|split]|].
    -
      apply Forall_forall. intros c Hin'.
      destruct (mcell_eq_dec c Cfreed') as [->|Hnf]; [exact (proj1 new_cells_hold)|].
      assert (DEC : {fr_off fr = 0 /\ (c = H3' \/ c = H16')} + {~ (fr_off fr = 0 /\ (c = H3' \/ c = H16'))}).
      { destruct (Z.eq_dec (fr_off fr) 0) as [E0|E0]; [|right; tauto].
        destruct (mcell_eq_dec c H3') as [->|N3]; [left; auto|].
        destruct (mcell_eq_dec c H16') as [->|N16]; [left; auto|]. right. intros [_ [E|E]]; [exact (N3 E) | exact (N16 E)]. }
      destruct DEC as [[E0 [-> | ->]] | Hnh].
      + exact (proj1 (proj2 new_cells_hold E0)).
      + exact (proj2 (proj2 new_cells_hold E0)).
      + destruct (image'_cases c Hin') as [E | [[E0 HE] | Hold]]; [exfalso; exact (Hnf E) | exfalso; exact (Hnh (conj E0 HE)) |].
        pose proof (image_cell_span c Hold) as [P1 P2].
        apply (cell_transfer c); [| apply (old_cell_avoids c Hold Hin' Hnf Hnh) | exact (image_cell_w s c Hold) | exact P1 | exact P2].
        exact (proj1 (Forall_forall _ _) HI c Hold).
    -
      intros x [(rg & Hrg & Hx) Hnu].
      destruct (free_blocks s gp gn [] qs1 G_W G_blk G_y) as (l1 & l2 & EB1 & EB2).
      rewrite G_s' in Hrg. change (footprint (upd_meta g (MUsed qam2) s)) with (footprint s) in Hrg.
      assert (M0 : ~ qblk x -> qbv0 x <> None).
      { intros Hnb. apply HR. split; [exists rg; split; [exact Hrg | exact Hx]|].
        intros (b & Hb & Hxb). rewrite EB1 in Hb. apply in_app_iff in Hb.
        assert (Hb' : In b (l1 ++ l2) \/ b = (gp, gn)).
        { destruct Hb as [Hb|[Hb|Hb]]; [left; apply in_app_iff; left; exact Hb | right; symmetry; exact Hb | left; apply in_app_iff; right; exact Hb]. }
        destruct Hb' as [Hb' | ->].
        - apply Hnu. exists b. rewrite EB2. split; [exact Hb' | exact Hxb].
        - apply Hnb. unfold qblk, gzp, addr_of. cbn [fst snd] in Hxb. exact Hxb. }
      pose proof G_L as (_ & _ & _ & POS). destruct (POS rg Hrg) as [Q1 Q2]. unfold crange in Q1, Q2. cbn [fst snd] in Q1, Q2.
      destruct (Z_le_dec gzp x) as [A|A]; [destruct (Z_lt_dec x (gzp + gn)) as [B|B]|].
      + apply BV2; [lia | unfold qblk; lia].
      + destruct (qwin x) as [b|] eqn:Ew.
        * assert (Hb : 0 <= b < 256).
          { unfold qwin in Ew. repeat (destruct (_ =? x) in Ew; [injection Ew as <-; lia|]).
            destruct ((gzg + 28 <=? x) && (x <? gzg + 32))%bool; [|discriminate]. injection Ew as <-. unfold le_byte. apply Z.mod_pos_bound. lia. }
          rewrite (BV3 x b ltac:(lia) Hb Ew). discriminate.
        * rewrite (proj1 (BV1 x ltac:(lia) ltac:(unfold qblk; lia) Ew)). apply M0. unfold qblk; lia.
      + destruct (qwin x) as [b|] eqn:Ew.
        * assert (Hb : 0 <= b < 256).
          { unfold qwin in Ew. repeat (destruct (_ =? x) in Ew; [injection Ew as <-; lia|]).
            destruct ((gzg + 28 <=? x) && (x <? gzg + 32))%bool; [|discriminate]. injection Ew as <-. unfold le_byte. apply Z.mod_pos_bound. lia. }
          rewrite (BV3 x b ltac:(lia) Hb Ew). discriminate.
        * rewrite (proj1 (BV1 x ltac:(lia) ltac:(unfold qblk; lia) Ew)). apply M0. unfold qblk; lia.
    -
      apply Forall_forall. intros c Hin'. pose proof (footer'_old c Hin') as Hin.
      pose proof (footer_cell_span c Hin) as [P1 P2].
      apply (cell_transfer c); [| apply (footer_avoids c Hin) | exact (footer_cells_w s c Hin) | exact P1 | exact P2].
      exact (proj1 (Forall_forall _ _) HF c Hin).
  Qed.

  Lemma W_place : ltac2:(tb__ "0|6|
S5S0S0S5S0S0S5S0S0S1S7S6R3Z10A2S49A2S1S7Z0S4cA2S1S7S6S49S4cA2S4eA2S1S7S6S4eZ4A2S6R3R2A2M0A2S1S3S7G0S93VC;A1M1A2S7S92VC;A1M2R3A2A2S1S7R1S4aA2S1S7S6S4aZ28A2S6R1Z1000M3A2M4A2S1S3S7G4G1A2S7G2R1A2A2S1S7G3R3A2S1S7G3R1A2S1S7G0S95VL;A1M5A2S1S7G4G5A2S8G5S9Z2Z3fA2A2A2A2A2A2A2A2A2A2A2A2A2A2LA;A2Llen;A2LR;A2").
  Proof using FFx HMI Har.
    pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & E3 & EZ & Pm & Pe & (rg & Hrg & [RI1 RI2] & Erg)).
    pose proof G_area_geom as (Eg & Pa & Pa2 & InA & _). destruct Har as (_ & Hk & _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 HMI))))) as HV. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMI)))))))) as HLG.
    cbn [ma_s ma_L] in HV, HLG.
    destruct rg as [lc len]. cbn [fst] in Erg. subst lc.
    unfold crange, loc_addr in RI1, RI2. cbn [fst snd] in RI1, RI2.
    pose proof (extent_pos _ _ _ _ _ (inv_groups G_W g am G_u)) as EP.
    assert (Hlen : 0 <= len) by (unfold IB in RI2; lia).
    pose proof (fp_mem_range C L s vm _ _ HV HLG Hrg Hlen) as (M1 & M2 & M3).
    pose proof (fp_mem_range C L s vm _ _ HV HLG InA ltac:(unfold PGSZ; lia)) as (A1 & A2 & A3).
    unfold addr_of, loc_addr in M1, M2, M3, A1, A2, A3.
    unfold gza, addr_of, loc_addr in Eg, Pa.
    exists (ly_reg L (prid (am_mem am)) + 0), len, (match a with SP r o => ly_reg L r + o end).
    pose proof G_i as Hi.
    assert (X1 : stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia.
    assert (X2 : 0 <= stride_of am * i) by nia.
    assert (X3 : gze <= gzm + group_extent am) by (unfold group_extent, UNIT, IB in *; lia).
    clear X1 X2 EZ.
    unfold UNIT, IB, PGSZ, AREA_HDR, META_SIZE, METAS_PER_AREA in *.
    top_ranges.
    repeat split; lia.
  Qed.

  Lemma written_not_static x lo n0 : ltac2:(tb__ "0|1|
S1S7S93VC;A1Vlo;A2S7S6Vlo;Vn0;A2M0S92VC;A1A2A2S1S7Vlo;Vx;A2S8Vx;G0A2A2S1S1S7Z0Vx;A2S8Vx;S9Z2Z40A2A2A2S1S4S51Vx;A1A1S2S3aS0A1S52Vx;A1S3dS0A1A3A2A2F_;F_;").
  Proof using FFx HMI HS Har.
    intros Hlo Hx. pose proof HS as HS0. unfold statics_in_image in HS0. cbn zeta in HS0.
    destruct HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpg & Hceil).
    destruct W_place as (R & len & A & P1 & P0 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    unfold qblk. unfold PGSZ, UNIT in Hpg, Hceil.
    split; [lia|]. split; [lia|]. apply win_None; lia.
  Qed.

  Lemma statics_post : ltac2:(tb__ "0|0|
S94VC;S5bS4dA3").
  Proof using FFx HMI HS Har V1.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HMI)))))) as ST. cbn [ma_s ma_L] in ST. fold qrv0 qbv0 in ST.
    pose proof HS as HS0. unfold statics_in_image in HS0. cbn zeta in HS0.
    destruct HS0 as (Ilibc & Irep & Isc & Ismall & Imed & Ictz & Igot & Iguard & Ilock & Ictx & Ierr & Hpg & Hceil).
    assert (RV : forall lo n0, mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> forall x, lo <= x < lo + n0 -> qrv1 x = qrv0 x /\ qbv1 x = qbv0 x).
    { intros lo n0 Hlo x Hx. destruct (written_not_static x lo n0 Hlo Hx) as (X1 & X2 & X3).
      destruct (BV1 x X1 X2 X3) as [B R]. auto. }
    assert (HR : forall a0 w z lo n0, holds qrv0 a0 w z -> mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> lo <= a0 -> a0 + Z.of_nat w <= lo + n0 -> holds qrv1 a0 w z).
    { intros a0 w z lo n0 Hh Hlo Ha Hw j Hj. rewrite (proj1 (RV lo n0 Hlo (a0 + Z.of_nat j) ltac:(lia))). exact (Hh j Hj). }
    assert (HB : forall a0 w z lo n0, holds qbv0 a0 w z -> mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> lo <= a0 -> a0 + Z.of_nat w <= lo + n0 -> holds qbv1 a0 w z).
    { intros a0 w z lo n0 Hh Hlo Ha Hw j Hj. rewrite (proj2 (RV lo n0 Hlo (a0 + Z.of_nat j) ltac:(lia))). exact (Hh j Hj). }
    destruct ST as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & (gd & T9 & T10)).
    unfold mc_need_locks, mc_page_size in *.
    split; [apply (HR _ _ _ _ _ T1 Ilibc); cbn; lia|].
    split; [apply (HR _ _ _ _ _ T2 Ilibc); cbn; lia|].
    split; [apply (HR _ _ _ _ _ T3 Irep); cbn; lia|].
    split; [apply (HB _ _ _ _ _ T4 Ilock); cbn; lia|].
    split; [intros j Hj; rewrite (proj1 (RV _ _ Isc (mc_size_classes C + Z.of_nat j) ltac:(lia))); exact (T5 j Hj)|].
    split; [intros j Hj; rewrite (proj1 (RV _ _ Ismall (mc_small_cnt_tab C + Z.of_nat j) ltac:(lia))); exact (T6 j Hj)|].
    split; [intros j Hj; rewrite (proj1 (RV _ _ Imed (mc_med_cnt_tab C + Z.of_nat j) ltac:(lia))); exact (T7 j Hj)|].
    split; [intros j Hj; rewrite (proj1 (RV _ _ Ictz (mc_ctz_tab C + Z.of_nat j) ltac:(lia))); exact (T8 j Hj)|].
    exists gd. split.
    - apply (HR _ _ _ _ _ T9 Igot); cbn; lia.
    -
      apply (HR _ _ _ _ _ T10 Iguard); cbn; lia.
  Qed.

  Theorem minv_post : ltac2:(tb__ "0|0|
S9fVC;Sa0S4bVL;A2Vrd1;Vwok1;Vvm;A5").
  Proof using FFx HMI HQ HS Har V1 V2 V3.
    pose proof HMI as (_ & HB & HC & _ & HV & _ & HA & HLG & HIMG & HMW & HRCH). cbn [ma_s ma_L] in HB, HC, HV, HA, HLG, HRCH.
    split; [exact G_W'|]. split; [rewrite G_s'; exact HB|]. split; [exact HC|].
    split; [exact reprP_post|]. split; [rewrite G_s'; exact HV|]. split; [exact statics_post|].
    split; [|split; [exact HLG|]; split; [exact HIMG|]; split; [exact HMW|];
              rewrite G_s'; apply (reach_ok_upd s g am qam2 G_MT); [reflexivity | cbn; lia | exact HRCH]].
    cbn [ma_s]. rewrite G_s'. change (st_init_done (upd_meta g (MUsed qam2) s)) with (st_init_done s).
    intros Hf. pose proof (ff_init _ _ _ _ _ FFx) as Ht. rewrite Ht in Hf. discriminate.
  Qed.

  Lemma cell_owned c x : ltac2:(tb__ "0|2|
S3S48S12Vc;S17Vs;A1A3S48S12Vc;S8dVs;A1A3A2S1S7S3eS0S0S13VL;Vc;A2M0A3M1Vx;A2S8Vx;S6G1S3fS0S0G0A3A2A2A2S1bVL;Vs;Vx;A3F_;F_;").
  Proof using HMI.
    intros Hc Hx. split.
    - destruct Hc as [Hc|Hc].
      + destruct (image_in_footprint s L c G_W G_L Hc) as (rg & Hrg & [I1 I2]). exists rg. split; [exact Hrg|]. unfold crange in I1, I2. cbn [fst snd] in I1, I2. lia.
      + destruct (footer_in_footprint s L c G_W G_L Hc) as (rg & Hrg & [I1 I2]). exists rg. split; [exact Hrg|]. unfold crange in I1, I2. cbn [fst snd] in I1, I2. lia.
    - intros (b & Hb & Hxb).
      assert (D : ranges_disjoint (cell_range L c) (block_range L b)).
      { destruct Hc as [Hc|Hc]; [exact (image_outside_user_blocks s L c b G_W G_L Hc Hb) | exact (footer_outside_user_blocks s L c b G_W G_L Hc Hb)]. }
      unfold ranges_disjoint, block_range in D. cbn [fst snd] in D. lia.
  Qed.

  Lemma window_cells : ltac2:(tb__ "0|b|
S15S14S5fS55N4A2A1U1M0S16Z0A1M1A3S12S15S14S5fS55N3A2A1G0S16S25Vam;Vi;Vfr;A3A1A3S12S15S14S5fS55N2A2A1U2S16S26Vam;Vi;Vfr;A3A1A3S12S15S14S69Vam;A1M2A1U8M3S21Vg;A1A3S12S15S14S5fVg;S2eA2A1G3S21G2A1A3S12S15S14S5fVg;S2cA2A1U4M4S16S6bVam;A1A1A3S12S15S14S5fVg;S1fA2A1G4S16S61Vam;A1A1A3S12S15S14S5fVg;S2dA2A1G3S16S1eVam;A1A1A3S12S15S14Va;A1G3S22A3S12S15S2bS2aA1G3S3cS35L_;S8bVs;A1S22G1X3cx2A3S12S15S14S8fVam;Vi;A2A1G0G1A3S12S1S48S12RbS17Vs;A1M5A3S1S48S12RaG5A3S1S48S12R9G5A3S1S48S12R8G5A3S1S48S12R7G5A3S1S48S12R6G5A3S1S48S12R5G5A3S1S48S12R4G5A3S1S48S12R3G5A3S1S48S12R2G5A3S1S3S48S12R1G5A3S48S12R1S8dVs;A1A3A2S1S2S39S0S0A2M6S13VL;RbA2S38S0S0SaS49Z4M7A2Z1M8A4A3S1S2G6S13VL;RaA2S38S0S0SaS49Z3A2G8A4A3S1S2G6S13VL;R9A2S38S0S0SaS49Z2M9A2G9A4A3S1S2G6S13VL;R8A2S38S0S0S4fZ8MaA4A3S1S2G6S13VL;R7A2S38S0S0S6S4aZ10A2GaA4A3S1S2G6S13VL;R6A2S38S0S0S6S4aZ18A2G7A4A3S1S2G6S13VL;R5A2S38S0S0S6S4aZ1cA2G7A4A3S1S2G6S13VL;R4A2S38S0S0S6S4aZ20A2GaA4A3S1S2G6S13VL;R3A2S38S0S0S50GaA4A3S1S2G6S13VL;R2A2S38S0S0S27VL;A1GaA4A3S2G6S13VL;R1A2S38S0S0S4eG8A4A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2TCE;TCX;TCA;TC8;TC7;TC6;TC5;TC4;TC3;TC2;TC1;").
  Proof using FFx HMI HQ Har.
    pose proof (quick_cells s g am i fr G_W G_fr G_kind) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _ & QE & _).
    cbn zeta. destruct Har as (Ha & Hk & Eg).
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - unfold image. apply in_app_iff. right. apply in_app_iff. left.
      apply (In_areas_cells_intro s (st_areas s) a _ Ha). intros next. unfold area_cells. apply in_app_iff. left. left. reflexivity.
    - unfold image. apply in_app_iff. left. unfold ctx_cells. left. reflexivity.
    - unfold cell_range, gzp, gp, addr_of, loc_addr. cbn [mc_loc mc_w]. destruct (frame_ptr am i fr); cbn [padd]. f_equal; lia.
    - unfold cell_range, gzp, gp, addr_of, loc_addr. cbn [mc_loc mc_w]. destruct (frame_ptr am i fr); cbn [padd]. f_equal; lia.
    - unfold cell_range, gzp, gp, addr_of, loc_addr. cbn [mc_loc mc_w]. destruct (frame_ptr am i fr); cbn [padd]. f_equal; lia.
    - unfold cell_range, gzm, addr_of. cbn [mc_loc mc_w]. reflexivity.
    - unfold cell_range, gzg, addr_of, loc_addr, META_mem. cbn [mc_loc mc_w]. destruct g; cbn [padd]. f_equal; lia.
    - unfold cell_range, gzg, addr_of, loc_addr, META_avail. cbn [mc_loc mc_w]. destruct g; cbn [padd]. f_equal; lia.
    - unfold cell_range, gzg, addr_of, loc_addr, META_freed. cbn [mc_loc mc_w]. destruct g; cbn [padd]. f_equal; lia.
    - unfold cell_range, gzg, addr_of, loc_addr, META_bits. cbn [mc_loc mc_w]. destruct g; cbn [padd]. f_equal; lia.
    - unfold cell_range, gza, addr_of. cbn [mc_loc mc_w]. reflexivity.
    - unfold cell_range, loc_addr, CTX_secret. cbn [mc_loc mc_w]. f_equal; lia.
    - unfold cell_range, gze, addr_of. cbn [mc_loc mc_w]. reflexivity.
  Qed.

  Theorem windows_owned x : ltac2:(tb__ "0|2|
S3S1S7SaS49Z4A2Vx;A2S8Vx;S49A2A2S3S1S7S4fVx;A2S8Vx;S6S4fZ8M0A2A2A2S3S1S7S6S4aZ10A2Vx;A2S8Vx;S6S4aZ28A2A2A2S3S1S7S50Vx;A2S8Vx;S6S50G0A2A2A2S3S1S7S27VL;A1M1Vx;A2S8Vx;S6G1G0A2A2A2S1S7S6S49S4cA2Vx;A2S8Vx;S6S4eZ1A2A2A2A2A2A2A2A2S1bVL;Vs;Vx;A3F_;").
  Proof using FFx HMI HQ Har.
    intros Hx.
    pose proof window_cells as W. cbn zeta in W.
    destruct W as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & QA & QX & QE & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & RA & RX & RE).
    assert (OWN : forall c, In c (image s) -> fst (cell_range L c) <= x < fst (cell_range L c) + snd (cell_range L c) -> alloc_owned L s x).
    { intros c Hc. apply cell_owned. left. exact Hc. }
    Ltac own OWN H R := apply (OWN _ H); rewrite R; cbn [fst snd]; lia.
    destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
    - assert (x = gzp - 4 \/ x = gzp - 3 \/ gzp - 2 <= x < gzp) as [X|[X|X]] by lia.
      + own OWN Q1 R1. + own OWN Q2 R2. + own OWN Q3 R3.
    - own OWN Q4 R4.
    - assert (gzg + 16 <= x < gzg + 24 \/ gzg + 24 <= x < gzg + 28 \/ gzg + 28 <= x < gzg + 32 \/ gzg + 32 <= x < gzg + 40) as [X|[X|[X|X]]] by lia.
      + own OWN Q5 R5. + own OWN Q6 R6. + own OWN Q7 R7. + own OWN Q8 R8.
    - own OWN QA RA.
    - own OWN QX RX.
    - destruct (Z.eq_dec x gze) as [->|Hne].
      + apply (cell_owned _ _ QE). rewrite RE. cbn [fst snd]. lia.
      +
        pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & E3 & EZ & Pm & Pe & (rg & Hrg & [RI1 RI2] & Erg)).
        split.
        * exists rg. split; [exact Hrg|]. unfold crange in RI1, RI2. cbn [fst snd] in RI1, RI2.
          pose proof G_i. assert (stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia.
          assert (0 <= stride_of am * i) by nia. unfold group_extent, UNIT, IB in *. lia.
        * intros ([q m] & Hb & Hxb). cbn [fst snd] in Hxb.
          destruct (zone_block_addr s L g am i G_W G_L G_u G_i ltac:(intros f Hf; rewrite G_sl in Hf; injection Hf as <-; exact G_kind) q m Hb) as [(f & Hf & -> & ->) | D].
          -- rewrite G_sl in Hf. injection Hf as <-. fold gp in Hxb. change (loc_addr L (LMem gp)) with gzp in Hxb. unfold gn in Hx. lia.
          -- rewrite EZ in D. unfold ranges_disjoint, block_range in D. cbn [fst snd] in D. unfold UNIT, IB in *. lia.
  Qed.

  Theorem block_owned' x : ltac2:(tb__ "0|0|
S51Vx;A1S1bVL;S4bVx;A3F_;").
  Proof using FFx HMI HQ.
    intros Hx. unfold qblk in Hx. rewrite G_s'. split.
    - change (footprint (upd_meta g (MUsed qam2) s)) with (footprint s).
      pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & E3 & EZ & Pm & Pe & (rg & Hrg & [RI1 RI2] & Erg)).
      exists rg. split; [exact Hrg|]. unfold crange in RI1, RI2. cbn [fst snd] in RI1, RI2.
      pose proof G_i. assert (stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia.
      assert (0 <= stride_of am * i) by nia. unfold group_extent, UNIT, IB in *. lia.
    - intros (b & Hb & Hxb). rewrite <- G_s' in Hb.
      destruct (free_blocks s gp gn [] qs1 G_W G_blk G_y) as (l1 & l2 & E1 & E2).
      pose proof (user_blocks_disjoint s L G_W G_L) as PW. rewrite E1, map_app in PW. cbn [map] in PW.
      rewrite E2 in Hb.
      destruct (pairwise_app_mid ranges_disjoint _ _ _ (block_range L b) PW ltac:(rewrite <- map_app; apply in_map; exact Hb)) as [D|D];
        unfold ranges_disjoint, block_range in D; cbn [fst snd] in D; fold gzp in D; unfold gzp, gp, addr_of in *; lia.
  Qed.
End Gap.
