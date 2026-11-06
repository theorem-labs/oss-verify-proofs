(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "padd"; "ameta"; "IB"; "frame"; "mslot"; "nth_slot"; "UNIT"; "MUsed"; "kreq"; "FUser"; "am_avail"; "am_last"; "region"; "slot_start"; "MMAP_THRESHOLD"; "NEST_FUEL"; "alloc_slot"; "am_mem"; "bind"; "malloc"; "slotst"; "ss_fr"; "ss_hdr"; "AREA_HDR"; "PGSZ"; "fkind"; "fr_kind"; "mkSlot"; "prid"; "ret"; "st_active"; "stride_of"; "KJunk"; "M"; "METAS_PER_AREA"; "META_SIZE"; "RkMap"; "SP"; "am_freed"; "am_next"; "am_prev"; "am_sc"; "am_set_avail"; "am_slots"; "ctz32"; "enframe"; "get"; "getm"; "lowbit"; "mkFrame"; "rg_kind"; "rkind"; "setm"; "st_areas"; "st_mmap_counter"; "upd_slot"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "pow"; "mul"; "eqb"; "to_nat"; "div"; "land"; "of_nat"; "leb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LMem"; "MCell"; "VZ"; "yields"; "cell_range"; "image"; "loc"; "mc_w"; "MT"; "cell_holds"; "footprint"; "user_blocks"; "U0"; "loc_addr"; "mc_loc"; "mc_val"; "usedX"; "Inv"; "VLo5"; "optr"; "sval"; "used_metas"; "META_avail"; "META_bits"; "META_freed"; "META_mem"; "META_next"; "META_prev"; "VP"; "WF"; "active_hd"; "alloc_owned"; "crange"; "fold_off"; "group_extent"; "group_ok"; "hdr_byte3"; "hdr_off16"; "keys_ok"; "le_byte"; "meta_bits"; "meta_slot_cells"; "range_incl"; "ranges_disjoint"; "region_of"; "sval_num"; "@Corelib.Init.Datatypes"; "prod"; "option"; "Some"; "pair"; "bool"; "nil"; "list"; "app"; "cons"; "None"; "fst"; "snd"; "nat"; "true"; "unit"; "length"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost.Gap"; "f_s'"; "f_am2"; "f_bv1"; "f_st"; "f_e"; "f_newcells"; "f_fr"; "f_off"; "in_zone"; "f_avoids"; "f_bv0"; "f_rv1"; "f_zm"; "f_footcells"; "f_frcells"; "f_hdrcells"; "f_rv0"; "f_p"; "f_zg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost"; "ms_ptr"; "as_ok_facts"; "ms_hdr"; "ms_post"; "ms_trace"; "ms_off"; "ms_slack"; "ms_stride"; "ms_am2"; "ms_frame"; "ms_off0"; "slow_case"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "wz"; "mc_img_hi"; "mc_img_lo"; "statics_ok"; "topL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "malloc_class"; "loop_case"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "reprO"; "frame_footer_cells"; "slot_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost.Post"; "ms_off"; "ms_slack"; "ms_stride"; "ms_ctr"; "ms_am2"; "ms_frame"; "ms_hdr"; "ms_off0"; "ms_reserved"; "ms_rsv"; "@Corelib.Init.Peano"; "lt"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MInv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones"; "zone_range"; "own_hdr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfSurgery MallocWfGeom MallocWfRepr MallocWfMain
  MallocWfSlot MallocWfMalloc MallocWfGroup MallocWfArith MallocLayout MallocFooter MallocFooterLemmas NestTier MallocIface MallocLaws
  MallocCallocLemmas FreeQuickModel Zones ImageUpd FpLaws MallocFastPost TryAvailPost MallocIfaceI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Definition slow_case (s : astate) (n : Z) : Prop := ltac2:(tb__ "0|2|
S1S1S40Z0M0Vn;A2S42Vn;S16A2A2S6S9S2S7dS6A1M1Sc5G1S47Sb2Vs;Vn;A2A1S26Vs;A1S85S6A1A4S7eS6R2A2A3S2S7dScA1S56Vs;R3A2S7eScSfR2A1A2A3S2S0S12R3A1G0A3F_;F_;Fam;Fg;A2").

Lemma loop_or_slow s n : ltac2:(tb__ "0|0|
S1S40Z0Vn;A2S42Vn;S16A2A2S6bVs;A1S5S3S6S6S3S9S9Sb3Vs;Vn;R2R1A4Lam;A2Lg;A2SabVs;Vn;A2A2F_;F_;").
Proof.
  intros Hn HW.
  destruct (nth (Z.to_nat (malloc_class s n)) (st_active s) None) as [g|] eqn:Eg.
  - pose proof (malloc_class_range s n Hn) as [R1 _].
    destruct (head_used [] None U0 s (malloc_class s n) g HW R1 Eg) as (am & Hu & _).
    pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
    destruct (Z.eq_dec (am_avail am) 0) as [E|NE].
    + right. split; [exact Hn|]. intros g' am' Eg' M'. rewrite Eg in Eg'. injection Eg' as <-.
      rewrite Mg in M'. injection M' as <-. exact E.
    + left. exists g, am. split; [exact Hn|]. split; [exact Eg|]. split; [exact Mg | exact NE].
  - right. split; [exact Hn|]. intros g' am' Eg' _. rewrite Eg in Eg'. discriminate.
Qed.

Section Post.
  Variables (s : astate) (n : Z) (g : sptr) (am : ameta) (idx : Z).

  Definition ms_stride : Z := stride_of am.
  Definition ms_slack : Z := ltac2:(tb__ "0|0|
S48S43S43SbaSaA2Vn;A2SeA2").
  Definition ms_ctr : Z := st_mmap_counter s.
  Definition ms_off0 (z : Z) : Z := ltac2:(tb__ "0|3|
S80S0L_;M0S46Sb9Z0M1A2G1S7dS7cS0S0A2M2A1S0Lx;S1eSdVam;Vidx;A2A1G2G2S0Lp;R1S0S0S49G0S46R2G1A2SbbS41R1Z1A2X80x2ZffA2Lh16;Lh3;X7cx1Lp;S4cVz;Z100A2X7dx2X80x2").
  Definition ms_off (z : Z) : Z := ltac2:(tb__ "0|0|
S6fSb9SbfVz;A1A2").
  Definition ms_reserved (z : Z) : Z := ltac2:(tb__ "0|0|
S43S43S43SbaSaA2S45SeSb8Vz;A1A2A2Vn;A2").
  Definition ms_rsv (z : Z) : Z := ltac2:(tb__ "0|2|
S80S0L_;S4bZ5M0Sc0Vz;A1M1A2G0G1X80x2").
  Definition ms_hdr (z : Z) : Z * Z := ltac2:(tb__ "0|1|
S80S7cS0S0A2L_;S46Sb8Vz;A1M0Z0A2S7fS0S0S41Vidx;S45Sc1Vz;A1Z20A2A2S48S45SbaVidx;A2SeA2A4S7fS0S0Ze0G0A4X80x2").
  Definition ms_frame (z : Z) : frame := ltac2:(tb__ "0|0|
S39Sb8Vz;A1Vn;S11A3").
  Definition ms_am2 (z : Z) : ameta := ltac2:(tb__ "0|0|
S3fVam;Vidx;S23S7eS7cS0S0A2SbeVz;A1A2S7eSbSbdVz;A1A2A2A3").
  Definition ms_post (z : Z) : astate := ltac2:(tb__ "0|0|
Sc9Vg;SfSbcVz;A1A1Vs;A3").
  Definition ms_ptr (z : Z) : sptr := ltac2:(tb__ "0|0|
S8S15Vam;Vidx;A2S45SeSb8Vz;A1A2A2").
  Definition ms_trace (z : Z) : list (kreq * Z) := ltac2:(tb__ "0|4|
S80S82S7cS10S0A2M0A1M1L_;S46Sb9Z0A2S81G0A1M2S7dS7cS0S0A2M3A1G1Lx;S1eSdVam;Vidx;A2A1G3G2Lp;S84G0S7fS10S0S28S49SbbZffA2A1Vz;A4G2A3X7dx2X80x2").
End Post.

Definition as_ok_facts (s : astate) (sc n : Z) (g : sptr) (am : ameta) (idx : Z) : Prop := ltac2:(tb__ "0|1|
S1S5fS81S6A1M0S7eS7cS6S0A2S7fS6S0Vg;Vidx;A4A2S5aVs;A4S1S2S7dS6A1S6cVs;Vsc;A2S7eS6Vg;A2A3S1S5eG0Vs;Vg;Vam;A4S1S2S0S31Vam;A1Vsc;A3S1S40S41Vn;SaA2S27Vam;A1A2S1S40Z0Vidx;A2S40Vidx;S13Vam;A1A2A2A2A2A2A2A2").

Section Yields.
  Variables (s : astate) (sc n : Z) (g : sptr) (am : ameta) (idx : Z).
  Hypothesis HF : ltac2:(tb__ "0|0|
Sa1Vs;Vsc;Vn;Vg;Vam;Vidx;A6").

  Lemma msy_slack : ltac2:(tb__ "0|0|
S40Z0Sa6Vn;Vam;A2A2").
  Proof using HF. destruct HF as (_ & _ & _ & _ & Fit & _). unfold ms_slack. apply Z.div_pos; [|unfold UNIT; lia]. unfold ms_stride, IB in *. lia. Qed.

  Lemma msy_off0 z : ltac2:(tb__ "0|1|
S1S40Z0SaaVs;Vn;Vam;Vidx;Vz;A5M0A2S42G0Z100A2A2").
  Proof using .
    unfold ms_off0. destruct (ms_slack n am =? 0); [lia|]. destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|].
    - pose proof (land255_range (if h3 =? 0 then ms_ctr s else h16 + 1)). lia.
    - pose proof (mod256_range z). lia.
  Qed.

  Lemma msy_off z : ltac2:(tb__ "0|1|
S1S1S40Z0Sa5Vs;Vn;Vam;Vidx;Vz;A5M0A2S40G0Sa6Vn;Vam;A2A2A2S40G0ZffA2A2").
  Proof using HF.
    pose proof (fold_off_ok (ms_slack n am) (ms_off0 s n am idx z) msy_slack (msy_off0 z)) as H1.
    pose proof (fold_off_le (ms_slack n am) (ms_off0 s n am idx z) ltac:(pose proof (msy_off0 z); lia) msy_slack) as H2.
    pose proof (msy_off0 z). unfold ms_off. lia.
  Qed.

  Theorem enframe_slow_yields : ltac2:(tb__ "0|0|
S0S1S40Z0R1A2S42R1Z100A2A2S51S7cS6S7A2S35Vg;Vidx;Vn;S3eVs;A1S11Vs;A6Sa4Vs;Vn;Vam;Vidx;R2A5S7fS6S7Sa0Vs;Vn;Vam;Vidx;R2A5Sa3Vs;Vn;Vg;Vam;Vidx;R2A6A4A4F_;Fz;").
  Proof using HF.
    intros z Hz. destruct HF as (_ & Hhd & Hu & Hsc' & Fit & Hidx).
    pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
    unfold enframe.
    eapply yields_bind0; [apply yields_getm; exact Mg|].
    unfold mcheck. replace ((0 <=? idx) && (idx <=? am_last am))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    eapply yields_bind0; [apply yields_ret|].
    fold (ms_stride am). change ((ms_stride am - IB - n) / UNIT) with (ms_slack n am). fold (ms_ctr s).
    eapply (yields_bind1 _ _ _ (ms_trace s n am idx z) (ms_off0 s n am idx z)).
    { unfold ms_trace, ms_off0. destruct (ms_slack n am =? 0); [apply yields_ret|].
      destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|]; [apply yields_ret|].
      cbn. split; [reflexivity|]. split; [exact Hz|]. reflexivity. }
    match goal with |- yields ((massert (?o <=? _) _ ;; _) _) _ _ => change o with (fold_off (ms_slack n am) (ms_off0 s n am idx z)) end.
    fold (ms_off s n am idx z).
    pose proof (msy_off z) as Hoff.
    unfold massert. replace (ms_off s n am idx z <=? ms_slack n am) with true by (symmetry; apply Z.leb_le; lia).
    eapply yields_bind0; [apply yields_ret|].
    eapply yields_bind0; [apply yields_setm|].
    unfold ms_ptr, ms_post, ms_am2, ms_hdr, ms_frame, ms_rsv, ms_reserved.
    apply yields_ret.
  Qed.
End Yields.

Section MallocYields.
  Variables (s0 : astate) (n : Z).
  Hypothesis HW0 : WF s0.
  Hypothesis HC : slow_case s0 n.
  Let sc : Z := malloc_class s0 n.

  Lemma slow_prefix_yields : ltac2:(tb__ "0|7|
S51S7cS7dS7cS6S0A2M0A1M1S7A2S1aS7G1S36S7S7dS6A1M2S29G1A1M3Lx;Sc5G2S47Sb2R1Vn;A2A1S26R1A1S85S6A1A4S6S1aS9G1S37R1A1S9S80G3L_;S46S12R1A1M4Z0A2S25G1S85G0A1M5A2M6S38G4A1S0S1aS8aG1S3cR3S32S43S12R2A1R1A2R2A2A2S8aS25G1S7eG0S7fS6S0R4S34R2A1A4A2A2L_;A4Tfirst;X80x2Lam;A4Lgm;G6X7dx2Ls;Vs0;A5S81S7cS10S0A2A1S7fG1S7G5Vs0;A4A4").
  Proof using HC HW0.
    destruct HC as [Hn HS].
    eapply yields_bind0; [apply yields_ret|]. cbn zeta.
    destruct (nth (Z.to_nat (malloc_class s0 n)) (st_active s0) None) as [g|] eqn:Eg; [|apply yields_ret].
    pose proof (malloc_class_range s0 n Hn) as [R1 _].
    destruct (head_used [] None U0 s0 (malloc_class s0 n) g HW0 R1 Eg) as (am & Hu & _).
    pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
    eapply yields_bind0; [apply (yields_getm _ _ _ Mg)|].
    rewrite (HS g am eq_refl Mg). cbn. reflexivity.
  Qed.

  Theorem malloc_slow_fail_yields : ltac2:(tb__ "0|1|
S82S7cS10S0A2A1S7S51S7cS0S7A2S18S17Vsc;Vn;Vs0;A4R2S7fS0S7N1R1A4A4S51S7cS7dS6A1M0S7A2S1bVn;Vs0;A2R3S7fG0S7S85S6A1R2A4A4F_;Fs1;Fktr;").
  Proof using HC HW0.
    intros ktr s1 HY. destruct HC as [Hn HS].
    rewrite malloc_loop_eq; [| unfold size_overflows; apply Z.leb_gt; unfold MMAP_THRESHOLD in Hn; lia | apply Z.leb_gt; lia].
    unfold malloc_loop.

    eapply yields_bind0; [apply yields_ret|]. cbn zeta.
    eapply (yields_bind _ _ s0 [] ktr None s0).
    { pose proof slow_prefix_yields as P. unfold bind in P. cbn zeta in P.
      destruct (nth (Z.to_nat (malloc_class s0 n)) (st_active s0) None) as [g|] eqn:Eg; [|apply yields_ret].
      pose proof (malloc_class_range s0 n Hn) as [R1 _].
      destruct (head_used [] None U0 s0 (malloc_class s0 n) g HW0 R1 Eg) as (am & Hu & _).
      pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
      eapply yields_bind0; [apply (yields_getm _ _ _ Mg)|]. rewrite (HS g am eq_refl Mg). cbn. reflexivity. }
    cbn beta iota. rewrite <- (app_nil_r ktr).
    eapply (yields_bind _ _ s0 ktr [] None s1).
    { eapply yields_bind1; [exact HY|]. cbn. reflexivity. }
    apply yields_ret.
  Qed.

  Theorem malloc_slow_ok_yields : ltac2:(tb__ "0|2|
S82S7cS10S0A2M0A1S7S6S9S0S0S51S7cS0S7A2S18S17Vsc;Vn;Vs0;A4R6S7fS0S7R2R5A4A4Sa1R6Vsc;Vn;R5R4R3A6S1S40Z0R3A2S42R3Z100A2A2S51S7cS7dS6A1M1S7A2S1bVn;Vs0;A2S83G0R9Sa4R8Vn;R6R5R4A5A3S7fG1S7S7eS6Sa0R8Vn;R6R5R4A5A2Sa3R8Vn;R7R6R5R4A6A4A4F_;F_;F_;Fz;Fidx;Fam;Fg;Fs1;Fktr;").
  Proof using HC HW0.
    intros ktr s1 g am idx z HY HF Hz. destruct HC as [Hn HS]. pose proof HF as (HI1 & Hhd & Hu & Hsc & Fit & Hidx).
    rewrite malloc_loop_eq; [| unfold size_overflows; apply Z.leb_gt; unfold MMAP_THRESHOLD in Hn; lia | apply Z.leb_gt; lia].
    unfold malloc_loop.
    eapply yields_bind0; [apply yields_ret|]. cbn zeta.
    eapply (yields_bind _ _ s0 [] (ktr ++ ms_trace s1 n am idx z) None s0).
    { destruct (nth (Z.to_nat (malloc_class s0 n)) (st_active s0) None) as [g0|] eqn:Eg; [|apply yields_ret].
      pose proof (malloc_class_range s0 n Hn) as [R1 _].
      destruct (head_used [] None U0 s0 (malloc_class s0 n) g0 HW0 R1 Eg) as (am0 & Hu0 & _).
      pose proof (usedX_MT _ _ _ _ Hu0) as [Mg0 _].
      eapply yields_bind0; [apply (yields_getm _ _ _ Mg0)|]. rewrite (HS g0 am0 eq_refl Mg0). cbn. reflexivity. }
    cbn beta iota.
    eapply (yields_bind _ _ s0 ktr (ms_trace s1 n am idx z) (Some (g, idx)) s1).
    { eapply yields_bind1; [exact HY|]. cbn beta iota.
      replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      eapply (yields_bind0 _ _ s1 _ (active_hd s1 sc) s1); [rewrite get_head_eq; reflexivity|].
      rewrite Hhd. apply yields_ret. }
    eapply yields_bind0; [apply yields_ret|].
    eapply yields_bind1; [|apply yields_ret].
    exact (enframe_slow_yields s1 sc n g am idx HF z Hz).
  Qed.
End MallocYields.

Lemma meta_cells_in_image_gen s g am c : ltac2:(tb__ "0|1|
S74Vs;A1S2S7dScA1S56Vs;Vg;A2S7eScSfVam;A1A2M0A3S8cS4dVc;S77Vg;G0A2A3S8cS4dVc;S53Vs;A1A3F_;F_;F_;").
Proof.
  intros HK Mg Hc. pose proof HK as (ND & KP & _ & _ & Hcnt).
  destruct (KP g (MT_Some_In_keys _ _ _ Mg)) as (a & k & Ha & Hk & Eg).
  assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
  unfold image. apply in_app_iff. right. apply in_app_iff. left.
  apply (In_areas_cells_intro s (st_areas s) a c Ha). intros next. unfold area_cells. apply in_app_iff. right.
  apply in_flat_map. exists (Z.to_nat k). split; [apply in_seq; lia|].
  rewrite Z2Nat.id by lia. rewrite <- Eg. unfold MT in Mg. rewrite Mg. exact Hc.
Qed.

Section Gap.
  Variables (C : mconsts) (s0 s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta) (idx z : Z) (ktr : list (kreq * Z)).
  Variables (rd0 rd1 : word -> option byte) (wok0 wok1 : word -> bool) (vm : VmMaps).

  Hypothesis HW0 : WF s0.
  Hypothesis HC : slow_case s0 n.
  Hypothesis HMI : ltac2:(tb__ "0|0|
SccVC;S81S6A1S7eS7cS6S0A2S7fS6S0Vg;Vidx;A4A2S5aSc7Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
  Hypothesis HF : ltac2:(tb__ "0|0|
Sa1Vs;Sb2Vs0;Vn;A2Vn;Vg;Vam;Vidx;A6").
  Hypothesis HUB : ub_same s0 s.
  Hypothesis HYA : ltac2:(tb__ "0|0|
S51S7cS0S7A2S18S17Sb2Vs0;Vn;A2Vn;Vs0;A4Vktr;S7fS0S7Vidx;Vs;A4A4").
  Hypothesis Hz : 0 <= z < 256.
  Hypothesis HS : statics_in_image C.

  Definition f_off : Z := ltac2:(tb__ "0|0|
Sa5Vs;Vn;Vam;Vidx;Vz;A5").
  Definition f_fr : frame := ltac2:(tb__ "0|0|
Sa9Vs;Vn;Vam;Vidx;Vz;A5").
  Definition f_am2 : ameta := ltac2:(tb__ "0|0|
Sa8Vs;Vn;Vam;Vidx;Vz;A5").
  Definition f_s' : astate := ltac2:(tb__ "0|0|
Sa3Vs;Vn;Vg;Vam;Vidx;Vz;A6").
  Definition f_st : Z := ltac2:(tb__ "0|0|
SacVL;S15Vam;Vidx;A2A2").
  Definition f_p : Z := ltac2:(tb__ "0|0|
SacVL;Sa0Vs;Vn;Vam;Vidx;Vz;A5A2").
  Definition f_e : Z := ltac2:(tb__ "0|0|
SacVL;Sb7Vam;Vidx;A2A2").
  Definition f_zm : Z := ltac2:(tb__ "0|0|
SacVL;S19Vam;A1A2").

  Definition f_bv0 : byteview := byteview_of rd0 wok0.
  Definition f_bv1 : byteview := byteview_of rd1 wok1.
  Definition f_rv0 : byteview := byteview_of rd0 (fun _ => true).
  Definition f_rv1 : byteview := byteview_of rd1 (fun _ => true).

  Definition f_hdrcells : list mcell := ltac2:(tb__ "0|1|
S7cS0S0A2S82S4dA1Lp;Sa2Vs;Vn;Vam;Vidx;Vz;A5S0S0S84S4dS4fS4eS8S15Vam;Vidx;A2M0N3A2A1U1S50R2A1A3S84S4dS4fS4eS8G0N2A2A1U2S50R1A1A3S81S4dA1A3A3Lh16;Lh3;X7cx1").
  Definition f_frcells : list mcell := ltac2:(tb__ "0|4|
S80S82S4dA1L_;S46S94Z0M0A2S81S4dA1M1S84S4dS4fS4eS8Sa0Vs;Vn;Vam;Vidx;Vz;A5M2N4A2A1U1M3S50G0A1A3S84S4dS4fS4eS8G2N3A2A1G3S50S72Vam;Vidx;S93A3A1A3S84S4dS4fS4eS8G2N2A2A1U2S50S73Vam;Vidx;S93A3A1A3G1A3A3A3X80x2").
  Definition f_footcells : list mcell := ltac2:(tb__ "0|0|
Sb6Vam;Vidx;S93A3").
  Definition f_newcells : list mcell := ltac2:(tb__ "0|0|
S83S4dS9cS83S4dS9bS9aA3A3").

  Definition in_zone (x : Z) : Prop := ltac2:(tb__ "0|0|
S1S40S43S90Z3A2Vx;A2S42Vx;S91A2A2").

  Hypothesis V1 : ltac2:(tb__ "0|1|
S0S1S40Z0R1A2S42R1S44Z2Z40A2A2A2S4S95R2A1A1S1S2S7dSc3Q8A1A1Vrd1;SadR3A1M0A1Vrd0;G0A1A3S2S80Vwok1;G0A1Vwok0;G0A1A3A2F_;F_;Fx;").
  Hypothesis V2 : ltac2:(tb__ "0|1|
S0S95R1A1S1S2S80Vwok1;SadR2A1A1S89A3S3Sc3Q8A1M0G0S2S7dG0A1Vrd1;SadR3A1A1S7eG0R1A2A3Lb;A2A2F_;Fx;").
  Hypothesis V3 : ltac2:(tb__ "0|3|
S4dS8cS4dR1S92A3S88Sc2R1S55R3A1A2S1S2S80Vwok1;SadS41S5bVL;S5cR4A1A2S4aR2A1A2A1M0A1S89A3S2S7dSc3Q8M1A1M2A1Vrd1;G0A1S7eG2Sc4G1S75S7bVL;S5dR4A1A2S55R4A1R2A3A2A2A3A2F_;Fj;F_;Fc;").

  Lemma F_n : ltac2:(tb__ "0|0|
S1S40Z0Vn;A2S42Vn;S16A2A2"). Proof using HC. exact (proj1 HC). Qed.
  Lemma F_I : ltac2:(tb__ "0|0|
S5fS81S6A1S7eS7cS6S0A2S7fS6S0Vg;Vidx;A4A2S5aVs;A4"). Proof using HMI. exact (mig_I HMI). Qed.
  Lemma F_u : ltac2:(tb__ "0|0|
S5eS81S6A1Vs;Vg;Vam;A4"). Proof using HF. exact (proj1 (proj2 (proj2 HF))). Qed.
  Lemma F_MT : ltac2:(tb__ "0|0|
S2S7dScA1S56Vs;Vg;A2S7eScSfVam;A1A2A3"). Proof using HF. exact (proj1 (usedX_MT _ _ _ _ F_u)). Qed.
  Lemma F_ND : List.NoDup (keys s). Proof using HMI. exact (proj1 (inv_keys F_I)). Qed.
  Lemma F_um : ltac2:(tb__ "0|0|
S8cS7cS6S9A2S7fS6S9Vg;Vam;A4S63Vs;A1A3"). Proof using HF HMI. apply (proj2 (used_metas_iff s g am F_ND)). exact F_MT. Qed.
  Lemma F_repr : ltac2:(tb__ "0|0|
Sb5VL;Vs;S97A3"). Proof using HMI. exact (mig_reprO HMI). Qed.
  Lemma F_L : layout_ok L s. Proof using HMI. exact (proj1 (proj1 F_repr)). Qed.
  Lemma F_idx : ltac2:(tb__ "0|0|
S1S40Z0Vidx;A2S40Vidx;S13Vam;A1A2A2"). Proof using HF. exact (proj2 (proj2 (proj2 (proj2 (proj2 HF))))). Qed.
  Lemma F_fit : ltac2:(tb__ "0|0|
S40S41Vn;SaA2S27Vam;A1A2"). Proof using HF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HF))))). Qed.
  Lemma F_sl : ltac2:(tb__ "0|0|
S2S7dSbA1S1dSdVam;Vidx;A2A1S85SbA1A3").
  Proof using HF HMI.
    destruct (inv_reserved F_I g idx eq_refl) as (am' & Hu' & _ & Hfr & _).
    rewrite (usedX_fun _ _ _ _ _ Hu' F_u) in Hfr. exact Hfr.
  Qed.
  Lemma F_G : ltac2:(tb__ "0|0|
S71S81S6A1S7eS7cS6S0A2S7fS6S0Vg;Vidx;A4A2Vs;Vg;Vam;A5"). Proof using HF HMI. exact (inv_groups F_I g am F_u). Qed.
  Lemma F_len : ltac2:(tb__ "0|0|
S2S88S8bS1cS33Vam;A1A2S47S41S13Vam;A1Z1A2A1A3").
  Proof using HF HMI. pose proof F_G as ((_ & _ & L0 & _) & _). exact L0. Qed.
  Lemma F_s' : ltac2:(tb__ "0|0|
S2S7S8dSc9Vg;SfS8eA1Vs;A3A3"). Proof using . reflexivity. Qed.
  Lemma F_y : ltac2:(tb__ "0|1|
S51S7cS7dS6A1M0S7A2S1bVn;Vs0;A2S83S7cS10S0A2Vktr;Sa4Vs;Vn;Vam;Vidx;Vz;A5A3S7fG0S7S7eS6Sa0Vs;Vn;Vam;Vidx;Vz;A5A2S8dA4A4").
  Proof using HC HF HW0 HYA Hz. exact (malloc_slow_ok_yields s0 n HW0 HC ktr s g am idx z HYA HF Hz). Qed.
  Lemma F_W' : WF f_s'.
  Proof using HC HF HW0 HYA Hz. exact (malloc_wf s0 n _ _ _ HW0 (proj1 F_n) F_y). Qed.
  Lemma F_L' : layout_ok L f_s'. Proof using HMI. exact F_L. Qed.
  Lemma F_MT' : ltac2:(tb__ "0|0|
S2S7dScA1S56S8dVg;A2S7eScSfS8eA1A2A3"). Proof using . rewrite F_s', MT_upd_same. reflexivity. Qed.
  Lemma F_u' : ltac2:(tb__ "0|0|
S5eS81S6A1S8dVg;S8eA4"). Proof using . apply usedX_intro; [reflexivity | exact F_MT']. Qed.
  Lemma F_ND' : List.NoDup (keys f_s'). Proof using HC HF HW0 HYA Hz. exact (proj1 (inv_keys F_W')). Qed.
  Lemma F_um' : ltac2:(tb__ "0|0|
S8cS7cS6S9A2S7fS6S9Vg;S8eA4S63S8dA1A3"). Proof using HC HF HW0 HYA Hz. apply (proj2 (used_metas_iff f_s' g f_am2 F_ND')). exact F_MT'. Qed.
  Lemma F_am2_slot j : ltac2:(tb__ "0|0|
S40Z0Vj;A2S2S1cSdS8eVj;A2S80S1cL_;S46Vj;Vidx;A2S23S7eS7cS0S0A2Sa2Vs;Vn;Vam;Vidx;Vz;A5A2S7eSbS93A2A2SdVam;Vj;A2X80x2A3F_;").
  Proof using HF HMI Hz.
    intros Hj. unfold f_am2, ms_am2. rewrite nth_slot_upd_slot; [| pose proof F_idx; lia | exact Hj | rewrite F_len; pose proof F_idx; lia].
    unfold f_fr. destruct (j =? idx); reflexivity.
  Qed.
  Lemma F_sl' : ltac2:(tb__ "0|0|
S2S7dSbA1S1dSdS8eVidx;A2A1S7eSbS93A2A3").
  Proof using HF HMI Hz. rewrite F_am2_slot by (pose proof F_idx; lia). rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma F_hdr' : ltac2:(tb__ "0|1|
S2S7dS7cS0S0A2M0A1S1eSdS8eVidx;A2A1S7eG0Sa2Vs;Vn;Vam;Vidx;Vz;A5A2A3").
  Proof using HF HMI Hz. rewrite F_am2_slot by (pose proof F_idx; lia). rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma F_kind : ltac2:(tb__ "0|0|
S2S21S22S93A1S11A3"). Proof using . reflexivity. Qed.
  Lemma F_off : ltac2:(tb__ "0|1|
S1S1S40Z0M0S94A2S40S94ZffA2A2S1S40S41S45SeS94A2Vn;A2S43Sa7Vam;A1SaA2A2S40G0Vn;A2A2A2").
  Proof using HC HF Hz.
    pose proof (msy_off s (malloc_class s0 n) n g am idx HF z) as [H1 H2]. pose proof F_fit as Fit. pose proof F_n as Hn.
    unfold f_off. split; [lia|]. split; [|lia].
    assert (UNIT * ms_slack n am <= ms_stride am - IB - n).
    { unfold ms_slack, UNIT. pose proof (Z.mul_div_le (ms_stride am - IB - n) 16 ltac:(lia)). unfold ms_stride in *. lia. }
    unfold UNIT in *. nia.
  Qed.

  Lemma F_blocks : ltac2:(tb__ "0|4|
S3S82S7cS6S0A2M0A1M1G1S3G1G1S1S2G1S59S8dA1S83G0R2S84G0S7fS6S0Sa0Vs;Vn;Vam;Vidx;Vz;A5M2Vn;A4R1A3A3A3S1S2G1S59Vs0;A1M3S83G0R2R1A3A3S4S8cS6G2Sc6G0S6S86S6S0A2G3A4A3A1A2A2Ll2;A2Ll1;A2").
  Proof using HC HF HW0 HYA Hz.
    pose proof (malloc_blocks s0 n _ _ _ HW0 (proj1 F_n) F_y) as (l1 & l2 & E1 & E2 & _ & NI). exists l1, l2. auto.
  Qed.
  Lemma F_ub : ltac2:(tb__ "0|0|
S2S82S7cS6S0A2A1S59Vs;A1S59Vs0;A1A3"). Proof using HMI HUB HW0. exact (ub_same_user_blocks s0 s (proj1 (inv_keys HW0)) F_ND HUB). Qed.

  Lemma F_geom : ltac2:(tb__ "0|5|
S1S40Z10Sa7Vam;A1M0A2S1S2S0S90S41S41S99SeA2S45G0Vidx;A2M1A2A3S1S2S0S9eS41S90S45SeS94A2A2A3S1S2S0S91S43S41S90G0A2SaA2A3S1S2S7cS0S0A2ScaVL;Vam;Vidx;A3S7fS0S0S43S90Z3M2A2S41S43G0SaA2G2A2A4A3S1S42Z0M3S99A2S1S42S41S91SaA2S44Z2Z3fA2A2S1S1S40G3G1A2S40S41G1G0A2S45G0S41S13Vam;A1Z1A2A2A2A2S3S7cS54S0A2M4G4S1S8cG4R1S58Vs;A1A3S1S78S7fS0S0S99S41S70Vam;A1SaA2A4S6eVL;R1A2A2S2S54S86S54S0R1A3S4eS2dS24S19Vam;A1A1G3A2A1A3A2A2Lrg;A2A2A2A2A2A2A2A2A2").
  Proof using HF HMI Hz.
    pose proof F_G as G0. pose proof (stride_pos _ _ _ _ _ G0) as Sp.
    destruct (used_group_region [] (Some (g, idx)) U0 s g am F_I F_u) as (rg & Hr & Hk & Hl & Ho0 & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
    pose proof F_L as (_ & _ & _ & POS). destruct (POS _ InR) as [P1 P2]. unfold crange, loc_addr in P1, P2. cbn [fst snd] in P1, P2.
    pose proof F_idx as Hi.
    assert (E1 : f_st = f_zm + UNIT + ms_stride am * idx).
    { unfold f_st, f_zm, addr_of, loc_addr, slot_start, ms_stride. destruct (am_mem am); cbn [padd]. lia. }
    assert (E2 : f_p = f_st + UNIT * f_off).
    { unfold f_p, f_st, ms_ptr, f_off, addr_of, loc_addr. destruct (slot_start am idx); cbn [padd]. lia. }
    assert (E3 : f_e = f_st + ms_stride am - IB).
    { unfold f_e, f_st, addr_of, loc_addr, slot_end, ms_stride. destruct (slot_start am idx); cbn [padd]. lia. }
    assert (Hsi : 0 <= ms_stride am * idx /\ ms_stride am * idx + ms_stride am <= ms_stride am * (am_last am + 1)) by (unfold ms_stride in *; split; nia).
    assert (Ezm : f_zm = ly_reg L (prid (am_mem am)) + poff (am_mem am)) by (unfold f_zm, addr_of, loc_addr; destruct (am_mem am); reflexivity).
    split; [exact Sp|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    split; [unfold zone_range; rewrite E1; unfold f_zm, addr_of, ms_stride; reflexivity|].
    split; [lia|]. split; [unfold group_extent, ms_stride in *; lia|]. split; [exact Hsi|].
    exists (LMem (SP (prid (am_mem am)) 0), rg_len rg). split; [exact InR|]. split; [|reflexivity].
    unfold range_incl, crange, loc_addr. cbn [fst snd]. lia.
  Qed.

  Definition f_zg : Z := addr_of L g.
  Lemma F_area : ltac2:(tb__ "0|3|
S3S6S6S3S0S0S1S8cS6R2S3dVs;A1A3S1S1S40Z0M0R1A2S42R1S2aA2A2S1S2S6Vg;S8R2S41S1fS45S2bR1A2M1A2A2A3S1S8cS7cS54S0A2S7fS54S0S4eR2A1S20A4S58Vs;A1A3S1S42G0SacVL;R2A2M2A2S1S42S41G2S20A2S44Z2Z3fA2A2S1S2S0S9fS41S41G2S1fA2G1A2A3S3S14S14S1S2S7dS14A1S7aVs;S24R3A1A2S7eS14R1A2A3S4S2S3bS3aR1A1S2cA3A1A2Lrga;A2A2A2A2A2A2A2A2Lk;A2La;A2").
  Proof using HF HMI Hz.
    pose proof F_MT as Mg.
    pose proof (inv_keys F_I) as (ND & KP & _ & _ & Hcnt).
    destruct (KP g (MT_Some_In_keys _ _ _ Mg)) as (a & k & Ha & Hk0 & Eg).
    assert (Hk : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk0; destruct (sptr_eqb a _); lia).
    exists a, k. split; [exact Ha|]. split; [exact Hk|]. split; [exact Eg|].
    assert (InA : In (LMem a, PGSZ) (footprint s)).
    { unfold footprint. right. apply in_app_iff. left. apply in_map_iff. exists a. auto. }
    split; [exact InA|].
    pose proof F_L as (_ & _ & _ & POS). destruct (POS _ InA) as [P1 P2]. unfold crange, loc_addr in P1, P2. cbn [fst snd] in P1, P2.
    clear V1 V2 V3.
    unfold f_zg, addr_of. split; [destruct a; cbn [loc_addr prid poff] in P1, P2 |- *; lia|]. split; [destruct a; cbn [loc_addr prid poff] in P1, P2 |- *; lia|].
    split; [rewrite Eg; unfold loc_addr; destruct a; cbn [padd]; lia|].
    pose proof (inv_areas F_I) as (_ & A2 & _). destruct (A2 _ Ha) as (r & o & rga & Ea & _ & _ & Hra & _ & _ & Hkind).
    exists rga. subst a. cbn [prid]. split; [exact Hra|]. destruct (rg_kind rga); [discriminate|discriminate|destruct Hkind].
  Qed.

  Lemma FBV1 : ltac2:(tb__ "0|1|
S0S1S40Z0R1A2S42R1S44Z2Z40A2A2A2S4S95R2A1A1S1S2S7dS0A1M0S8fR3A1S97R3A1A3S2G0S98R3A1S9dR3A1A3A2F_;F_;Fx;").
  Proof using V1.
    intros x Hx Hb. destruct (V1 x Hx Hb) as [E1 E2].
    unfold f_bv1, f_bv0, f_rv1, f_rv0, byteview_of. unfold wz in E1, E2. rewrite E1, E2. split; reflexivity.
  Qed.

  Lemma FBV2 : ltac2:(tb__ "0|0|
S0S1S40Z0R1A2S42R1S44Z2Z40A2A2A2S95R2A1S4S2S7dS0A1S8fR3A1S85S0A1A3A1F_;F_;Fx;").
  Proof using Hz V2.
    intros x Hx Hb. destruct (V2 x Hb) as [E1 [b E2]]. unfold f_bv1, byteview_of. unfold wz in E1, E2.
    replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    cbn [andb]. rewrite E1, E2. discriminate.
  Qed.

  Lemma FBV3 : ltac2:(tb__ "0|0|
S4dS8cS4dR1S92A3S40Z0S5bVL;S5cR2A1A2A2S40S41S5bVL;S5cR3A1A2S4aS55R3A1A1A2S44Z2Z40A2A2S0S4S2S62S5dR5A1S60R1A1A3A1Fv;S57VL;S8fR5A3F_;F_;F_;F_;Fc;").
  Proof using Hz V3.
    intros c Hc Hlo Hhi Hnv. unfold cell_holds.
    destruct (mc_val c) as [v|q|v|] eqn:Ev; [| | exfalso; exact (Hnv v eq_refl) |];
      intros j Hj; destruct (V3 c Hc j Hj) as [E1 E2]; rewrite Ev in E2; unfold f_bv1, byteview_of; unfold wz in E1, E2;
      (replace ((0 <=? loc_addr L (mc_loc c) + Z.of_nat j) && (loc_addr L (mc_loc c) + Z.of_nat j <? 2 ^ 64))%bool with true
         by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia));
      cbn [andb]; rewrite E1, E2; f_equal; apply Z_to_bv_small; change (bv_modulus 8) with 256; unfold le_byte; apply Z.mod_pos_bound; lia.
  Qed.

  Lemma own_hdr_new : ltac2:(tb__ "0|0|
S2S82S4dA1ScbS8eVidx;A2S83S4dS9cS9bA3A3").
  Proof using HF HMI Hz.
    unfold own_hdr. rewrite F_hdr', F_sl'. unfold f_hdrcells, f_frcells, f_off, f_fr, ms_frame. cbn [fr_off].
    destruct (ms_hdr s n am idx z) as [h3 h16]. reflexivity.
  Qed.

  Definition f_Ccheck : mcell := ltac2:(tb__ "0|0|
S4fS4eS8S15Vam;Vidx;A2N4A2A1U1S50Z0A1A3").
  Lemma Ccheck_in : In f_Ccheck (image s).
  Proof using HF HMI.
    apply (In_image_group s g am _ F_um). apply (In_group_slot g am idx); [exact F_idx|].
    unfold slot_cells. left. reflexivity.
  Qed.
  Lemma Ccheck_in' : In f_Ccheck (image f_s').
  Proof using HC HF HW0 HYA Hz.
    apply (In_image_group f_s' g f_am2 _ F_um'). apply (In_group_slot g f_am2 idx); [exact F_idx|].
    unfold slot_cells. left. reflexivity.
  Qed.

  Lemma image'_cases c : ltac2:(tb__ "0|0|
S8cS4dVc;S53S8dA1A3S5S8cS4dVc;S92A3S8cS4dVc;S53Vs;A1A3A2F_;").
  Proof using HF HMI Hz.
    intros Hin. rewrite F_s' in Hin.
    destruct (upd_image_In s g am f_am2 F_ND F_MT c Hin) as [Hold | [Hm | Hgr]]; [right; exact Hold| |].
    -
      right. unfold meta_slot_cells in Hm. cbn in Hm.
      assert (OLD : forall c', In c' (meta_slot_cells g (Some (MUsed am))) -> In c' (image s)).
      { intros c' Hc'. exact (meta_cells_in_image_gen s g am c' (inv_keys F_I) F_MT Hc'). }
      unfold meta_slot_cells in OLD.
      destruct Hm as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; apply OLD; cbn; tauto.
    - unfold group_cells in Hgr. apply in_app_iff in Hgr as [Hh|Hsl].
      + right. apply (In_image_group s g am c F_um). unfold group_cells. apply in_app_iff. left. exact Hh.
      + apply in_flat_map in Hsl as [j [Hj Hc]]. apply In_zseq in Hj. change (am_last f_am2) with (am_last am) in Hj.
        unfold slot_cells in Hc. rewrite (F_am2_slot j) in Hc by lia.
        change (slot_start f_am2 j) with (slot_start am j) in Hc.
        destruct (j =? idx) eqn:Eji.
        * apply Z.eqb_eq in Eji. subst j. cbn [ss_hdr ss_fr] in Hc.
          apply in_app_iff in Hc as [Hc|Hc].
          -- right. destruct Hc as [<-|[]]. exact Ccheck_in.
          -- assert (K : In c (own_hdr f_am2 idx)).
             { unfold own_hdr. rewrite F_hdr', F_sl'. exact Hc. }
             rewrite own_hdr_new in K. left. unfold f_newcells. apply in_app_iff in K. apply in_app_iff.
             destruct K as [K|K]; [left; exact K | right; apply in_app_iff; left; exact K].
        * right. apply (In_image_group s g am c F_um). apply (In_group_slot g am j); [lia|]. exact Hc.
  Qed.

  Lemma newcells_ranges c : ltac2:(tb__ "0|2|
S8cS4dVc;S92A3S1S40S43S90Z3A2S86S0S0S52VL;Vc;A2M0A3M1A2S1S40S41G1S87S0S0G0A3A2S91A2S1Sc2U0S55Vc;A1A2S0S4S2S62S5dVc;A1S60R1A1A3A1Fv;A2A2A2F_;").
  Proof using HC HF HMI Hz.
    intros Hc. pose proof F_geom as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & _). pose proof F_off as (Ho & Hfit & Hn).
    assert (Est : forall d, cell_range L (MCell (LMem (padd (slot_start am idx) d)) 1 (VZ 0)) = (f_st + d, 1)
                  /\ forall w v, cell_range L (MCell (LMem (padd (slot_start am idx) d)) w v) = (f_st + d, Z.of_nat w)).
    { intros d. unfold cell_range, f_st, addr_of, loc_addr. destruct (slot_start am idx); cbn [mc_loc mc_w padd]. split; [f_equal; lia|]. intros; f_equal; lia. }
    assert (Ep : forall w v d, cell_range L (MCell (LMem (padd (ms_ptr s n am idx z) d)) w v) = (f_p + d, Z.of_nat w)).
    { intros w v d. unfold cell_range, f_p, addr_of, loc_addr. destruct (ms_ptr s n am idx z); cbn [mc_loc mc_w padd]. f_equal; lia. }
    assert (Ee : forall w v d, cell_range L (MCell (LMem (padd (slot_end am idx) d)) w v) = (f_e + d, Z.of_nat w)).
    { intros w v d. unfold cell_range, f_e, addr_of, loc_addr. destruct (slot_end am idx); cbn [mc_loc mc_w padd]. f_equal; lia. }
    unfold f_newcells, f_hdrcells, f_frcells, f_footcells, frame_footer_cells in Hc. rewrite F_kind in Hc.
    change (frame_ptr am idx f_fr) with (ms_ptr s n am idx z) in Hc.
    change (fr_n f_fr) with n in Hc.
    assert (Hrsv : reserved_of am f_fr = ms_stride am - IB - UNIT * f_off - n) by reflexivity.
    unfold IB, UNIT in *.
    destruct (ms_hdr s n am idx z) as [h3 h16].
    apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
    - destruct Hc as [<-|[<-|[]]]; (rewrite (proj2 (Est _)); cbn [mc_w mc_val fst snd Z.of_nat]; split; [lia|]; split; [lia|]; split; [cbn; lia | intros; discriminate]).
    - destruct (f_off =? 0) eqn:E0; [destruct Hc|]. apply Z.eqb_neq in E0.
      destruct Hc as [<-|[<-|[<-|[]]]]; (rewrite Ep; cbn [mc_w mc_val fst snd Z.of_nat]; split; [lia|]; split; [lia|]; split; [cbn; lia | intros; discriminate]).
    - apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
      + destruct (0 <? reserved_of am f_fr) eqn:Er; [|destruct Hc]. apply Z.ltb_lt in Er. destruct Hc as [<-|[]].
        rewrite Ep. cbn [mc_w mc_val fst snd Z.of_nat]. split; [lia|]. split; [lia|]. split; [cbn; lia | intros; discriminate].
      + destruct (5 <=? reserved_of am f_fr) eqn:Er; [|destruct Hc]. apply Z.leb_le in Er. destruct Hc as [<-|[]].
        rewrite Ee. cbn [mc_w mc_val fst snd Z.of_nat]. split; [lia|]. split; [lia|]. split; [cbn; lia | intros; discriminate].
      + destruct (5 <? reserved_of am f_fr) eqn:Er; [|destruct Hc]. apply Z.ltb_lt in Er. destruct Hc as [<-|[]].
        rewrite Ee. cbn [mc_w mc_val fst snd Z.of_nat]. split; [lia|]. split; [lia|]. split; [cbn; lia | intros; discriminate].
  Qed.

  Lemma newcells_hold c : ltac2:(tb__ "0|0|
S8cS4dVc;S92A3S57VL;S8fVc;A3F_;").
  Proof using HC HF HMI Hz V3.
    intros Hc. pose proof F_geom as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & [Hsi1 Hsi2] & _).
    destruct (newcells_ranges c Hc) as (R1 & R2 & Rw & Rv). unfold cell_range in R1, R2. cbn [fst snd] in R1, R2.
    apply FBV3; [exact Hc | | | exact Rv]; unfold UNIT, IB in *; lia.
  Qed.

  Definition f_avoids (r : Z * Z) : Prop := ltac2:(tb__ "0|0|
S79Vr;ScaVL;Vam;Vidx;A3A2").

  Lemma avoids_bytes lo w : ltac2:(tb__ "0|2|
S96S7fS0S0Vlo;Vw;A4A1S42Z0Vlo;A2S42S41Vlo;Vw;A2M0S44Z2Z3fA2A2S0S1S40Vlo;R1A2S42R1G0A2A2S1S2S7dS0A1M1S8fR2A1S97R2A1A3S2G1S98R2A1S9dR2A1A3A2F_;Fx;F_;F_;F_;").
  Proof using HF HMI Hz V1.
    intros D1 Hlo Hhi x Hx. pose proof F_geom as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & _). unfold f_avoids in D1. rewrite EZ in D1.
    unfold ranges_disjoint in D1. cbn [fst snd] in D1.
    apply FBV1; [lia | unfold in_zone; unfold IB in *; lia].
  Qed.

  Lemma cell_transfer c : ltac2:(tb__ "0|2|
S57VL;S97Vc;A3S96S52VL;Vc;A2M0A1Sc2U0S55Vc;A1A2S42Z0S86S0S0G0A3M1A2S42S41G1S87S0S0G0A3A2S44Z2Z3fA2A2S57VL;S8fVc;A3F_;F_;F_;F_;F_;").
  Proof using HF HMI Hz V1.
    intros Hc Hav Hw Hlo Hhi. unfold cell_range in *. cbn [fst snd] in Hlo, Hhi.
    pose proof (avoids_bytes _ _ Hav Hlo Hhi) as B.
    unfold cell_holds in *. destruct (mc_val c).
    - intros j Hj. rewrite (proj1 (B (loc_addr L (mc_loc c) + Z.of_nat j) ltac:(lia))). exact (Hc j Hj).
    - intros j Hj. rewrite (proj1 (B (loc_addr L (mc_loc c) + Z.of_nat j) ltac:(lia))). exact (Hc j Hj).
    - destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm].
      rewrite (proj1 (B (loc_addr L (mc_loc c)) ltac:(lia))). exact Hb.
    - intros j Hj. rewrite (proj1 (B (loc_addr L (mc_loc c) + Z.of_nat j) ltac:(lia))). exact (Hc j Hj).
  Qed.

  Lemma footprint_s' : ltac2:(tb__ "0|0|
S2S82S7cS54S0A2A1S58S8dA1S58Vs;A1A3"). Proof using . reflexivity. Qed.

  Lemma image'_cell_span c : ltac2:(tb__ "0|2|
S8cS4dVc;S53S8dA1A3S1S42Z0S86S0S0S52VL;Vc;A2M0A3M1A2S42S41G1S87S0S0G0A3A2S44Z2Z3fA2A2A2F_;").
  Proof using HC HF HMI HW0 HYA Hz.
    intros Hin. destruct (image_in_footprint f_s' L c F_W' F_L' Hin) as (rg & Hrg & [I1 I2]).
    pose proof F_L' as (_ & _ & _ & POS). destruct (POS rg Hrg) as [P1 P2].
    assert (0 <= snd (cell_range L c)) by (unfold cell_range; cbn; lia). lia.
  Qed.

  Lemma footer'_cell_span c : ltac2:(tb__ "0|2|
S8cS4dVc;Sb4S8dA1A3S1S42Z0S86S0S0S52VL;Vc;A2M0A3M1A2S42S41G1S87S0S0G0A3A2S44Z2Z3fA2A2A2F_;").
  Proof using HC HF HMI HW0 HYA Hz.
    intros Hin. destruct (footer_in_footprint f_s' L c F_W' F_L' Hin) as (rg & Hrg & [I1 I2]).
    pose proof F_L' as (_ & _ & _ & POS). destruct (POS rg Hrg) as [P1 P2].
    assert (0 <= snd (cell_range L c)) by (unfold cell_range; cbn; lia). lia.
  Qed.

  Lemma Hng_s' : ltac2:(tb__ "0|0|
SbS2S7dSbA1S1dSdS8eVidx;A2A1S7eSbR1A2A3S2S21S22R2A1S11A3F_;Ff;").
  Proof using HF HMI Hz. intros f Hf. rewrite F_sl' in Hf. injection Hf as <-. reflexivity. Qed.

  Lemma old_cell_avoids c : ltac2:(tb__ "0|0|
S8cS4dVc;S53S8dA1A3S4S8cS4dVc;S92A3A1S96S52VL;Vc;A2A1F_;F_;").
  Proof using HC HF HMI HW0 HYA Hz.
    intros Hin' Hnew. unfold f_avoids.
    destruct (zone_image_addr f_s' L g f_am2 idx F_W' F_L' F_u' F_idx Hng_s' c Hin') as [Hown | D].
    - exfalso. apply Hnew. rewrite own_hdr_new in Hown. unfold f_newcells. apply in_app_iff in Hown. apply in_app_iff.
      destruct Hown as [K|K]; [left; exact K | right; apply in_app_iff; left; exact K].
    - exact D.
  Qed.

  Lemma footer'_cases c : ltac2:(tb__ "0|0|
S8cS4dVc;Sb4S8dA1A3S5S8cS4dVc;S9aA3S8cS4dVc;Sb4Vs;A1A3A2F_;").
  Proof using HF HMI Hz.
    intros Hin. rewrite F_s' in Hin.
    destruct (upd_footer_In s g am f_am2 F_ND F_MT c Hin) as [H|H]; [right; exact H|].
    unfold group_footer_cells in H. destruct H as [<-|H].
    - right. unfold footer_cells. apply in_flat_map. exists (g, am). split; [exact F_um|]. left. reflexivity.
    - apply in_flat_map in H as [j [Hj H]]. apply In_zseq in Hj. change (am_last f_am2) with (am_last am) in Hj.
      rewrite (F_am2_slot j) in H by lia.
      destruct (j =? idx) eqn:Eji.
      + apply Z.eqb_eq in Eji. subst j. cbn [ss_fr] in H. left. exact H.
      + right. unfold footer_cells. apply in_flat_map. exists (g, am). split; [exact F_um|]. cbn [snd].
        unfold group_footer_cells. right. apply in_flat_map. exists j. split; [apply In_zseq; lia|].
        destruct (ss_fr (nth_slot am j)) as [f|]; [|destruct H]. exact H.
  Qed.

  Lemma old_footer_avoids c : ltac2:(tb__ "0|0|
S8cS4dVc;Sb4S8dA1A3S4S8cS4dVc;S92A3A1S96S52VL;Vc;A2A1F_;F_;").
  Proof using HC HF HMI HW0 HYA Hz.
    intros Hin Hnew. unfold f_avoids.
    destruct (zone_footer_addr f_s' L g f_am2 idx F_W' F_L' F_u' F_idx Hng_s' c Hin) as [(f & Hf & Hc) | D]; [|exact D].
    exfalso. apply Hnew. rewrite F_sl' in Hf. injection Hf as <-. unfold f_newcells, f_footcells. apply in_app_iff. right. apply in_app_iff. right. exact Hc.
  Qed.

  Theorem reprP_post : ltac2:(tb__ "0|0|
Sb5VL;S8dS8fA3").
  Proof using HC HF HMI HUB HW0 HYA Hz V1 V2 V3.
    pose proof F_repr as [[HL0 [HI HR]] HF0].
    split; [split; [exact F_L'|split]|].
    - apply Forall_forall. intros c Hin'.
      destruct (in_dec mcell_eq_dec c f_newcells) as [Hnew|Hnew]; [exact (newcells_hold c Hnew)|].
      destruct (image'_cases c Hin') as [Hnew'|Hold]; [exfalso; exact (Hnew Hnew')|].
      pose proof (image'_cell_span c Hin') as [P1 P2].
      apply (cell_transfer c); [| apply (old_cell_avoids c Hin' Hnew) | exact (image_cell_w s c Hold) | exact P1 | exact P2].
      exact (proj1 (Forall_forall _ _) HI c Hold).
    -
      intros x [(rg & Hrg & Hx) Hnu].
      rewrite footprint_s' in Hrg.
      destruct F_blocks as (l1 & l2 & EB1 & EB2 & _).
      assert (M0 : f_bv0 x <> None).
      { apply HR. split; [exists rg; split; [exact Hrg | exact Hx]|].
        intros (b & Hb & Hxb). apply Hnu. exists b. split; [|exact Hxb].
        rewrite EB1. rewrite F_ub, EB2 in Hb.
        apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
      pose proof F_L as (_ & _ & _ & POS). destruct (POS rg Hrg) as [Q1 Q2]. unfold crange in Q1, Q2. cbn [fst snd] in Q1, Q2.
      destruct (Z_le_dec (f_st - 3) x) as [A|A]; [destruct (Z_lt_dec x f_e) as [B|B]|].
      + apply FBV2; [lia | unfold in_zone; lia].
      + rewrite (proj1 (FBV1 x ltac:(lia) ltac:(unfold in_zone; lia))). exact M0.
      + rewrite (proj1 (FBV1 x ltac:(lia) ltac:(unfold in_zone; lia))). exact M0.
    - apply Forall_forall. intros c Hin'.
      destruct (in_dec mcell_eq_dec c f_newcells) as [Hnew|Hnew]; [exact (newcells_hold c Hnew)|].
      destruct (footer'_cases c Hin') as [Hnew' | Hold].
      + exfalso. apply Hnew. unfold f_newcells, f_footcells. apply in_app_iff. right. apply in_app_iff. right. exact Hnew'.
      + pose proof (footer'_cell_span c Hin') as [P1 P2].
        apply (cell_transfer c); [| apply (old_footer_avoids c Hin' Hnew) | exact (footer_cells_w s c Hold) | exact P1 | exact P2].
        exact (proj1 (Forall_forall _ _) HF0 c Hold).
  Qed.

  Lemma W_place : ltac2:(tb__ "0|3|
S3S0S0S3S0S0S1S40S41R2ZdA2S43S90Z3A2M0A2S1S40S41S91Z4A2S41R2R1A2M1A2S1S5S40G1SafVC;A1A2S40SaeVC;A1R2A2A2S1S40Z1000R2A2S1S40G1Sb1VL;A1M2A2S1S42G2S44Z2Z3fA2A2S40G0S91A2A2A2A2A2A2A2Llen;A2LR;A2").
  Proof using HC HF HMI Hz.
    pose proof F_geom as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & [Hsi1 Hsi2] & (rg & Hrg & [RI1 RI2] & Erg)).
    pose proof (mig_vm HMI) as HV. pose proof (mig_ledger HMI) as HLG. cbn [ma_s ma_L] in HV, HLG.
    destruct rg as [lc len]. cbn [fst] in Erg. subst lc.
    unfold crange, loc_addr in RI1, RI2. cbn [fst snd] in RI1, RI2.
    pose proof (extent_pos _ _ _ _ _ F_G) as EP.
    assert (Hlen : 0 <= len) by (unfold IB in RI2; lia).
    pose proof (fp_mem_range C L s vm _ _ HV HLG Hrg Hlen) as (M1 & M2 & M3).
    unfold addr_of, loc_addr in M1, M2, M3.
    exists (ly_reg L (prid (am_mem am)) + 0), len.
    assert (X3 : f_e <= f_zm + group_extent am) by (unfold group_extent, ms_stride, UNIT, IB in *; lia).
    pose proof F_fit as Fit. pose proof F_n as Hn. unfold ms_stride in *.
    clear Hsi2 EZ.
    unfold UNIT, IB, PGSZ in *.
    top_ranges.
    repeat split; lia.
  Qed.

  Lemma written_not_static x lo n0 : ltac2:(tb__ "0|1|
S1S40SafVC;A1Vlo;A2S40S41Vlo;Vn0;A2M0SaeVC;A1A2A2S1S40Vlo;Vx;A2S42Vx;G0A2A2S1S1S40Z0Vx;A2S42Vx;S44Z2Z40A2A2A2S4S95Vx;A1A1A2F_;F_;").
  Proof using HC HF HMI HS Hz.
    intros Hlo Hx. pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta delta [CTX_SIZE PGSZ UNIT] in HS0.
    destruct HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpg & Hceil).
    destruct W_place as (R & len & P1 & P2 & P3 & P4 & P5 & P6 & P7).
    unfold in_zone. unfold PGSZ, UNIT in Hpg, Hceil.
    split; [lia|]. lia.
  Qed.

  Lemma statics_post : ltac2:(tb__ "0|0|
Sb0VC;S98S8fA3").
  Proof using HC HF HMI HS Hz V1.
    pose proof (mig_statics HMI) as ST. cbn [ma_s ma_L] in ST. fold f_rv0 f_bv0 in ST.
    pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta delta [CTX_SIZE PGSZ UNIT] in HS0.
    destruct HS0 as (Ilibc & Irep & Isc & Ismall & Imed & Ictz & Igot & Iguard & Ilock & Ictx & Ierr & Hpg & Hceil).
    assert (RV : forall lo n0, mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> forall x, lo <= x < lo + n0 -> f_rv1 x = f_rv0 x /\ f_bv1 x = f_bv0 x).
    { intros lo n0 Hlo x Hx. destruct (written_not_static x lo n0 Hlo Hx) as (X1 & X2).
      destruct (FBV1 x X1 X2) as [B R]. auto. }
    assert (HR : forall a0 w v lo n0, holds f_rv0 a0 w v -> mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> lo <= a0 -> a0 + Z.of_nat w <= lo + n0 -> holds f_rv1 a0 w v).
    { intros a0 w v lo n0 Hh Hlo Ha Hw j Hj. rewrite (proj1 (RV lo n0 Hlo (a0 + Z.of_nat j) ltac:(lia))). exact (Hh j Hj). }
    assert (HB : forall a0 w v lo n0, holds f_bv0 a0 w v -> mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> lo <= a0 -> a0 + Z.of_nat w <= lo + n0 -> holds f_bv1 a0 w v).
    { intros a0 w v lo n0 Hh Hlo Ha Hw j Hj. rewrite (proj2 (RV lo n0 Hlo (a0 + Z.of_nat j) ltac:(lia))). exact (Hh j Hj). }
    destruct ST as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & (gd & T9 & T10)).
    unfold statics_ok, mc_need_locks, mc_page_size in *.
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
    - apply (HR _ _ _ _ _ T10 Iguard); cbn; lia.
  Qed.

  Lemma F_init : st_init_done s = true.
  Proof using HF HMI.
    destruct (st_init_done s) eqn:E; [reflexivity|]. exfalso.
    destruct (inv_ctx F_I) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinit & _).
    destruct (Hinit E) as (Hm & _). pose proof F_MT as M. unfold MT in M. rewrite Hm in M. cbn in M. discriminate.
  Qed.

  Hypothesis HRCH : reach_ok f_s'.

  Theorem minv_post : ltac2:(tb__ "0|0|
Sc8VC;Sc7S8dVL;A2Vrd1;Vwok1;Vvm;A5").
  Proof using HC HF HMI HRCH HS HUB HW0 HYA Hz V1 V2 V3.
    pose proof (mig_bounded HMI) as HB. pose proof (mig_ctx HMI) as HC0. pose proof (mig_vm HMI) as HV.
    pose proof (mig_ledger HMI) as HLG. pose proof (mig_img HMI) as HIMG. pose proof (mig_maps HMI) as HMW.
    cbn [ma_s ma_L] in HB, HC0, HV, HLG, HIMG, HMW.
    split; [exact F_W'|]. split; [rewrite F_s'; exact HB|]. split; [exact HC0|].
    split; [exact reprP_post|]. split; [rewrite F_s'; exact HV|]. split; [exact statics_post|].
    split; [|split; [exact HLG|]; split; [exact HIMG|]; split; [exact HMW | exact HRCH]].
    cbn [ma_s]. rewrite F_s'. change (st_init_done (upd_meta g (MUsed f_am2) s)) with (st_init_done s).
    rewrite F_init. discriminate.
  Qed.

  Theorem slot_owned x : ltac2:(tb__ "0|0|
S1S40S43S90Z4A2Vx;A2S42Vx;S91A2A2S6dVL;Vs;Vx;A3F_;").
  Proof using HC HF HMI HUB HW0 HYA Hz.
    intros Hx. pose proof F_geom as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & [Hsi1 Hsi2] & (rg & Hrg & [RI1 RI2] & Erg)).
    split.
    - exists rg. split; [exact Hrg|]. unfold crange in RI1, RI2. cbn [fst snd] in RI1, RI2.
      unfold group_extent, ms_stride, UNIT, IB in *. lia.
    - intros ([q m] & Hb & Hxb). cbn [fst snd] in Hxb.
      destruct F_blocks as (l1 & l2 & EB1 & EB2 & NI).
      assert (Hb' : In (q, m) (user_blocks f_s')).
      { rewrite EB1. rewrite F_ub, EB2 in Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
      destruct (Z.eq_dec x (f_st - 4)) as [->|Hne].
      +
        pose proof (image_outside_user_blocks f_s' L f_Ccheck (q, m) F_W' F_L' Ccheck_in' Hb') as D.
        unfold ranges_disjoint, cell_range, block_range, f_Ccheck in D. cbn [mc_loc mc_w fst snd Z.of_nat] in D.
        unfold f_st, addr_of in D, Hxb. unfold loc_addr in D. destruct (slot_start am idx) as [r o]. cbn [padd] in D.
        unfold addr_of, loc_addr in Hxb. cbn in Hxb. cbn in D. lia.
      + destruct (zone_block_addr f_s' L g f_am2 idx F_W' F_L' F_u' F_idx Hng_s' q m Hb') as [(f & Hf & Eq & _) | D].
        * rewrite F_sl' in Hf. injection Hf as <-. apply NI. rewrite <- F_ub. apply in_map_iff. exists (q, m). split; [|exact Hb].
          cbn [fst]. rewrite Eq. reflexivity.
        * change (zone_range L f_am2 idx) with (zone_range L am idx) in D. rewrite EZ in D.
          unfold ranges_disjoint, block_range in D. cbn [fst snd] in D. unfold UNIT, IB in *. lia.
  Qed.

  Lemma meta_cells_old : ltac2:(tb__ "0|3|
S1S8cS4dS4fS4eS8Vg;S67A2A1U8M0S6aS19Vam;A1A1A3S53Vs;A1M1A3S1S8cS4dS4fS4eS8Vg;S64A2A1U4M2S50S12Vam;A1A1A3G1A3S1S8cS4dS4fS4eS8Vg;S66A2A1G2S50S2eVam;A1A1A3G1A3S1S8cS4dS4fS4eS8Vg;S65A2A1G0S50S76Vam;A1A1A3G1A3S1S8cS4dS4fS4eS8Vg;S69A2A1G0S61S30Vam;A1A1A3G1A3S8cS4dS4fS4eS8Vg;S68A2A1G0S61S2fVam;A1A1A3G1A3A2A2A2A2A2").
  Proof using HF HMI Hz.
    assert (K : forall c, In c (meta_slot_cells g (Some (MUsed am))) -> In c (image s)).
    { intros c Hc. exact (meta_cells_in_image_gen s g am c (inv_keys F_I) F_MT Hc). }
    unfold meta_slot_cells in K. repeat split; apply K; cbn; tauto.
  Qed.
End Gap.
