(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "PGSZ"; "mslot"; "region"; "st_areas"; "brkst"; "st_brk"; "st_metas"; "padd"; "st_area_head"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_regions"; "st_seq"; "st_active"; "st_area_tail"; "st_avail_meta"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_avail_meta_count"; "st_bounces"; "st_free_meta_head"; "st_unmap_seq"; "st_usage"; "BrkCur"; "BrkDead"; "META_SIZE"; "MRaw"; "SP"; "astate"; "rg_len"; "st_init_done"; "AREA_HDR"; "METAS_PER_AREA"; "RkBrk"; "lupd"; "rg_kind"; "rg_live"; "rkind"; "MFree"; "RkMap"; "alloc_meta"; "ameta"; "mkRegion"; "mupdate"; "set_avail_meta"; "set_avail_meta_area_count"; "set_avail_meta_areas"; "set_avail_meta_count"; "set_brk"; "set_regions"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.BRK"; "tB"; "pz"; "bp"; "bm"; "rg0"; "tBpre"; "vmB"; "rgB"; "C_tn"; "rr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LCtx"; "MCell"; "loc"; "VZ"; "ctx_cells"; "footprint"; "region_of"; "MT"; "image"; "keys"; "mc_loc"; "sval"; "Inv"; "LMem"; "VP"; "loc_addr"; "user_blocks"; "CTX_brk"; "area_cells"; "ly_reg"; "optr"; "CTX_avail_meta_areas"; "CTX_seq"; "mc_w"; "usedX"; "CTX_active"; "CTX_avail_meta"; "CTX_avail_meta_area_count"; "CTX_avail_meta_count"; "CTX_free_meta_head"; "CTX_init_done"; "CTX_meta_alloc_shift"; "CTX_meta_area_head"; "CTX_meta_area_tail"; "CTX_mmap_counter"; "CTX_secret"; "VSec"; "brk_regions"; "ly_brk0"; "ly_ctx"; "memb"; "yields"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.DEAD"; "sd"; "C_brkD"; "@Corelib.Init.Datatypes"; "list"; "cons"; "prod"; "bool"; "option"; "Some"; "app"; "None"; "nat"; "nil"; "true"; "pair"; "snd"; "fst"; "false"; "andb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "modulo"; "of_nat"; "sub"; "eqb"; "pow"; "@Stdlib.Lists.List"; "In"; "incl"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "wz"; "vm_ok"; "blocks"; "topL"; "addr_of"; "img_reserved"; "ledger_ok"; "mc_ctx"; "mc_img_hi"; "mc_img_lo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "vm_reserved"; "vm_maps"; "vm_start_brk"; "mkVmMapsFull"; "vm_brk"; "vm_init_sp"; "vm_limit"; "vm_mmap_base"; "vm_noaccess"; "@Corelib.Init.Peano"; "lt"; "le"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk"; "SC13"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost"; "am_spec_post"; "r_RES"; "s0"; "s_BKok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta"; "am_frame"; "open_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame MallocWfRings MallocWfRepr MallocWfMeta MallocWfGeom
  MallocWfSurgery MallocFooter MallocFooterLemmas MallocLayout MallocIface MallocIfaceI MallocLaws FpLaws WalkArith RingFacts Zones2
  AllocMetaPost AllocMetaImage AllocMetaGrow AllocMetaArea MapsWf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac in_list := solve [ cbn; repeat first [ left; reflexivity | right ] ].

Section BRK.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (t : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S51VX;VR;VU;Vt;A4").
  Hypothesis HX : xraw X t.
  Hypothesis Hhd : st_free_meta_head t = None.
  Hypothesis Hcnt : st_avail_meta_count t = 0.
  Hypothesis Hac : st_avail_meta_area_count t = 0.
  Hypothesis Hinit : st_init_done t = true.
  Variables (rb : nat) (pb : Z).
  Hypothesis Hbrk : ltac2:(tb__ "0|0|
S0ScSdVt;A1S1fVrb;Vpb;A2A3").
  Hypothesis HL : layout_ok L t.

  Definition rr : nat := length (st_regions t).
  Definition bp : sptr := bk_p rb pb.
  Definition bm : sptr := padd bp AREA_HDR.
  Definition tB : astate := ltac2:(tb__ "0|0|
SaaVt;Vrb;Vpb;A3").
  Definition rg0 : region := bk_rg t rb.
  Definition rgB : region := ltac2:(tb__ "0|0|
S32S29S82S25S3eA1S8A2S7aS6A1S7bA4").

  Lemma s0_t : s0 t = t.
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit. unfold s0. destruct t; cbn in *. rewrite Hinit. reflexivity. Qed.

  Lemma bk_facts : ltac2:(tb__ "0|1|
S1S0S71S79A1S6aVt;A1S72S79Vrb;S7aS79A1A3A3S1S0S75SaA1S4bVt;Vrb;A2S76SaS3eA2A3S1S0S2dS2bS3eA1S29A3S1S0S74S2cS3eA1S7bA3S1S0S6S25S3eA1S84S8Vpb;A2M0A3S1S81Z2Vpb;A2S1Sa3Vrb;S43A2S0S7S3cS23Vrb;G0A2A3A2A2A2A2A2A2A2").
  Proof using HI Hbrk.
    pose proof (inv_areas HI) as (_ & _ & _ & _ & _ & _ & A7 & _). rewrite Hbrk in A7.
    destruct A7 as (Hbr & rg & Hr & Hl & Hlen & Hpb).
    assert (Erg : rg0 = rg).
    { unfold rg0, bk_rg. unfold region_of in Hr. destruct (nth_error (st_regions t) rb) as [x|] eqn:E; [|discriminate]. injection Hr as ->. exact (nth_error_nth _ _ _ E). }
    destruct (brk_regions_In t rb ltac:(rewrite Hbr; left; reflexivity)) as (rg' & Hr' & Hk'). rewrite Hr in Hr'. injection Hr' as <-.
    rewrite Erg. repeat split; try assumption. unfold rr. exact (region_of_lt _ _ _ Hr).
  Qed.

  Lemma SPECB : ltac2:(tb__ "0|0|
Sa7VX;VR;VU;Vt;S7cS75S7A1S24S76S7S3dA2S3aA4A5").
  Proof using HI Hac Hbrk Hcnt Hhd.
    pose proof (yields_BK t Hhd Hcnt Hac rb pb Hbrk 1 0 0) as Y. unfold r_BK in Y. cbn [Z.eqb] in Y.
    exact (am_spec_of_yields X R U t HI _ _ Y).
  Qed.
  Lemma HIB : ltac2:(tb__ "0|0|
S51S72S7S3dVX;A3VR;VU;S3aA4"). Proof using HI Hac Hbrk Hcnt Hhd. exact (proj1 SPECB). Qed.

  Lemma tB_fields : ltac2:(tb__ "0|4|
S1S0S71SaA1S13S3aA1S2aSaS13Vt;A1Vrb;S41A4A3S1S0S71S7A1SbS3aA1S77S7SbVt;A1S72S7S3cS7aS7A1A3A3A3S1S0S71S73S7S9A2A1SeS3aA1S33SeVt;A1S3dS22A3A3S1S0ScSdS3aA1S1fVrb;S82Vpb;Z1M0A2A2A3S1S0S74S26S3aA1S7bA3S1S0S75S7A1M1S1cS3aA1S78S7A1A3S1S0S7S17S3aA1SfS3dS21A2A3S1S0S6S1aS3aA1S87S28G0A2A3S1S0S6S18S3aA1Z0A3S1S0S6S11S3aA1S11Vt;A1A3S1S0G1S10S3aA1G1G1Lx;S10Vt;A1S7S76S7R1A2Ls;S76S7S3cA2M2X75x2A3S1S0G1S16S3aA1G2A3S1S0S7S19S3aA1SfS3cZ1000A2A3S1S0S71G1A1S15S3aA1S15Vt;A1A3S1S0S71S6A1M3S1eS3aA1S1eVt;A1A3S1S0G3S1dS3aA1S1dVt;A1A3S1S0G3S1bS3aA1S1bVt;A1A3S1S0S6S14S3aA1S14Vt;A1A3S0S6S12S3aA1S12Vt;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    unfold tB, s_BKok, take, open_st, rgB, rg0, bm, bp. rewrite s0_t. cbn -[Z.mul Z.add Z.sub Z.shiftl padd METAS_PER_AREA bk_p bk_rg].
    repeat split; try reflexivity; assumption.
  Qed.

  Lemma region_of_tB k : ltac2:(tb__ "0|1|
S0S75SaA1M0S4bS3aVk;A2S74G0L_;Sb0Vk;Vrb;A2S76SaS41A2S4bVt;Vk;A2X74x2A3").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof tB_fields as (F1 & _). pose proof bk_facts as (_ & Hr & _ & _ & _ & _ & LT & _). unfold region_of. rewrite F1.
    rewrite nth_error_lupd. unfold rr in LT. replace (Nat.ltb rb (length (st_regions t))) with true by (symmetry; apply Nat.ltb_lt; exact LT).
    rewrite Bool.andb_true_r. reflexivity.
  Qed.

  Definition C_tn : mcell := ltac2:(tb__ "0|0|
S46S52SfS8cS7SbVt;A1S23U0Z0A2A3Z8A2A1U8S53S3cA1A3").

  Lemma bm_prid : prid bm = rb. Proof using HI Hbrk. pose proof bk_facts as (_ & _ & _ & _ & _ & _ & _ & E). unfold bm. rewrite E. reflexivity. Qed.

  Lemma fresh_slot j : ltac2:(tb__ "0|0|
S81Z0Vj;A2S0S75S9A1S4cVt;SfS3cS82S27S84S21Vj;A2A2A2A2S78S9A1A3F_;").
  Proof using HI Hbrk.
    intros Hj. pose proof bk_facts as (Hbr & Hr & Hk & Hl & Hlen & Hpb & LT & Ebp).
    destruct (MT t (padd bp (AREA_HDR + META_SIZE * j))) as [x|] eqn:E; [|reflexivity]. exfalso.
    pose proof (MT_Some_In_keys _ _ _ E) as Kq.
    destruct (key_area X R U t HI _ Kq) as (a0 & k0 & Ha0 & Hk0 & Eq).
    pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a0 Ha0) as (r' & o' & rg' & Ea0 & Ho' & Ho'2 & Hr' & Hl' & Hlen' & KIND).
    rewrite Ebp, Ea0 in Eq. cbn [padd] in Eq. injection Eq as Er Eo. subst r'.
    rewrite Hr in Hr'. injection Hr' as <-. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
    clear - Hj Hk0 Eo Ho' Hlen' Hlen Hpb. Z.to_euclidean_division_equations. nia.
  Qed.
  Lemma bp_fresh : ltac2:(tb__ "0|0|
S3S8aS7S3cSbVt;A1A3A1").
  Proof using HI Hbrk.
    intros Hin. pose proof bk_facts as (Hbr & Hr & Hk & Hl & Hlen & Hpb & LT & Ebp).
    pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK bp Hin) as (r' & o' & rg' & Ea0 & _ & _ & Hr' & _ & Hlen' & _).
    rewrite Ebp in Ea0. injection Ea0 as <- <-. rewrite Hr in Hr'. injection Hr' as <-. unfold PGSZ in *. lia.
  Qed.

  Definition tBpre : astate := ltac2:(tb__ "0|1|
S34SfS3dS21A2S37S87S28Z1M0A2SaeS3cS38S1fVrb;S82Vpb;G0A2A2S36S3cS35G0S39S2aSaS13Vt;A1Vrb;S41A4Vt;A2A2A2A2A2A2A2").
  Lemma tB_upd : ltac2:(tb__ "0|0|
S0S24S3aSacS3dS22S3fA3A3").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit. unfold tB, s_BKok, take, open_st, tBpre, rgB, rg0, bm, bp. rewrite s0_t. reflexivity. Qed.
  Lemma tBpre_fields : ltac2:(tb__ "0|0|
S1S0S71S73S7S9A2A1SeS3fA1SeVt;A1A3S1S0S71S7A1SbS3fA1S77S7SbVt;A1S72S7S3cS7aS7A1A3A3A3S0S71S44A1S49S3fA1S49S3aA1A3A2A2").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit. rewrite tB_upd. repeat split; reflexivity. Qed.
  Lemma bm_fresh : ltac2:(tb__ "0|0|
S0S75S9A1S4cVt;S3dA2S78S9A1A3").
  Proof using HI Hbrk. unfold bm. replace AREA_HDR with (AREA_HDR + META_SIZE * 0) by lia. apply fresh_slot. lia. Qed.

  Lemma area_cells_tB : ltac2:(tb__ "0|1|
S0S71S44A1S57S3aS3cS78S7A1M0A3S57Vt;S3cG0A3A3").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof tB_fields as (_ & _ & F3 & _).
    assert (E : forall k, meta_slot_cells (padd bp (AREA_HDR + META_SIZE * Z.of_nat k)) (mlookup (st_metas tB) (padd bp (AREA_HDR + META_SIZE * Z.of_nat k)))
                        = meta_slot_cells (padd bp (AREA_HDR + META_SIZE * Z.of_nat k)) (mlookup (st_metas t) (padd bp (AREA_HDR + META_SIZE * Z.of_nat k)))).
    { intros k. rewrite F3. rewrite mlookup_mupdate.
      pose proof (fresh_slot (Z.of_nat k) ltac:(lia)) as FR. unfold MT in FR. rewrite FR.
      destruct (sptr_eqb _ _); [apply meta_slot_cells_raw | reflexivity]. }
    unfold area_cells. f_equal.
    induction (seq 0 (Z.to_nat METAS_PER_AREA)) as [|k l IH]; [reflexivity|]. cbn [flat_map]. rewrite (E k), IH. reflexivity.
  Qed.

  Theorem image_tB c : ltac2:(tb__ "0|0|
S8aS44Vc;S77S44S4dS3aA1S8dS3aA1A3A3S2S8aS44Vc;S49S3aA1A3S2S1S3S0S71S7A1SbVt;A1S7aS7A1A3A1S0S44Vc;S42A3A2S2S8aS44Vc;S57S3aS3cS78S7A1A3A3S1S8aS44Vc;S77S44S4dVt;A1S8dVt;A1A3A3S4S7S7S0S47S4fVc;A1S52R1A1A3Lq;A2A2A2A2A2F_;").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof tBpre_fields as (P1 & P2 & P3).
    assert (NU : nonused (MT tBpre bm)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) bm) with (MT t bm); rewrite bm_fresh; exact I).
    intros Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite tB_upd in Hin. destruct (uf_image_In tBpre bm MRaw NU I c Hin) as [H|H].
      + unfold image in H. apply in_app_iff in H as [H|H]; [left; rewrite <- P3; exact H|].
        rewrite P2, (co_areas_cells t tBpre P1), (co_used_metas t tBpre P1) in H.
        apply in_app_iff in H as [H|H].
        * destruct (ap_areas_cells_In t t bp eq_refl (st_areas t) c H) as [Ho|[Htn|Hnew]].
          -- right; right; right. apply (old_noctx_loc X R U t HI HX). left. apply in_app_iff. left. exact Ho.
          -- right; left. exact Htn.
          -- right; right; left. rewrite area_cells_tB. exact Hnew.
        * right; right; right. apply (old_noctx_loc X R U t HI HX). left. apply in_app_iff. right. exact H.
      + right; right; left. rewrite area_cells_tB. unfold area_cells. apply in_app_iff. right.
        apply in_flat_map. exists 0%nat. split; [apply in_seq; unfold METAS_PER_AREA; lia|].
        replace (padd bp (AREA_HDR + META_SIZE * Z.of_nat 0)) with bm by (unfold bm; f_equal).
        change (mlookup (st_metas t) bm) with (MT t bm). rewrite bm_fresh. rewrite meta_slot_cells_raw in H. exact H.
    - right; right; right. apply (old_noctx_loc X R U t HI HX). right.
      rewrite tB_upd, (uf_footers tBpre bm MRaw NU I), (co_footers t tBpre P1) in Hin. exact Hin.
  Qed.

  Lemma ctx_cells_tBC c : ltac2:(tb__ "0|1|
S8aS44Vc;S49S3aA1A3S2S4S6S6S4S79S79S4S50S50S1S0S44Vc;S46S45R3A1R2R1A3A3S1Sa3U0R2A2S2S1S81Z0R3A2S81S82R3S86R2A1A2M0ZcA2A2S2S1S81Z10R3A2S81G0Z50A2A2S1S81Z398R3A2S81G0Z3a0A2A2A2A2A2A2Lval;A2Lw;A2Lo;A2S1S8aS44Vc;S49Vt;A1A3S3S0S47S4fVc;A1S45S5aA1A3A1A2A2F_;").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    intros Hin.
    pose proof tB_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
    unfold ctx_cells in Hin. rewrite F2, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19 in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    - cbn [In] in Hin.
      unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
        CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in *.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
        first [ left; eexists _, _, _; (split; [reflexivity|]); (split; [cbn; lia | cbn; lia])
              | right; (split; [unfold ctx_cells; apply in_app_iff; left; rewrite ?Hinit; in_list | cbn [mc_loc]; intros E; injection E as E'; lia]) ].
    - right. split; [unfold ctx_cells; apply in_app_iff; right; exact Hin|].
      destruct (ctx_maps_loc _ c Hin) as (o & -> & Ho). unfold CTX_active, CTX_avail_meta_areas in *. intros E. injection E as E'. lia.
  Qed.

  Lemma fp_tB e : ltac2:(tb__ "0|1|
S5S8aS73S47S6A2M0Ve;S4aS3aA1A3S2S8aG0Ve;S4aVt;A1A3S0G0Ve;S7cS47S6S52S3cA1S8A4A3A2A2").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof tB_fields as (F1 & F2 & _). pose proof bk_facts as (_ & Hr & Hk & _). rewrite !In_footprint, F2.
    rewrite (map_fp_regions_only (set_regions (lupd (st_regions t) rb rgB) t) tB) by (rewrite F1; reflexivity).
    rewrite (map_fp_upd_nonmap t rb rg0 rgB Hr) by (cbn; rewrite ?Hk; discriminate).
    rewrite map_app, in_app_iff. cbn [map In]. intuition congruence.
  Qed.
  Lemma ub_tB : ltac2:(tb__ "0|0|
S0S71S73S7S6A2A1S55S3aA1S55Vt;A1A3").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof tBpre_fields as (P1 & _).
    assert (NU : nonused (MT tBpre bm)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) bm) with (MT t bm); rewrite bm_fresh; exact I).
    rewrite tB_upd, (uf_user_blocks tBpre bm MRaw NU I). exact (co_user_blocks t tBpre P1).
  Qed.
  Lemma footers_tB : ltac2:(tb__ "0|0|
S0S71S44A1S8dS3aA1S8dVt;A1A3").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof tBpre_fields as (P1 & _).
    assert (NU : nonused (MT tBpre bm)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) bm) with (MT t bm); rewrite bm_fresh; exact I).
    rewrite tB_upd, (uf_footers tBpre bm MRaw NU I). exact (co_footers t tBpre P1).
  Qed.

  Variables (C : mconsts) (vm : VmMaps).
  Hypothesis Hctx : ltac2:(tb__ "0|0|
S0S6S6cVL;A1S97VC;A1A3").
  Hypothesis HSI : statics_in_image C.
  Hypothesis HV : ltac2:(tb__ "0|0|
S91VL;Vt;Vvm;A3").
  Hypothesis HLG : ledger_ok C vm.
  Hypothesis HIR : img_reserved C vm.
  Hypothesis HB : bounded t.
  Hypothesis HMW : maps_wf vm.

  Definition pz : Z := ltac2:(tb__ "0|0|
S82S58VL;Vrb;A2S84S8Vpb;A2A2").

  Hypothesis HG_ceil : ltac2:(tb__ "0|0|
S81S82S3bS8A2S93VL;A1A2").
  Hypothesis HG_free : ltac2:(tb__ "0|4|
S73S8fQ40M0A1M1G1A2M2S8aG2R1S77G2S9aVvm;A1S9bVvm;A1A3A3S2S81S82S8eG0S7eG1G1R2A3A2M3S8eG0S7dG1G1R2A3A2A2S3bA2S81S82S3bS8A2G3A2A2F_;Fe;").

  Definition vmB : VmMaps := ltac2:(tb__ "0|1|
S9dS9aVvm;A1S72S73S8fQ40A1M0G0A2S7cG0G0S90S3bA1S90S8A1A4S9bVvm;A1A3Sa2Vvm;A1S9cVvm;A1S90S82S3bS8A2A1Sa0Vvm;A1Sa1Vvm;A1S9fVvm;A1A8").

  Lemma pz_eq : ltac2:(tb__ "0|0|
S0S6S54VL;S52S3cA1A2S3bA3").
  Proof using HI Hbrk. pose proof bk_facts as (_ & _ & _ & _ & _ & _ & _ & E). unfold pz. rewrite E. reflexivity. Qed.
  Lemma bm_addr : ltac2:(tb__ "0|0|
S0S6S94VL;S3dA2S82S3bS27A2A3").
  Proof using HI Hbrk. pose proof bk_facts as (_ & _ & _ & _ & _ & _ & _ & E). unfold addr_of, bm, pz. rewrite E. cbn [padd loc_addr prid poff]. lia. Qed.
  Lemma brk_facts : ltac2:(tb__ "0|5|
S1S0S6S58VL;Vrb;A2M0S6bVL;A1M1A3S1S0S6S8eQ40M2S9eVvm;A1A2S3bA3S1S0S6S8eG2S9cVvm;A1A2G1A3S1S81S8G0A2S1S0S6S85G0S8A2Z0M3A3S1S0S6S85S3bS8A2G3A3S1S81S84Z2M4S8A2S3bA2S1S81S82S3bS8A2S93VL;A1A2S1S81G3S3bA2S83S3bS89G4Z40A2A2A2A2A2A2A2A2A2A2A2").
  Proof using HG_ceil HI HL HV Hbrk.
    pose proof bk_facts as (Hbr & Hr & Hk & Hl & Hlen & Hpb & LT & Ebp). pose proof HV as (_ & _ & V3 & _ & _ & _ & _ & X4 & _). rewrite Hbrk in V3.
    destruct V3 as (E0 & Eb & Es & _). destruct (X4 rb rg0 Hr Hl) as [B1 B2]. pose proof HL as (_ & Halign & _). pose proof (Halign rb rg0 Hr Hl) as AL.
    assert (M1 : PGSZ * 2 <= PGSZ * pb) by (apply Z.mul_le_mono_nonneg_l; unfold PGSZ; lia).
    assert (PZ : pz mod PGSZ = 0) by (unfold pz; rewrite Z.add_mod, AL, Z.mul_comm, Z.mod_mul by (unfold PGSZ; lia); reflexivity).
    top_ranges. unfold pz in *. unfold PGSZ in *. repeat split; try assumption; lia.
  Qed.

  Lemma page_vs_image x : ltac2:(tb__ "0|0|
S1S81S99VC;A1Vx;A2S83Vx;S98VC;A1A2A2S3S1S81S3bVx;A2S83Vx;S82S3bS8A2A2A2A1F_;").
  Proof using HG_free HIR.
    intros Hx Hin. destruct (HIR x Hx) as (e & He & Hex). pose proof (HG_free e ltac:(apply in_app_iff; left; exact He)). lia.
  Qed.

  Lemma page_vs_footprint e x : ltac2:(tb__ "0|1|
S8aS73S47S6A2Ve;S4aVt;A1A3S1S81S54VL;S7eS47S6Ve;A3A2M0Vx;A2S83Vx;S82G0S7dS47S6Ve;A3A2A2A2S3S1S81S3bVx;A2S83Vx;S82S3bS8A2A2A2A1F_;F_;").
  Proof using HG_free HIR HSI HV Hctx.
    intros He Hx Hin. pose proof HV as (_ & _ & _ & V5 & _).
    destruct e as [[o|q] n].
    -   pose proof HSI as (_&_&_&_&_&_&_&_&_& [C1 C2] &_). cbn [fst snd loc_addr] in Hx.
      unfold footprint in He. destruct He as [E|He].
      + injection E as <- <-. apply (page_vs_image x); [rewrite Hctx in Hx; lia | exact Hin].
      + apply in_app_iff in He as [He|He]; [apply in_map_iff in He as (? & E & _); discriminate|].
        apply in_flat_map in He as (k & _ & He). destruct (region_of t k) as [rg|]; [|destruct He]. destruct (rg_kind rg); try destruct He.
        destruct (rg_live rg); [destruct He as [E|[]]; discriminate | destruct He].
    - cbn [fst snd] in Hx. destruct (V5 q n He) as (e' & He' & R1' & R2').
      pose proof (HG_free e' ltac:(apply in_app_iff; right; exact He')). unfold addr_of in *. destruct q as [r o]. cbn [loc_addr padd prid poff] in *. lia.
  Qed.
  Lemma fp_size e : ltac2:(tb__ "0|0|
S8aS73S47S6A2Ve;S4aVt;A1A3S83Z0S7dS47S6Ve;A3A2F_;").
  Proof using HV. exact (AllocMetaArea.fp_size t L vm HV e). Qed.
  Lemma map_region_vs_page k rg x : ltac2:(tb__ "0|1|
S0S75SaA1S4bVt;Vk;A2S76SaVrg;A2A3S0S74S2cVrg;A1S7bA3S0S2dS2bVrg;A1S2fA3S1S81S58VL;Vk;A2M0Vx;A2S83Vx;S82G0S25Vrg;A1A2A2A2S3S1S81S3bVx;A2S83Vx;S82S3bS8A2A2A2A1F_;F_;F_;F_;").
  Proof using HG_free HIR HSI HV Hctx.
    intros Hk Hl Hkd Hx. apply (page_vs_footprint (LMem (SP k 0), rg_len rg) x (footprint_region_In t k rg Hk Hkd Hl)).
    cbn [fst snd loc_addr]. lia.
  Qed.

  Theorem layout_ok_tB : layout_ok L tB.
  Proof using HG_ceil HG_free HI HIR HL HSI HV HX Hac Hbrk Hcnt Hctx Hhd Hinit.
    pose proof HL as (A & B & Cc & D). pose proof bk_facts as (Hbr & Hr & Hk & Hl & _). pose proof brk_facts as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
    split; [exact A|]. split.
    { intros k rg Hk' Hl'. rewrite region_of_tB in Hk'. destruct (Nat.eqb k rb) eqn:E; [apply Nat.eqb_eq in E; subst k; exact (B rb rg0 Hr Hl) | exact (B k rg Hk' Hl')]. }
    pose proof tB_fields as (F1 & F2 & _).
    assert (NEWR : crange L (LMem bp, PGSZ) = (pz, PGSZ)) by (unfold crange; cbn [fst snd]; rewrite pz_eq; reflexivity).
    assert (DISJ : forall e, In e (footprint t) -> ranges_disjoint (crange L e) (crange L (LMem bp, PGSZ)) /\ ranges_disjoint (crange L (LMem bp, PGSZ)) (crange L e)).
    { intros e He. rewrite NEWR. unfold ranges_disjoint, crange. cbn [fst snd]. pose proof (fp_size e He) as SZ.
      destruct (Z_le_dec (loc_addr L (fst e) + snd e) pz); [lia|].
      destruct (Z_le_dec (pz + PGSZ) (loc_addr L (fst e))); [lia|]. exfalso.
      destruct (Z_le_dec (loc_addr L (fst e)) pz).
      - apply (page_vs_footprint e pz He); unfold PGSZ in *; lia.
      - apply (page_vs_footprint e (loc_addr L (fst e)) He); unfold PGSZ in *; lia. }
    assert (FP2 : footprint tB = ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ (LMem bp, PGSZ) :: map_fp t).
    { rewrite footprint_eq, F2, map_app. rewrite (map_fp_regions_only (set_regions (lupd (st_regions t) rb rgB) t) tB) by (rewrite F1; reflexivity).
      rewrite (map_fp_upd_nonmap t rb rg0 rgB Hr) by (cbn; rewrite ?Hk; discriminate). cbn [map]. rewrite <- app_assoc. reflexivity. }
    assert (FP0 : footprint t = ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ map_fp t) by (rewrite footprint_eq; reflexivity).
    split.
    - rewrite FP2, map_app.
      change (map (crange L) ((LMem bp, PGSZ) :: map_fp t)) with (crange L (LMem bp, PGSZ) :: map (crange L) (map_fp t)).
      assert (EQ0 : map (crange L) ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ map (crange L) (map_fp t) = map (crange L) (footprint t)).
      { rewrite FP0, map_app. reflexivity. }
      apply pairwise_insert.
      + rewrite EQ0. exact Cc.
      + intros y Hy. rewrite EQ0 in Hy. apply in_map_iff in Hy as (e & <- & He). split; [apply (proj2 (DISJ e He)) | apply (proj1 (DISJ e He))].
    - intros rg Hrg. apply fp_tB in Hrg as [Hrg| ->]; [exact (D rg Hrg)|]. rewrite NEWR. cbn [fst snd]. top_ranges. unfold PGSZ in *. lia.
  Qed.

  Lemma u_pz : ltac2:(tb__ "0|0|
S0S6S8eQ40S90S3bA1A2S3bA3"). Proof using HG_ceil HI HL HV Hbrk. pose proof brk_facts as (_ & _ & _ & _ & _ & _ & _ & _ & R9). unfold wz. apply u64. exact R9. Qed.
  Lemma u_pgsz : ltac2:(tb__ "0|0|
S0S6S8eQ40S90S8A1A2S8A3"). Proof using . reflexivity. Qed.
  Lemma u_brk : ltac2:(tb__ "0|1|
S0S6S8eQ40S90S82S3bS8A2M0A1A2G0A3").
  Proof using HG_ceil HI HL HV Hbrk. pose proof brk_facts as (_ & _ & _ & _ & _ & _ & _ & R8 & R9). unfold wz. apply u64. top_ranges. unfold PGSZ in *. lia. Qed.

  Theorem vm_ok_tB : ltac2:(tb__ "0|0|
S91VL;S3aS40A3").
  Proof using HG_ceil HG_free HI HL HV HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof HV as (V1 & V2 & V3 & V5 & X1 & X2 & X3 & X4 & V9 & V10 & V11). pose proof bk_facts as (Hbr & Hr & Hk & Hl & Hlen & Hpb & LT & Ebp).
    pose proof brk_facts as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9). pose proof tB_fields as (F1 & F2 & F3 & F4 & _).
    rewrite Hbrk in V3. destruct V3 as (E0 & Eb & Es & Epages). rewrite Hbrk in V10.
    unfold vm_ok. rewrite F4. cbn [vmB vm_maps vm_noaccess vm_brk vm_start_brk].
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|   exact V11]]]]]]]]]].
    - intros k rg Hk' Hl' Hkd. rewrite region_of_tB in Hk'. destruct (Nat.eqb k rb) eqn:E; [injection Hk' as <-; cbn in Hkd; discriminate | right; exact (V1 k rg Hk' Hl' Hkd)].
    - intros k rg Hk' Hkd. rewrite region_of_tB in Hk'. destruct (Nat.eqb k rb) eqn:E; [injection Hk' as <-; cbn in Hkd; discriminate|].
      destruct (V2 k rg Hk' Hkd) as (W1 & W2 & W3). split; [right; exact W1|]. split; [exact W2 | exact W3].
    - split; [exact E0|]. split; [rewrite u_brk; unfold pz; lia|]. split; [exact Es|].
      intros k Hk1. destruct (Z_lt_dec k pb) as [Hlt|Hge].
      + apply range_in_maps_cons. apply Epages. lia.
      + apply range_in_maps_head; cbn [fst snd]; rewrite ?u_pz, ?u_pgsz; unfold pz; rewrite <- E0; LiaFast.nia_noeuclid.
    - intros p n Hin. apply fp_tB in Hin as [Hin|E].
      + destruct (V5 p n Hin) as (e & He & Q). exists e. split; [right; exact He | exact Q].
      + injection E as -> ->. exists (wz pz, wz PGSZ). split; [left; reflexivity|]. cbn [fst snd]. rewrite u_pz, u_pgsz. unfold addr_of. rewrite pz_eq. lia.
    -   intros k rg off Hk' Hkd Hoff. rewrite region_of_tB in Hk'. destruct (Nat.eqb k rb) eqn:E; [injection Hk' as <-; cbn in Hkd; discriminate | exact (X1 k rg off Hk' Hkd Hoff)].
    -   intros r1 r2 q1 q2 Hne H1 H2 K1 K2. rewrite region_of_tB in H1, H2.
      destruct (Nat.eqb r1 rb); [injection H1 as <-; cbn in K1; discriminate|]. destruct (Nat.eqb r2 rb); [injection H2 as <-; cbn in K2; discriminate|].
      exact (X2 r1 r2 q1 q2 Hne H1 H2 K1 K2).
    -   intros k rg Hk' Hl'. rewrite region_of_tB in Hk'. destruct (Nat.eqb k rb) eqn:E; [injection Hk' as <-; cbn [rgB rg_len]; pose proof (X3 rb rg0 Hr Hl); unfold PGSZ in *; lia | exact (X3 k rg Hk' Hl')].
    -   intros k rg Hk' Hl'. rewrite region_of_tB in Hk'. destruct (Nat.eqb k rb) eqn:E; [apply Nat.eqb_eq in E; subst k; injection Hk' as <-; cbn [rgB rg_len]; unfold pz in R8; lia | exact (X4 k rg Hk' Hl')].
    -   intros k rg q n Hk' Hkd Hl' Hin Hne. apply fp_tB in Hin as [Hin|E].
      + rewrite region_of_tB in Hk'. destruct (Nat.eqb k rb) eqn:Ek; [injection Hk' as <-; cbn in Hkd; discriminate | exact (V9 k rg q n Hk' Hkd Hl' Hin Hne)].
      + injection E as -> ->. rewrite region_of_tB in Hk'. rewrite Ebp in Hne. cbn [prid] in Hne.
        destruct (Nat.eqb k rb) eqn:Ek; [apply Nat.eqb_eq in Ek; exfalso; exact (Hne (eq_sym Ek))|].

        destruct (V2 k rg Hk' Hkd) as (W1 & _). pose proof (HG_free _ ltac:(apply in_app_iff; right; exact W1)) as D. cbn [fst snd] in D.
        pose proof (X4 k rg Hk' Hl') as [B1 B2]. pose proof (X3 k rg Hk' Hl') as B3. top_ranges.
        unfold wz in D. rewrite !u64 in D by (unfold PGSZ in *; lia). rewrite pz_eq. lia.
    -
      intros rb' p k rgk Hb Hk' Hkd Hl'. injection Hb as <- <-. rewrite region_of_tB in Hk'.
      destruct (Nat.eqb k rb) eqn:Ek; [injection Hk' as <-; cbn in Hkd; discriminate|].
      pose proof (V10 rb pb k rgk eq_refl Hk' Hkd Hl') as OLD.
      pose proof (HG_free _ ltac:(apply in_app_iff; right; exact (V1 k rgk Hk' Hl' Hkd))) as D. cbn [fst snd] in D.
      pose proof (X4 k rgk Hk' Hl') as [B1 B2]. pose proof (X3 k rgk Hk' Hl') as B3. top_ranges.
      unfold wz in D. rewrite !u64 in D by (unfold PGSZ in *; lia). unfold pz in *. LiaFast.nia_noeuclid.
  Qed.

  Theorem ledger_tB : ltac2:(tb__ "0|1|
S1S96VC;S40A2S1S95VC;S40A2S0S71S73S8fQ40A1M0G0A2A1S9aS40A1S9aVvm;A1A3A2A2").
  Proof using HG_ceil HG_free HI HIR HL HLG HSI HV Hbrk.
    pose proof brk_facts as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
    split; [|split; [exact HIR | reflexivity]].
    intros e [<-|He]; [|exact (HLG e He)]. cbn [fst snd]. rewrite u_pz, u_pgsz.
    split; [lia|]. split; [change (alloc_top vmB) with (alloc_top vm); rewrite <- (vm_ok_top L t vm HV); exact R8|].
    pose proof HSI as (_&_&_&_&_&_&_&_&_& [C1 C2] &_).
    destruct (Z_le_dec (pz + PGSZ) (mc_img_lo C)) as [|N1]; [left; lia|]. destruct (Z_le_dec (mc_img_hi C) pz) as [|N2]; [right; lia|]. exfalso.
    destruct (Z_le_dec (mc_img_lo C) pz).
    - apply (page_vs_image pz); unfold PGSZ, CTX_SIZE in *; lia.
    - apply (page_vs_image (mc_img_lo C)); unfold PGSZ, CTX_SIZE in *; lia.
  Qed.
  Lemma maps_wf_tB : maps_wf vmB.
  Proof using HG_ceil HG_free HI HL HMW HV Hbrk.
    unfold maps_wf. cbn [vmB vm_maps]. apply mwf_cons; [exact HMW | cbn [snd]; rewrite u_pgsz; unfold PGSZ; lia |].
    intros e' He'. unfold wdisj. cbn [fst snd]. rewrite u_pz, u_pgsz.
    destruct (HG_free e' ltac:(apply in_app_iff; right; exact He')) as [H|H]; [right; exact H | left; exact H].
  Qed.

  Lemma xraw_tB : ltac2:(tb__ "0|0|
SafS72S7S3dVX;A3S3aA2").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    intros q [<-|Hq].
    - left. rewrite tB_upd. apply MT_upd_same.
    - rewrite tB_upd. rewrite MT_upd_other.
      + unfold MT. rewrite (proj1 tBpre_fields). exact (HX q Hq).
      + intros ->. destruct (HX bm Hq) as [E|E]; rewrite bm_fresh in E; discriminate.
  Qed.
  Lemma bm_notX : ltac2:(tb__ "0|3|
S1S0S74S6dS3dVX;A2S7fA3S1S8aS7S3dS4eS3aA1A3S2S0S75S9A1M0S4cS3aS3dA2M1S76S9S22A2A3S0G0G1S76S9S2eS78S7A1M2G2A2A2A3A2A2A2").
  Proof using HI Hac Hbrk Hcnt Hhd. pose proof SPECB as (_ & M & K & R2 & _). cbn [fst snd] in *. auto. Qed.
  Lemma keys_tB : ltac2:(tb__ "0|0|
S8bS7S4eVt;A1S4eS3aA1A3").
  Proof using HI Hac Hbrk Hcnt Hhd. pose proof SPECB as (_ & _ & _ & _ & _ & _ & (ext & E & _)). cbn [fst snd] in E. intros q Hq. rewrite E. apply in_app_iff. left. exact Hq. Qed.
  Lemma am_frame_tB : ltac2:(tb__ "0|0|
S1SadVt;S3aA2S1S7S31S5S5dS72S7S3dVX;A3S3aR2R1A4S5dVX;Vt;R2R1A4A2Fgm;Fg;SabVt;S3aA2A2A2").
  Proof using HI Hac Hbrk Hcnt Hhd. pose proof SPECB as (_ & _ & _ & _ & F & U1 & UB). cbn [fst snd] in *. auto. Qed.
  Lemma bounded_tB : bounded tB.
  Proof using HB HG_ceil HG_free HI HIR HL HLG HSI HV HX Hac Hbrk Hcnt Hctx Hhd Hinit.
    pose proof HB as (B1 & B2 & B3 & _). pose proof bk_facts as (Hbr & Hr & Hk & Hl & Hlen & Hpb & LT & Ebp).
    pose proof tB_fields as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & F10 & _ & _ & F13 & _ & F15 & _).
    split; [intros sc; unfold usage_of; rewrite F15; apply B1|]. split; [rewrite F10; exact B2|].
    split; [exact (areas_bound (bm :: X) R U tB L C vmB HIB layout_ok_tB vm_ok_tB (proj1 ledger_tB))|].
    right. rewrite F13, F1, Ebp. cbn [prid padd]. rewrite length_lupd. exact LT.
  Qed.
  Lemma cell_whereB c x : ltac2:(tb__ "0|3|
S8aS44Vc;S77S44S4dS3aA1S8dS3aA1A3A3S1S81S54VL;S4fVc;A1A2M0Vx;A2S83Vx;S82G0S86S5cVc;A1A1A2A2A2S2S4S73S47S6A2M1G1S1S8aG1R1S4aVt;A1A3S1S81S54VL;S7eS47S6R1A3A2M2Vx;A2S83Vx;S82G2S7dS47S6R1A3A2A2A2A2Le;A2S1S81S3bVx;A2S83Vx;S82S3bS8A2A2A2A2F_;F_;").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    intros Hc Hx. destruct (cell_in_footprintI (bm :: X) R U tB L HIB xraw_tB c Hc) as (e & He & [I1 I2]).
    unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2. apply fp_tB in He as [He| ->].
    - left. exists e. split; [exact He|]. lia.
    - right. cbn [fst snd] in I1, I2. rewrite pz_eq in I1, I2. lia.
  Qed.
  Lemma page_vs_block b n x : ltac2:(tb__ "0|0|
S8aS73S6S6A2S7cS6S6Vb;Vn;A4S92VL;Vt;A2A3S1S81Vb;Vx;A2S83Vx;S82Vb;Vn;A2A2A2S3S1S81S3bVx;A2S83Vx;S82S3bS8A2A2A2A1F_;F_;").
  Proof using HG_free HI HIR HSI HV HX Hctx. intros Hin Hx. destruct (AllocMetaArea.block_where X R U t L HI HX b n x Hin Hx) as (e & p & He & _ & Rx). exact (page_vs_footprint e x He Rx). Qed.
End BRK.

Lemma loc_eq_dec (a b : loc) : ltac2:(tb__ "0|1|
Sa5S0S47Va;Vb;A3M0S3G0A1A2").
Proof.
  destruct a as [o|p], b as [o'|p']; try (right; discriminate).
  - destruct (Z.eq_dec o o') as [->|N]; [left; reflexivity | right; intros E; injection E; exact N].
  - destruct (sptr_eq_dec p p') as [->|N]; [left; reflexivity | right; intros E; injection E as E'; exact (N E')].
Qed.

Section DEAD.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (t : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S51VX;VR;VU;Vt;A4").
  Hypothesis HX : xraw X t.
  Hypothesis Hinit : st_init_done t = true.
  Hypothesis Halive : ltac2:(tb__ "0|0|
S3S0ScSdVt;A1S20A3A1").
  Hypothesis HL : layout_ok L t.

  Definition sd : astate := set_brk BrkDead t.

  Lemma Inv_sd : ltac2:(tb__ "0|0|
S51VX;VR;VU;S6fA4"). Proof using HI Halive Hinit. exact (Inv_brk_dead X R U t HI Halive Hinit). Qed.
  Lemma xraw_sd : xraw X sd. Proof using HX. exact HX. Qed.
  Lemma sd_fields : ltac2:(tb__ "0|2|
S1S0ScSdS6fA1S20A3S1S0S74S26S6fA1S7bA3S1S0S71S73S7S9A2A1SeS6fA1SeVt;A1A3S1S0S71S7A1SbS6fA1SbVt;A1A3S1S0S71SaA1S13S6fA1S13Vt;A1A3S1S0S75S7A1M0S1cS6fA1S1cVt;A1A3S1S0S7S17S6fA1S17Vt;A1A3S1S0S6S1aS6fA1S1aVt;A1A3S1S0S6S18S6fA1S18Vt;A1A3S1S0S6S11S6fA1S11Vt;A1A3S1S0G0S10S6fA1S10Vt;A1A3S1S0G0S16S6fA1S16Vt;A1A3S1S0S7S19S6fA1S19Vt;A1A3S1S0S71G0A1S15S6fA1S15Vt;A1A3S1S0S71S6A1M1S1eS6fA1S1eVt;A1A3S1S0G1S1dS6fA1S1dVt;A1A3S1S0G1S1bS6fA1S1bVt;A1A3S1S0S6S14S6fA1S14Vt;A1A3S0S6S12S6fA1S12Vt;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using Hinit. repeat split; try reflexivity. exact Hinit. Qed.
  Lemma footprint_sd : ltac2:(tb__ "0|0|
S0S71S73S47S6A2A1S4aS6fA1S4aVt;A1A3"). Proof using . reflexivity. Qed.
  Lemma user_blocks_sd : ltac2:(tb__ "0|0|
S0S71S73S7S6A2A1S55S6fA1S55Vt;A1A3"). Proof using . apply co_user_blocks. reflexivity. Qed.
  Lemma footers_sd : ltac2:(tb__ "0|0|
S0S71S44A1S8dS6fA1S8dVt;A1A3"). Proof using . apply co_footers. reflexivity. Qed.
  Lemma keys_sd : ltac2:(tb__ "0|0|
S0S71S7A1S4eS6fA1S4eVt;A1A3"). Proof using . reflexivity. Qed.
  Lemma MT_sd q : ltac2:(tb__ "0|0|
S0S75S9A1S4cS6fVq;A2S4cVt;Vq;A2A3"). Proof using . reflexivity. Qed.
  Lemma region_of_sd k : ltac2:(tb__ "0|0|
S0S75SaA1S4bS6fVk;A2S4bVt;Vk;A2A3"). Proof using . reflexivity. Qed.
  Lemma blocks_sd : ltac2:(tb__ "0|0|
S0S71S73S6S6A2A1S92VL;S6fA2S92VL;Vt;A2A3"). Proof using . reflexivity. Qed.
  Lemma layout_ok_sd : layout_ok L sd. Proof using HL. exact HL. Qed.

  Definition C_brkD : mcell := ltac2:(tb__ "0|0|
S46S45S56A1U8S48N1A1A3").

  Lemma image_sd c : ltac2:(tb__ "0|0|
S8aS44Vc;S77S44S4dS6fA1S8dS6fA1A3A3S2S0S44Vc;S70A3S1S8aS44Vc;S77S44S4dVt;A1S8dVt;A1A3A3S3S0S47S4fVc;A1S45S56A1A3A1A2A2F_;").
  Proof using HI HX Hinit.
    intros Hin.
    assert (CTX : forall u d, In d (ctx_cells u) -> mc_loc d = LCtx CTX_brk ->
              d = MCell (LCtx CTX_brk) 8 (match st_brk u with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end)).
    { intros u d Hd Ed. unfold ctx_cells in Hd. apply in_app_iff in Hd as [Hd|Hd].
      - cbn [In] in Hd. unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
          CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in *.
        destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc] in Ed; try (injection Ed as Ed'; lia). reflexivity.
      - exfalso. unfold CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces, CTX_brk in *.
        apply in_app_iff in Hd as [Hd|Hd]; [|apply in_app_iff in Hd as [Hd|Hd]; [|apply in_app_iff in Hd as [Hd|Hd]]];
          apply in_map_iff in Hd as (k & <- & Hk); apply in_seq in Hk; cbn [mc_loc] in Ed; injection Ed as Ed'; lia. }
    assert (SPLIT : forall u d, In d (image u ++ footer_cells u) -> In d (ctx_cells u) \/ In d (areas_cells u (st_areas u) ++ flat_map (fun gm => group_cells (fst gm) (snd gm)) (used_metas u)) \/ In d (footer_cells u)).
    { intros u d Hd. apply in_app_iff in Hd as [Hd|Hd]; [|right; right; exact Hd]. unfold image in Hd. apply in_app_iff in Hd as [Hd|Hd]; [left; exact Hd | right; left; exact Hd]. }
    destruct (SPLIT sd c Hin) as [Hc|[Hc|Hc]].
    -
      destruct (loc_eq_dec (mc_loc c) (LCtx CTX_brk)) as [E|NE].
      + left. rewrite (CTX sd c Hc E). reflexivity.
      + right. split; [|exact NE]. apply in_app_iff. left. unfold image. apply in_app_iff. left.
        pose proof sd_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
        clear - Hc NE F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19.
        unfold ctx_cells in Hc |- *. change (st_init_done sd) with (st_init_done t) in Hc. rewrite F1, F4, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19 in Hc.
        apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff; right; exact Hc].
        apply in_app_iff. left.
        destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
          [do 0 right|do 1 right|do 2 right|do 3 right|do 4 right|do 5 right|do 6 right|do 7 right|do 8 right|do 9 right|do 10 right|do 11 right|];
          try (left; reflexivity). exfalso. apply NE. reflexivity.
    - right. pose proof sd_fields as (_ & _ & F3 & F4 & _). rewrite F4, (co_areas_cells t sd F3), (co_used_metas t sd F3) in Hc.
      pose proof (AllocMetaArea.old_noctx_loc X R U t HI HX c (or_introl Hc)) as [H1 (q & Eq)]. split; [exact H1 | rewrite Eq; discriminate].
    - right. pose proof sd_fields as (_ & _ & F3 & _). rewrite (co_footers t sd F3) in Hc.
      pose proof (AllocMetaArea.old_noctx_loc X R U t HI HX c (or_intror Hc)) as [H1 (q & Eq)]. split; [exact H1 | rewrite Eq; discriminate].
  Qed.
  Lemma C_brkD_image : In C_brkD (image sd).
  Proof using . unfold image. apply in_app_iff. left. unfold ctx_cells. apply in_app_iff. left. cbn. do 12 right. left. reflexivity. Qed.

  Variables (C : mconsts) (vm : VmMaps).
  Hypothesis HV : ltac2:(tb__ "0|0|
S91VL;Vt;Vvm;A3").
  Hypothesis HLG : ledger_ok C vm.
  Hypothesis HB : bounded t.
  Lemma vm_ok_sd : ltac2:(tb__ "0|0|
S91VL;S6fVvm;A3").
  Proof using HV.
    pose proof HV as (V1 & V2 & V3 & V5 & X1 & X2 & X3 & X4 & V9 & V10 & V11).
    split; [exact V1|]. split; [exact V2|]. split; [exact I|]. split; [exact V5|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact V9|].
    split; [intros r p k rgk Hb; discriminate | exact V11].
  Qed.
  Lemma bounded_sd : bounded sd. Proof using HB. exact HB. Qed.
End DEAD.

Section DEADRUN.
  Variable t : astate.
  Hypothesis Hhd : st_free_meta_head t = None.
  Hypothesis Hcnt : st_avail_meta_count t = 0.
  Hypothesis Hac : st_avail_meta_area_count t = 0.
  Hypothesis Hbrk : ltac2:(tb__ "0|0|
S0ScSdVt;A1S20A3").
  Hypothesis Hinit : st_init_done t = true.

  Ltac am_compute_in H :=
    unfold alloc_meta, dequeue_head, dequeue, area_from_brk, area_from_mmap, open_area, new_region, upd_region,
           setslot, get_head, set_head, get_links, set_links, set_next, set_prev in H;
    unfold bind, ret, get, put, modify, ask in H;
    cbn -[padd Z.mul Z.add Z.sub Z.shiftl] in H.

  Lemma yields_dead_inv ktr res : ltac2:(tb__ "0|1|
S6eS73S75S7A1S24A2M0S30Vt;A1Vktr;Vres;A4S4S6S6S4S6S6S0G0Vres;Sa8Sa9Vt;A1R2R1A3A3Lzp;A2Lzm;A2F_;").
  Proof using Hac Hbrk Hcnt Hhd.
    intros Y.
    am_compute_in Y. repeat (progress (rewrite ?Hhd, ?Hcnt, ?Hac, ?Hbrk in Y; cbn -[padd Z.mul Z.add Z.sub Z.shiftl] in Y)).
    destruct ktr as [|[q1 zm] ktr]; [destruct Y|]. destruct Y as (_ & _ & Y). exists zm.
    destruct (zm =? 0) eqn:Ezm; cbn -[padd Z.mul Z.add Z.sub Z.shiftl] in Y.
    - destruct ktr; [|destruct p; destruct Y]. exists 0. rewrite <- Y. unfold r_RES. rewrite Ezm. reflexivity.
    - destruct ktr as [|[q2 zp] ktr]; [destruct Y|]. destruct Y as (_ & _ & Y). exists zp.
      destruct (zp =? 0) eqn:Ezp; cbn -[padd Z.mul Z.add Z.sub Z.shiftl] in Y.
      + destruct ktr; [|destruct p; destruct Y]. rewrite <- Y. unfold r_RES. rewrite Ezm, Ezp.
        unfold t_RES1, res_r, res_n, s0. cbn -[Z.mul Z.add Z.sub Z.shiftl]. reflexivity.
      + destruct ktr; [|destruct p; destruct Y]. rewrite <- Y. unfold r_RES. rewrite Ezm, Ezp.
        unfold s_RESok, take, open_st, t_RES1, res_r, res_n, s0. cbn -[Z.mul Z.add Z.sub Z.shiftl].
        rewrite !nth_middle. cbn -[Z.mul Z.add Z.sub Z.shiftl]. reflexivity.
  Qed.
End DEADRUN.

Definition SC13 (u : astate) : list mcell := ltac2:(tb__ "0|9|
S72S44S46S45S68A1U8M0S74S50L_;M1S26Vu;A1M2S69S48Z0M3A1M4X74x2A3S72S44S46S45S63A1U4M5S48S74S6L_;G2Z1G3X74x2A1A3S72S44S46S45S67A1G5S48S12Vu;A1A1A3S72S44S46S45S62A1G0S59S1cVu;A1A1A3S72S44S46S45S5fA1G0S71S7A1M6S50Lx;SbVu;A1M7G4S7G6S53S17Vu;A1A1Ll;Ls;X71x2A3S72S44S46S45S61A1G0S48S1aVu;A1A1A3S72S44S46S45S60A1G0S48S18Vu;A1M8A1A3S72S44S46S45S64A1G0S48S11Vu;A1A1A3S72S44S46S45S65A1G0S59S10Vu;A1A1A3S72S44S46S45S66A1G0S59S16Vu;A1A1A3S72S44S46S45S5aA1G0G1S80G6S74Lx;G7S7bS7G6S7fLl;Ls;X71x2S88G8G3A2A2G4S53S19Vu;A1A1X74x2A3S72S44S46S45S5bA1U1S48S14Vu;A1A1A3S72S44S46S45S56A1G0ScS50Lx;SdVu;A1G4S48N1A1S79S6S53S23R2S84S8R1A2A2A1Lp;Lr;Xcx3A3S7aS44A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma ctx_cells_SC13 u c o : ltac2:(tb__ "0|0|
S8aS44Vc;S49Vu;A1A3S0S47S4fVc;A1S45Vo;A1A3S2S83Vo;S5eA2S81S5bVo;A2A2S8aS44Vc;Sa6Vu;A1A3F_;F_;F_;").
Proof.
  intros Hin Hloc Ho. unfold ctx_cells in Hin.
  apply in_app_iff in Hin as [Hin|Hin]; [exact Hin|]. exfalso.
  unfold CTX_active, CTX_seq, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
  apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
    apply in_map_iff in H1 as (k & E & Hk); subst c; apply in_seq in Hk; cbn [mc_loc] in Hloc; injection Hloc as Hloc; lia.
Qed.

Lemma ctx_cell_w8 u c : ltac2:(tb__ "0|0|
S8aS44Vc;S49Vu;A1A3Sa4S5cVc;A1U8A2F_;").
Proof.
  intros Hin. unfold ctx_cells in Hin.
  apply in_app_iff in Hin as [Hin|Hin].
  { cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn; lia. }
  apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
    apply in_map_iff in H1 as (k & E & Hk); subst c; cbn; lia.
Qed.
