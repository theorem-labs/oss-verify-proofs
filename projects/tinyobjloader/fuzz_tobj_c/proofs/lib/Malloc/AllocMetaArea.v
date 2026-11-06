(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "PGSZ"; "region"; "mslot"; "st_areas"; "padd"; "rg_len"; "ameta"; "rg_kind"; "rg_live"; "st_metas"; "META_SIZE"; "MRaw"; "rkind"; "st_avail_meta_area_count"; "st_regions"; "AREA_HDR"; "METAS_PER_AREA"; "RkMetaRes"; "SP"; "astate"; "lupd"; "rg_rw"; "st_active"; "st_area_head"; "st_bounces"; "st_brk"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_seq"; "st_unmap_seq"; "st_usage"; "MFree"; "RkMap"; "brkst"; "mkRegion"; "mupdate"; "set_avail_meta"; "set_avail_meta_count"; "set_regions"; "st_area_tail"; "st_avail_meta"; "st_avail_meta_areas"; "st_avail_meta_count"; "st_free_meta_head"; "st_init_done"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.AREA"; "tA"; "pz"; "ap"; "am"; "rg0"; "ao"; "ar"; "tApre"; "vmA"; "rgA"; "C_tn"; "rr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "sub"; "mul"; "of_nat"; "pow"; "@Stdlib.Lists.List"; "In"; "flat_map"; "incl"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "mcell"; "LMem"; "footprint"; "loc_addr"; "ctx_cells"; "region_of"; "image"; "ly_reg"; "mc_loc"; "LCtx"; "MT"; "area_cells"; "keys"; "Inv"; "MCell"; "ly_ctx"; "sval"; "usedX"; "user_blocks"; "CTX_SIZE"; "CTX_avail_meta_areas"; "VP"; "areas_cells"; "group_cells"; "mc_w"; "memb"; "used_metas"; "@Corelib.Init.Datatypes"; "prod"; "list"; "option"; "Some"; "app"; "bool"; "None"; "cons"; "snd"; "fst"; "pair"; "nil"; "true"; "nat"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "vm_reserved"; "vm_maps"; "maps_subtract"; "mkVmMapsFull"; "vm_brk"; "vm_init_sp"; "vm_limit"; "vm_mmap_base"; "vm_noaccess"; "vm_start_brk"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "blocks"; "mc_img_hi"; "mc_img_lo"; "topL"; "vm_ok"; "wz"; "addr_of"; "img_reserved"; "ledger_ok"; "mc_ctx"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost"; "am_spec_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta"; "am_frame"; "open_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame MallocWfRings MallocWfRepr MallocWfMeta MallocWfGeom
  MallocWfSurgery MallocFooter MallocFooterLemmas MallocLayout MallocIface MallocIfaceI MallocLaws FpLaws WalkArith RingFacts Zones2
  AllocMetaPost AllocMetaImage AllocMetaGrow MapsWf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac in_list := solve [ cbn; repeat first [ left; reflexivity | right ] ].

Section AREA.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (t : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;VR;VU;Vt;A4").
  Hypothesis HX : xraw X t.
  Hypothesis Hhd : st_free_meta_head t = None.
  Hypothesis Hcnt : st_avail_meta_count t = 0.
  Hypothesis Hac : 0 < st_avail_meta_area_count t.
  Hypothesis Hinit : st_init_done t = true.
  Hypothesis HL : layout_ok L t.

  Definition rr : nat := length (st_regions t).
  Definition ap : sptr := ar_p t.
  Definition am : sptr := padd ap AREA_HDR.
  Definition tA : astate := s_ARok t.
  Definition ar : nat := prid ap.
  Definition ao : Z := poff ap.
  Definition rg0 : region := ar_rg t.
  Definition rgA : region := ltac2:(tb__ "0|0|
S2aSfS39A1SdS39A1S6dS6S1dS39A1S70S6S3aS74S6A1A3A3S10S39A1A4").

  Lemma s0_t : s0 t = t.
  Proof using HI HL HX Hac Hcnt Hhd Hinit. unfold s0. destruct t; cbn in *. rewrite Hinit. reflexivity. Qed.

  Lemma ap_facts : ltac2:(tb__ "0|0|
S0S1S7S37S1aS3bS3aA2A3S0S1S6bS9A1S53Vt;S3bA2S6cS9S39A2A3S0S1S14SfS39A1S19A3S0S1S6eS10S39A1S75A3S0S1S6S44S3aS8A2Z0A3S0S41S8S3aA2S0S1S6S42S3aS46S8S15Vt;A1A2A2SdS39A1A3S0S6S49S6R1S1dS39A1A3S43R2S3aA2F_;Fx;S83S3bS40A2A2A2A2A2A2A2A2A2").
  Proof using HI Hac.
    pose proof (inv_areas HI) as (_ & _ & _ & _ & _ & _ & _ & A8 & _).
    destruct (A8 Hac) as (r & o & rg & Ep & Hr & Hk & Hl & Ho1 & Ho2 & Hlen & Hrw).
    assert (Ear : ar = r) by (unfold ar, ap, ar_p; rewrite Ep; reflexivity).
    assert (Eao : ao = o) by (unfold ao, ap, ar_p; rewrite Ep; reflexivity).
    assert (Erg : rg0 = rg).
    { unfold rg0, ar_rg, ar_p. rewrite Ep. cbn [prid]. unfold region_of in Hr.
      destruct (nth_error (st_regions t) r) as [x|] eqn:E; [|discriminate]. injection Hr as ->. exact (nth_error_nth _ _ _ E). }
    rewrite Ear, Eao, Erg. split; [unfold ap, ar_p; exact Ep|]. repeat split; try assumption.
    unfold rr. exact (region_of_lt _ _ _ Hr).
  Qed.

  Lemma SPECA : ltac2:(tb__ "0|0|
S8fVX;VR;VU;Vt;S73S6bS7A1S1bS6cS7S38A2S35A4A5").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    pose proof (yields_AR t Hhd Hcnt Hac 1) as Y. rewrite s0_t in Y. cbn [Z.eqb] in Y.
    exact (am_spec_of_yields X R U t HI _ _ Y).
  Qed.
  Lemma HIA : ltac2:(tb__ "0|0|
S5bS70S7S38VX;A3VR;VU;S35A4"). Proof using HI HL HX Hac Hcnt Hhd Hinit. exact (proj1 SPECA). Qed.

  Lemma tA_fields : ltac2:(tb__ "0|4|
S0S1S6aS9A1S16S35A1S1cS9S16Vt;A1S3bS3eA4A3S0S1S6aS7A1SbS35A1S6dS7SbVt;A1S70S7S37S74S7A1A3A3A3S0S1S6aS69S7SaA2A1S11S35A1S2bS11Vt;A1S38S13A3A3S0S1S29S21S35A1S21Vt;A1A3S0S1S6eS34S35A1S75A3S0S1S6bS7A1M0S33S35A1S6fS7A1A3S0S1S7S30S35A1ScS38S12A2A3S0S1S6S32S35A1S45S18Z1M1A2A3S0S1S6S15S35A1S45S15Vt;A1G1A2A3S0S1S6S22S35A1S22Vt;A1A3S0S1G0S1fS35A1G0G0Lx;S1fVt;A1S7S6cS7R1A2Ls;S6cS7S37A2M2X6bx2A3S0S1G0S2fS35A1G2A3S0S1S7S31S35A1ScS37Z1000A2A3S0S1S6aG0A1S1eS35A1S1eVt;A1A3S0S1S6aS6A1M3S26S35A1S26Vt;A1A3S0S1G3S25S35A1S25Vt;A1A3S0S1G3S20S35A1S20Vt;A1A3S0S1S6S24S35A1S24Vt;A1A3S1S6S23S35A1S23Vt;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    unfold tA, s_ARok, take, open_st, rgA, rg0, am, ao, ar, ap. rewrite s0_t. cbn -[Z.mul Z.add Z.sub Z.shiftl padd METAS_PER_AREA ar_p ar_rg].
    repeat split; try reflexivity; assumption.
  Qed.

  Lemma region_of_tA k : ltac2:(tb__ "0|1|
S1S6bS9A1M0S53S35Vk;A2S6eG0L_;S95Vk;S3bA2S6cS9S3eA2S53Vt;Vk;A2X6ex2A3").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    pose proof tA_fields as (F1 & _). pose proof ap_facts as (_ & Hr & _ & _ & _ & _ & _ & _ & LT). unfold region_of. rewrite F1.
    rewrite nth_error_lupd. unfold rr in LT. replace (Nat.ltb ar (length (st_regions t))) with true by (symmetry; apply Nat.ltb_lt; exact LT).
    rewrite Bool.andb_true_r. reflexivity.
  Qed.

  Definition C_tn : mcell := ltac2:(tb__ "0|0|
S5cS4fScS4cS7SbVt;A1S1aU0Z0A2A3Z8A2A1U8S63S37A1A3").

  Lemma am_prid : prid am = ar. Proof using HI Hac. pose proof ap_facts as (E & _). unfold am. rewrite E. reflexivity. Qed.
  Lemma fresh_slot j : ltac2:(tb__ "0|0|
S41Z0Vj;A2S1S6bSaA1S58Vt;ScS37S42S17S46S12Vj;A2A2A2A2S6fSaA1A3F_;").
  Proof using HI Hac.
    intros Hj. pose proof ap_facts as (Eap & Hr & Hk & Hl & Ho1 & Ho2 & Hlen & Hrw & LT).
    destruct (MT t (padd ap (AREA_HDR + META_SIZE * j))) as [x|] eqn:E; [|reflexivity]. exfalso.
    pose proof (MT_Some_In_keys _ _ _ E) as Kq.
    destruct (key_area X R U t HI _ Kq) as (a0 & k0 & Ha0 & Hk0 & Eq).
    pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a0 Ha0) as (r' & o' & rg' & Ea0 & Ho' & Ho'2 & Hr' & Hl' & Hlen' & KIND).
    rewrite Eap, Ea0 in Eq. cbn [padd] in Eq. injection Eq as Er Eo. subst r'.
    rewrite Hr in Hr'. injection Hr' as <-. rewrite Hk in KIND. pose proof (Hrw o' KIND). unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
    clear - Hj Hk0 Eo Ho' Ho1 H. Z.to_euclidean_division_equations. nia.
  Qed.
  Lemma ap_fresh : ltac2:(tb__ "0|0|
S4S49S7S37SbVt;A1A3A1").
  Proof using HI Hac.
    intros Hin. pose proof ap_facts as (Eap & Hr & Hk & Hl & Ho1 & Ho2 & Hlen & Hrw & LT).
    pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK ap Hin) as (r' & o' & rg' & Ea0 & _ & _ & Hr' & _ & _ & KIND).
    rewrite Eap in Ea0. injection Ea0 as <- <-. rewrite Hr in Hr'. injection Hr' as <-. rewrite Hk in KIND. pose proof (Hrw ao KIND). lia.
  Qed.

  Definition tApre : astate := ltac2:(tb__ "0|0|
S2cScS38S12A2S2dS45S18Z1A2S93S37S2eS1cS9S16Vt;A1S3bS3eA4Vt;A2A2A2A2").
  Lemma tA_upd : ltac2:(tb__ "0|0|
S1S1bS35S91S38S13S3cA3A3").
  Proof using HI HL HX Hac Hcnt Hhd Hinit. unfold tA, s_ARok, take, open_st, tApre, rgA, rg0, am, ao, ar, ap. rewrite s0_t. reflexivity. Qed.
  Lemma tApre_fields : ltac2:(tb__ "0|0|
S0S1S6aS69S7SaA2A1S11S3cA1S11Vt;A1A3S0S1S6aS7A1SbS3cA1S6dS7SbVt;A1S70S7S37S74S7A1A3A3A3S1S6aS4eA1S52S3cA1S52S35A1A3A2A2").
  Proof using HI HL HX Hac Hcnt Hhd Hinit. rewrite tA_upd. repeat split; reflexivity. Qed.
  Lemma am_fresh : ltac2:(tb__ "0|0|
S1S6bSaA1S58Vt;S38A2S6fSaA1A3").
  Proof using HI Hac. unfold am. replace AREA_HDR with (AREA_HDR + META_SIZE * 0) by lia. apply fresh_slot. lia. Qed.

  Lemma area_cells_tA : ltac2:(tb__ "0|1|
S1S6aS4eA1S59S35S37S6fS7A1M0A3S59Vt;S37G0A3A3").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    pose proof tA_fields as (_ & _ & F3 & _).
    assert (E : forall k, meta_slot_cells (padd ap (AREA_HDR + META_SIZE * Z.of_nat k)) (mlookup (st_metas tA) (padd ap (AREA_HDR + META_SIZE * Z.of_nat k)))
                        = meta_slot_cells (padd ap (AREA_HDR + META_SIZE * Z.of_nat k)) (mlookup (st_metas t) (padd ap (AREA_HDR + META_SIZE * Z.of_nat k)))).
    { intros k. rewrite F3. rewrite mlookup_mupdate.
      pose proof (fresh_slot (Z.of_nat k) ltac:(lia)) as FR. unfold MT in FR. rewrite FR.
      destruct (sptr_eqb _ _); [apply meta_slot_cells_raw | reflexivity]. }
    unfold area_cells. f_equal.
    induction (seq 0 (Z.to_nat METAS_PER_AREA)) as [|k l IH]; [reflexivity|]. cbn [flat_map]. rewrite (E k), IH. reflexivity.
  Qed.

  Lemma old_noctx_loc c : ltac2:(tb__ "0|2|
S2S49S4eVc;S6dS4eS64Vt;SbVt;A1A2S4aS69S7SeA2M0S4eG0S65S72S7SeR1A3S71S7SeR1A3A2Lgm;S68Vt;A1A4A3A3S49S4eVc;S78Vt;A1M1A3A2S0S49S4eVc;S6dS4eS54Vt;A1G1A3A3S3S7S7S1S4dS56Vc;A1S4fR1A1A3Lq;A2A2F_;").
  Proof using HI HX.
    intros H. split.
    - apply in_app_iff. destruct H as [H|H]; [left; unfold image; apply in_app_iff; right; exact H | right; exact H].
    - destruct H as [H|H].
      + apply in_app_iff in H as [H|H].
        * destruct (In_areas_cells t _ c H) as (a0 & next & _ & Hc). destruct (In_area_cells t a0 next c Hc) as (d & E & _). rewrite E. eexists; reflexivity.
        * apply in_flat_map in H as ([g gm] & Hg & Hc). cbn [fst snd] in Hc.
          destruct (In_group_cells X R U t g gm c HI (proj1 (used_iff X R U t HI HX g gm) Hg) Hc) as (d & E & _). rewrite E. eexists; reflexivity.
      + unfold footer_cells in H. apply in_flat_map in H as ([g gm] & Hg & Hc). cbn [fst snd] in Hc.
        destruct (In_group_footer_cells X R U t g gm c HI (proj1 (used_iff X R U t HI HX g gm) Hg) Hc) as (d & E & _). rewrite E. eexists; reflexivity.
  Qed.

  Theorem image_tA c : ltac2:(tb__ "0|0|
S49S4eVc;S6dS4eS54S35A1S78S35A1A3A3S2S49S4eVc;S52S35A1A3S2S0S4S1S6aS7A1SbVt;A1S74S7A1A3A1S1S4eVc;S3fA3A2S2S49S4eVc;S59S35S37S6fS7A1A3A3S0S49S4eVc;S6dS4eS54Vt;A1S78Vt;A1A3A3S3S7S7S1S4dS56Vc;A1S4fR1A1A3Lq;A2A2A2A2A2F_;").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    pose proof tApre_fields as (P1 & P2 & P3).
    assert (NU : nonused (MT tApre am)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) am) with (MT t am); rewrite am_fresh; exact I).
    intros Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite tA_upd in Hin. destruct (uf_image_In tApre am MRaw NU I c Hin) as [H|H].
      + unfold image in H. apply in_app_iff in H as [H|H]; [left; rewrite <- P3; exact H|].
        rewrite P2, (co_areas_cells t tApre P1), (co_used_metas t tApre P1) in H.
        apply in_app_iff in H as [H|H].
        * destruct (ap_areas_cells_In t t ap eq_refl (st_areas t) c H) as [Ho|[Htn|Hnew]].
          -- right; right; right. apply old_noctx_loc. left. apply in_app_iff. left. exact Ho.
          -- right; left. exact Htn.
          -- right; right; left. rewrite area_cells_tA. exact Hnew.
        * right; right; right. apply old_noctx_loc. left. apply in_app_iff. right. exact H.
      + right; right; left. rewrite area_cells_tA. unfold area_cells. apply in_app_iff. right.
        apply in_flat_map. exists 0%nat. split; [apply in_seq; unfold METAS_PER_AREA; lia|].
        replace (padd ap (AREA_HDR + META_SIZE * Z.of_nat 0)) with am by (unfold am; f_equal).
        change (mlookup (st_metas t) am) with (MT t am). rewrite am_fresh. rewrite meta_slot_cells_raw in H. exact H.
    - right; right; right. apply old_noctx_loc. right.
      rewrite tA_upd, (uf_footers tApre am MRaw NU I), (co_footers t tApre P1) in Hin. exact Hin.
  Qed.

  Lemma ctx_cells_tAC c : ltac2:(tb__ "0|1|
S49S4eVc;S52S35A1A3S2S3S6S6S3S76S76S3S5eS5eS0S1S4eVc;S5cS57R3A1R2R1A3A3S0S83U0R2A2S2S0S41Z0R3A2S41S42R3S47R2A1A2M0ZcA2A2S2S0S41Z10R3A2S41G0Z50A2A2S0S41Z398R3A2S41G0Z3a0A2A2A2A2A2A2Lval;A2Lw;A2Lo;A2S0S49S4eVc;S52Vt;A1A3S4S1S4dS56Vc;A1S57S62A1A3A1A2A2F_;").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    intros Hin.
    pose proof tA_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
    unfold ctx_cells in Hin. rewrite F2, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19 in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    - cbn [In] in Hin.
      unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
        CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in *.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
        first [
                left; eexists _, _, _; (split; [reflexivity|]); (split; [cbn; lia | cbn; lia])
              | right; (split; [unfold ctx_cells; apply in_app_iff; left; rewrite ?Hinit; in_list | cbn [mc_loc]; intros E; injection E as E'; lia]) ].
    - right. split; [unfold ctx_cells; apply in_app_iff; right; exact Hin|].
      destruct (ctx_maps_loc _ c Hin) as (o & -> & Ho). unfold CTX_active, CTX_avail_meta_areas in *. intros E. injection E as E'. lia.
  Qed.

  Lemma fp_tA e : ltac2:(tb__ "0|1|
S5S49S69S4dS6A2M0Ve;S50S35A1A3S2S49G0Ve;S50Vt;A1A3S1G0Ve;S73S4dS6S4fS37A1S8A4A3A2A2").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    pose proof tA_fields as (F1 & F2 & _). pose proof ap_facts as (_ & Hr & Hk & _). rewrite !In_footprint, F2.
    rewrite (map_fp_regions_only (set_regions (lupd (st_regions t) ar rgA) t) tA) by (rewrite F1; reflexivity).
    rewrite (map_fp_upd_nonmap t ar rg0 rgA Hr) by (cbn; rewrite Hk; discriminate).
    rewrite map_app, in_app_iff. cbn [map In]. intuition congruence.
  Qed.
  Lemma ub_tA : ltac2:(tb__ "0|0|
S1S6aS69S7S6A2A1S60S35A1S60Vt;A1A3").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    pose proof tApre_fields as (P1 & _).
    assert (NU : nonused (MT tApre am)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) am) with (MT t am); rewrite am_fresh; exact I).
    rewrite tA_upd, (uf_user_blocks tApre am MRaw NU I). exact (co_user_blocks t tApre P1).
  Qed.
  Lemma footers_tA : ltac2:(tb__ "0|0|
S1S6aS4eA1S78S35A1S78Vt;A1A3").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    pose proof tApre_fields as (P1 & _).
    assert (NU : nonused (MT tApre am)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) am) with (MT t am); rewrite am_fresh; exact I).
    rewrite tA_upd, (uf_footers tApre am MRaw NU I). exact (co_footers t tApre P1).
  Qed.

  Variables (C : mconsts) (vm : VmMaps).
  Hypothesis Hctx : ltac2:(tb__ "0|0|
S1S6S5dVL;A1S8dVC;A1A3").
  Hypothesis HSI : statics_in_image C.
  Hypothesis HV : ltac2:(tb__ "0|0|
S88VL;Vt;Vvm;A3").
  Hypothesis HLG : ledger_ok C vm.
  Hypothesis HIR : img_reserved C vm.
  Hypothesis HB : bounded t.
  Hypothesis HMW : maps_wf vm.

  Definition pz : Z := ltac2:(tb__ "0|0|
S42S55VL;S3bA2S3aA2").
  Definition vmA : VmMaps := ltac2:(tb__ "0|0|
S7cS79Vvm;A1S7aVvm;A1S7bS81Vvm;A1S36S42S36S8A2A3S82Vvm;A1S7dVvm;A1S7fVvm;A1S80Vvm;A1S7eVvm;A1A8").

  Lemma pz_eq : ltac2:(tb__ "0|0|
S1S6S51VL;S4fS37A1A2S36A3").
  Proof using HI Hac. pose proof ap_facts as (E & _). unfold pz. rewrite E. reflexivity. Qed.
  Lemma am_addr : ltac2:(tb__ "0|0|
S1S6S8aVL;S38A2S42S36S17A2A3").
  Proof using HI Hac. pose proof ap_facts as (E & _). unfold addr_of, am, pz. rewrite E. cbn [padd loc_addr]. lia. Qed.

  Lemma res_facts : ltac2:(tb__ "0|4|
S0S41S8S55VL;S3bA2M0A2S0S41S42G0SdS39A1M1A2S87VL;A1M2A2S0S1S6S44G0S8A2Z0M3A3S0S41S8S3aA2S0S41S42S3aS8A2G1A2S0S1S6S44S36S8A2G3A3S0S41S8S36A2S0S41S42S36S8A2G2A2S0S41G3S36A2S43S36S48Z2Z40A2A2A2A2A2A2A2A2A2A2A2").
  Proof using HI HL HV Hac.
    pose proof ap_facts as (Eap & Hr & Hk & Hl & Ho1 & Ho2 & Hlen & Hrw & LT). pose proof HV as (_ & _ & _ & _ & _ & _ & _ & X4 & _).
    destruct (X4 ar rg0 Hr Hl) as [B1 B2]. pose proof HL as (_ & Halign & _). pose proof (Halign ar rg0 Hr Hl) as AL.
    assert (M1 : PGSZ * 1 <= PGSZ * st_avail_meta_area_count t) by (apply Z.mul_le_mono_nonneg_l; unfold PGSZ; lia).
    assert (PZ : pz mod PGSZ = 0) by (unfold pz; rewrite Z.add_mod, AL, Ho1 by (unfold PGSZ; lia); reflexivity).
    top_ranges. unfold pz in *. unfold PGSZ in *.
    split; [lia|]. split; [lia|]. split; [exact AL|]. split; [lia|]. split; [lia|]. split; [exact PZ|]. lia.
  Qed.
  Lemma in_maps : ltac2:(tb__ "0|1|
S49S69S8eQ40A1M0G0A2S73G0G0S89S55VL;S3bA2A1S89SdS39A1A1A4S7aVvm;A1A3").
  Proof using HI HV Hac. pose proof ap_facts as (_ & Hr & Hk & _). pose proof HV as (_ & V2 & _). exact (proj1 (V2 ar rg0 Hr Hk)). Qed.
  Lemma page_vs_image x : ltac2:(tb__ "0|0|
S0S41S86VC;A1Vx;A2S43Vx;S85VC;A1A2A2S4S0S41S36Vx;A2S43Vx;S42S36S8A2A2A2A1F_;").
  Proof using HI HL HLG HV Hac.
    intros Hx Hin. pose proof res_facts as (R1 & R2 & _ & R4 & R5 & _). pose proof (HLG _ in_maps) as (G1 & G2 & G3). cbn [fst snd] in G3.
    unfold wz in G3. top_ranges. rewrite !u64 in G3 by (unfold PGSZ in *; lia). unfold pz in Hin. lia.
  Qed.

  Lemma page_vs_footprint e x : ltac2:(tb__ "0|1|
S49S69S4dS6A2Ve;S50Vt;A1A3S0S41S51VL;S72S4dS6Ve;A3A2M0Vx;A2S43Vx;S42G0S71S4dS6Ve;A3A2A2A2S4S0S41S36Vx;A2S43Vx;S42S36S8A2A2A2A1F_;F_;").
  Proof using HI HL HLG HSI HV Hac Hctx.
    intros He Hx Hin. pose proof ap_facts as (Eap & Hr & Hk & Hl & Ho1 & Ho2 & Hlen & Hrw & LT). pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & V9 & _).
    pose proof res_facts as (R1 & R2 & R3 & R4 & R5 & _).
    destruct e as [[o|q] n].
    -   pose proof HSI as (_&_&_&_&_&_&_&_&_& [C1 C2] &_). cbn [fst snd loc_addr] in Hx.
      unfold footprint in He. destruct He as [E|He].
      + injection E as <- <-. apply (page_vs_image x); [rewrite Hctx in Hx; lia | exact Hin].
      + apply in_app_iff in He as [He|He]; [apply in_map_iff in He as (? & E & _); discriminate|].
        apply in_flat_map in He as (k & _ & He). destruct (region_of t k) as [rg|]; [|destruct He]. destruct (rg_kind rg); try destruct He.
        destruct (rg_live rg); [destruct He as [E|[]]; discriminate | destruct He].
    - cbn [fst snd] in Hx. destruct (Nat.eq_dec (prid q) ar) as [Eq|Hne].
      +
        unfold footprint in He. destruct He as [E|He]; [discriminate|]. apply in_app_iff in He as [He|He].
        * apply in_map_iff in He as (a0 & E & Ha0). injection E as -> <-.
          pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK q Ha0) as (r' & o' & rg' & Ea0 & Ho' & Ho'2 & Hr' & Hl' & Hlen' & KIND).
          subst q. cbn [prid] in Eq. subst r'. rewrite Hr in Hr'. injection Hr' as <-. rewrite Hk in KIND. pose proof (Hrw o' KIND) as LT'.
          cbn [loc_addr] in Hx. unfold pz in Hin. unfold PGSZ in *. Z.to_euclidean_division_equations; nia.
        * apply in_flat_map in He as (k & _ & He). destruct (region_of t k) as [rg|] eqn:Ek; [|destruct He]. destruct (rg_kind rg) eqn:Kk; try destruct He.
          destruct (rg_live rg); [|destruct He]. destruct He as [E|[]]. injection E as <- <-. cbn [prid] in Eq. subst k.
          rewrite Hr in Ek. injection Ek as <-. rewrite Hk in Kk. discriminate.
      + pose proof (V9 ar rg0 q n Hr Hk Hl He Hne) as D. unfold pz in Hin. lia.
  Qed.
  Lemma fp_size e : ltac2:(tb__ "0|0|
S49S69S4dS6A2Ve;S50Vt;A1A3S43Z0S71S4dS6Ve;A3A2F_;").
  Proof using HV.
    intros He. pose proof HV as (_ & _ & _ & _ & _ & _ & SZ & _). unfold footprint in He. destruct He as [<-|He]; [cbn; unfold CTX_SIZE; lia|].
    apply in_app_iff in He as [He|He]; [apply in_map_iff in He as (? & <- & _); cbn; unfold PGSZ; lia|].
    apply in_flat_map in He as (k & _ & He). destruct (region_of t k) as [rg|] eqn:Ek; [|destruct He]. destruct (rg_kind rg); try destruct He.
    destruct (rg_live rg) eqn:El; [|destruct He]. destruct He as [<-|[]]. cbn. pose proof (SZ k rg Ek El). unfold PGSZ in *. lia.
  Qed.

  Lemma map_region_vs_page k rg x : ltac2:(tb__ "0|1|
S1S6bS9A1S53Vt;Vk;A2S6cS9Vrg;A2A3S1S6eS10Vrg;A1S75A3S1S14SfVrg;A1S28A3S0S41S55VL;Vk;A2M0Vx;A2S43Vx;S42G0SdVrg;A1A2A2A2S4S0S41S36Vx;A2S43Vx;S42S36S8A2A2A2A1F_;F_;F_;F_;").
  Proof using HI HL HLG HSI HV Hac Hctx.
    intros Hk Hl Hkd Hx. apply (page_vs_footprint (LMem (SP k 0), rg_len rg) x (footprint_region_In t k rg Hk Hkd Hl)).
    cbn [fst snd loc_addr]. lia.
  Qed.

  Theorem layout_ok_tA : layout_ok L tA.
  Proof using HI HL HLG HSI HV HX Hac Hcnt Hctx Hhd Hinit.
    pose proof HL as (A & B & Cc & D). pose proof ap_facts as (Eap & Hr & Hk & Hl & _). pose proof res_facts as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
    split; [exact A|]. split.
    { intros k rg Hk' Hl'. rewrite region_of_tA in Hk'. destruct (Nat.eqb k ar) eqn:E; [apply Nat.eqb_eq in E; subst k; exact (B ar rg0 Hr Hl) | exact (B k rg Hk' Hl')]. }
    pose proof tA_fields as (F1 & F2 & _).
    assert (NEWR : crange L (LMem ap, PGSZ) = (pz, PGSZ)) by (unfold crange; cbn [fst snd]; rewrite pz_eq; reflexivity).
    assert (DISJ : forall e, In e (footprint t) -> ranges_disjoint (crange L e) (crange L (LMem ap, PGSZ)) /\ ranges_disjoint (crange L (LMem ap, PGSZ)) (crange L e)).
    { intros e He. rewrite NEWR. unfold ranges_disjoint, crange. cbn [fst snd]. pose proof (fp_size e He) as SZ.
      destruct (Z_le_dec (loc_addr L (fst e) + snd e) pz); [lia|].
      destruct (Z_le_dec (pz + PGSZ) (loc_addr L (fst e))); [lia|]. exfalso.
      destruct (Z_le_dec (loc_addr L (fst e)) pz).
      - apply (page_vs_footprint e pz He); unfold PGSZ in *; lia.
      - apply (page_vs_footprint e (loc_addr L (fst e)) He); unfold PGSZ in *; lia. }
    assert (FP2 : footprint tA = ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ (LMem ap, PGSZ) :: map_fp t).
    { rewrite footprint_eq, F2, map_app. rewrite (map_fp_regions_only (set_regions (lupd (st_regions t) ar rgA) t) tA) by (rewrite F1; reflexivity).
      rewrite (map_fp_upd_nonmap t ar rg0 rgA Hr) by (cbn; rewrite Hk; discriminate). cbn [map]. rewrite <- app_assoc. reflexivity. }
    assert (FP0 : footprint t = ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ map_fp t) by (rewrite footprint_eq; reflexivity).
    split.
    - rewrite FP2, map_app.
      change (map (crange L) ((LMem ap, PGSZ) :: map_fp t)) with (crange L (LMem ap, PGSZ) :: map (crange L) (map_fp t)).
      assert (EQ0 : map (crange L) ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ map (crange L) (map_fp t) = map (crange L) (footprint t)).
      { rewrite FP0, map_app. reflexivity. }
      apply pairwise_insert.
      + rewrite EQ0. exact Cc.
      + intros y Hy. rewrite EQ0 in Hy. apply in_map_iff in Hy as (e & <- & He). split; [apply (proj2 (DISJ e He)) | apply (proj1 (DISJ e He))].
    - intros rg Hrg. apply fp_tA in Hrg as [Hrg| ->]; [exact (D rg Hrg)|]. rewrite NEWR. cbn [fst snd]. top_ranges. unfold PGSZ in *. lia.
  Qed.

  Lemma region_live_t k rg : ltac2:(tb__ "0|0|
S1S6bS9A1S53Vt;Vk;A2S6cS9Vrg;A2A3S1S14SfVrg;A1S19A3S1S6eS10Vrg;A1S75A3F_;F_;").
  Proof using HI. intros Hk Hkd. pose proof (inv_areas HI) as (_&_&_&_&A5&_). exact (proj1 (A5 k rg Hk Hkd)). Qed.

  Theorem vm_ok_tA : ltac2:(tb__ "0|0|
S88VL;S35S3dA3").
  Proof using HI HL HV HX Hac Hcnt Hhd Hinit.
    pose proof HV as (V1 & V2 & V3 & V5 & X1 & X2 & X3 & X4 & V9 & V10 & V11). pose proof ap_facts as (Eap & Hr & Hk & Hl & Ho1 & Ho2 & Hlen & Hrw & LT).
    pose proof res_facts as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9). pose proof tA_fields as (F1 & F2 & F3 & F4 & _).
    assert (HI64 : pz + PGSZ < 2 ^ 64) by (top_ranges; unfold PGSZ in *; lia).
    assert (Hlo : 0 <= pz) by lia. assert (Hlh : pz <= pz + PGSZ) by (unfold PGSZ; lia).
    unfold vm_ok. rewrite F4. cbn [vmA vm_maps vm_noaccess vm_brk vm_start_brk].
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|   exact V11]]]]]]]]]].
    - intros k rg Hk' Hl' Hkd. rewrite region_of_tA in Hk'. destruct (Nat.eqb k ar) eqn:E; [injection Hk' as <-; cbn in Hkd; rewrite Hk in Hkd; discriminate | exact (V1 k rg Hk' Hl' Hkd)].
    - intros k rg Hk' Hkd. rewrite region_of_tA in Hk'. destruct (Nat.eqb k ar) eqn:E.
      + apply Nat.eqb_eq in E. subst k. injection Hk' as <-. cbn [rgA rg_len rg_rw rg_kind]. destruct (V2 ar rg0 Hr Hk) as (W1 & W2 & W3).
        split; [exact W1|]. split.
        * intros k Hk1 Hk2 Hk3.
          assert (NK : PGSZ * k <> ao) by (intros E; apply Hk3; apply in_app_iff; right; left; symmetry; exact E).
          apply (maps_subtract_keeps (vm_noaccess vm) pz (pz + PGSZ) (ly_reg L ar + PGSZ * k) PGSZ); [unfold PGSZ; lia | exact Hlo | exact HI64 | |].
          -- unfold pz. unfold PGSZ in *. Z.to_euclidean_division_equations; nia.
          -- apply (W2 k Hk1 Hk2). intros Hin. apply Hk3. apply in_app_iff. left. exact Hin.
        * intros off Hoff e He.
          destruct (maps_subtract_piece _ pz (pz + PGSZ) e Hlo Hlh HI64 He) as (e0 & He0 & S1 & S2 & Dj).
          apply in_app_iff in Hoff as [Hoff|[<-|[]]].
          -- pose proof (W3 off Hoff e0 He0) as W. clear - W S1 S2. lia.
          -- unfold pz in Dj. clear - Dj S1 S2. lia.
      + apply Nat.eqb_neq in E. destruct (V2 k rg Hk' Hkd) as (W1 & W2 & W3). pose proof (region_live_t k rg Hk' Hkd) as Hl'.
        split; [exact W1|]. split.
        * intros j Hj1 Hj2 Hj3.
          apply (maps_subtract_keeps (vm_noaccess vm) pz (pz + PGSZ)); [unfold PGSZ; lia | exact Hlo | exact HI64 | |].
          --
             pose proof (X2 k ar rg rg0 E Hk' Hr Hkd Hk) as DD. unfold pz. unfold PGSZ in *. nia.
          -- exact (W2 j Hj1 Hj2 Hj3).
        * intros off Hoff e He.
          destruct (maps_subtract_piece _ pz (pz + PGSZ) e Hlo Hlh HI64 He) as (e0 & He0 & S1 & S2 & Dj).
          pose proof (W3 off Hoff e0 He0) as W. clear - W S1 S2. lia.
    - exact V3.
    - intros p n Hin. apply fp_tA in Hin as [Hin|E]; [exact (V5 p n Hin)|].
      injection E as -> ->. exists (wz (ly_reg L ar), wz (rg_len rg0)). split; [exact in_maps|]. cbn [fst snd]. unfold wz.
      rewrite !u64 by (clear - R1 R2 R4 R5; top_ranges; unfold PGSZ in *; lia). unfold addr_of. rewrite pz_eq. unfold pz. clear - R1 R2 R4 R5. top_ranges. unfold PGSZ in *. lia.
    -   intros k rg off Hk' Hkd Hoff. rewrite region_of_tA in Hk'. destruct (Nat.eqb k ar) eqn:E.
      + injection Hk' as <-. cbn [rgA rg_rw rg_len] in Hoff |- *. apply in_app_iff in Hoff as [Hoff|[<-|[]]]; [exact (X1 ar rg0 off Hr Hk Hoff)|]. lia.
      + exact (X1 k rg off Hk' Hkd Hoff).
    -   intros r1 r2 q1 q2 Hne H1 H2 K1 K2. rewrite region_of_tA in H1, H2.
      assert (G : forall k q, (if Nat.eqb k ar then Some rgA else region_of t k) = Some q -> rg_kind q = RkMetaRes ->
                 exists q', region_of t k = Some q' /\ rg_kind q' = RkMetaRes /\ rg_len q' = rg_len q).
      { intros k q Hq Kq. destruct (Nat.eqb k ar) eqn:E; [apply Nat.eqb_eq in E; subst k; injection Hq as <-; exists rg0; repeat split; assumption | exists q; auto]. }
      destruct (G r1 q1 H1 K1) as (q1' & H1' & K1' & L1). destruct (G r2 q2 H2 K2) as (q2' & H2' & K2' & L2).
      rewrite <- L1, <- L2. exact (X2 r1 r2 q1' q2' Hne H1' H2' K1' K2').
    -   intros k rg Hk' Hl'. rewrite region_of_tA in Hk'. destruct (Nat.eqb k ar) eqn:E; [injection Hk' as <-; cbn [rgA rg_len]; exact (X3 ar rg0 Hr Hl) | exact (X3 k rg Hk' Hl')].
    -   intros k rg Hk' Hl'. rewrite region_of_tA in Hk'. destruct (Nat.eqb k ar) eqn:E; [apply Nat.eqb_eq in E; subst k; injection Hk' as <-; cbn [rgA rg_len]; exact (X4 ar rg0 Hr Hl) | exact (X4 k rg Hk' Hl')].
    -   intros k rg q n Hk' Hkd Hl' Hin Hne. apply fp_tA in Hin as [Hin|E].
      + rewrite region_of_tA in Hk'. destruct (Nat.eqb k ar) eqn:Ek.
        * apply Nat.eqb_eq in Ek. subst k. injection Hk' as <-. cbn [rgA rg_len]. exact (V9 ar rg0 q n Hr Hk Hl Hin Hne).
        * exact (V9 k rg q n Hk' Hkd Hl' Hin Hne).
      + injection E as -> ->. rewrite region_of_tA in Hk'. rewrite Eap in Hne. cbn [prid] in Hne.
        destruct (Nat.eqb k ar) eqn:Ek; [apply Nat.eqb_eq in Ek; exfalso; exact (Hne (eq_sym Ek))|]. apply Nat.eqb_neq in Ek.
        pose proof (X2 k ar rg rg0 Ek Hk' Hr Hkd Hk) as DD. rewrite pz_eq. unfold pz. unfold PGSZ in *. lia.
    -   intros rb p k rgk Hb Hk' Hkd Hl'. rewrite region_of_tA in Hk'. destruct (Nat.eqb k ar) eqn:Ek.
      + injection Hk' as <-. cbn in Hkd. rewrite Hk in Hkd. discriminate.
      + exact (V10 rb p k rgk Hb Hk' Hkd Hl').
  Qed.

  Theorem ledger_tA : ltac2:(tb__ "0|1|
S0S8cVC;S3dA2S0S8bVC;S3dA2S1S6aS69S8eQ40A1M0G0A2A1S79S3dA1S79Vvm;A1A3A2A2").
  Proof using HIR HLG. split; [exact HLG | split; [exact HIR | reflexivity]]. Qed.
  Lemma maps_wf_tA : maps_wf vmA. Proof using HMW. exact HMW. Qed.

  Lemma xraw_tA : ltac2:(tb__ "0|0|
S94S70S7S38VX;A3S35A2").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    intros q [<-|Hq].
    - left. rewrite tA_upd. apply MT_upd_same.
    - rewrite tA_upd. rewrite MT_upd_other.
      + unfold MT. rewrite (proj1 tApre_fields). exact (HX q Hq).
      + intros ->. destruct (HX am Hq) as [E|E]; rewrite am_fresh in E; discriminate.
  Qed.
  Lemma am_notX : ltac2:(tb__ "0|3|
S0S1S6eS67S38VX;A2S77A3S0S49S7S38S5aS35A1A3S2S1S6bSaA1M0S58S35S38A2M1S6cSaS13A2A3S1G0G1S6cSaS27S6fS7A1M2G2A2A2A3A2A2A2").
  Proof using HI HL HX Hac Hcnt Hhd Hinit. pose proof SPECA as (_ & M & K & R2 & _). cbn [fst snd] in *. auto. Qed.
  Lemma keys_tA : ltac2:(tb__ "0|0|
S4bS7S5aVt;A1S5aS35A1A3").
  Proof using HI HL HX Hac Hcnt Hhd Hinit. pose proof SPECA as (_ & _ & _ & _ & _ & _ & (ext & E & _)). cbn [fst snd] in E. intros q Hq. rewrite E. apply in_app_iff. left. exact Hq. Qed.
  Lemma am_frame_tA : ltac2:(tb__ "0|0|
S0S92Vt;S35A2S0S7SeS5S5fS70S7S38VX;A3S35R2R1A4S5fVX;Vt;R2R1A4A2Fgm;Fg;S90Vt;S35A2A2A2").
  Proof using HI HL HX Hac Hcnt Hhd Hinit. pose proof SPECA as (_ & _ & _ & _ & F & U1 & UB). cbn [fst snd] in *. auto. Qed.
  Lemma bounded_tA : bounded tA.
  Proof using HB HI HIR HL HLG HSI HV HX Hac Hcnt Hctx Hhd Hinit.
    pose proof HB as (B1 & B2 & B3 & _). pose proof ap_facts as (Eap & _ & _ & _ & _ & _ & _ & _ & LT).
    pose proof tA_fields as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & F10 & _ & _ & F13 & _ & F15 & _).
    split; [intros sc; unfold usage_of; rewrite F15; apply B1|]. split; [rewrite F10; exact B2|].
    split; [exact (areas_bound (am :: X) R U tA L C vmA HIA layout_ok_tA vm_ok_tA (proj1 ledger_tA))|].
    right. rewrite F13, F1, Eap. cbn [prid padd]. rewrite length_lupd. exact LT.
  Qed.
  Lemma cell_whereA c x : ltac2:(tb__ "0|3|
S49S4eVc;S6dS4eS54S35A1S78S35A1A3A3S0S41S51VL;S56Vc;A1A2M0Vx;A2S43Vx;S42G0S47S66Vc;A1A1A2A2A2S2S3S69S4dS6A2M1G1S0S49G1R1S50Vt;A1A3S0S41S51VL;S72S4dS6R1A3A2M2Vx;A2S43Vx;S42G2S71S4dS6R1A3A2A2A2A2Le;A2S0S41S36Vx;A2S43Vx;S42S36S8A2A2A2A2F_;F_;").
  Proof using HI HL HX Hac Hcnt Hhd Hinit.
    intros Hc Hx. destruct (cell_in_footprintI (am :: X) R U tA L HIA xraw_tA c Hc) as (e & He & [I1 I2]).
    unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2. apply fp_tA in He as [He| ->].
    - left. exists e. split; [exact He|]. lia.
    - right. cbn [fst snd] in I1, I2. rewrite pz_eq in I1, I2. lia.
  Qed.
  Lemma block_where b n x : ltac2:(tb__ "0|3|
S49S69S6S6A2S73S6S6Vb;Vn;A4S84VL;Vt;A2A3S0S41Vb;Vx;A2S43Vx;S42Vb;Vn;A2A2A2S3S69S4dS6A2M0G0S3S7S7S0S49G0R2S50Vt;A1A3S0S1S4dS72S4dS6R2A3M1S4fR1A1A3S0S41S51VL;G1A2M2Vx;A2S43Vx;S42G2S71S4dS6R2A3A2A2A2A2A2Lp;A2Le;A2F_;F_;").
  Proof using HI HX.
    intros Hin Hx. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U t L HI HX (p, n) Hin) as (g & gm & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4). cbn [fst snd] in *.
    destruct (used_group_region X R U t g gm HI Hu) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
    exists (LMem (SP (prid (am_mem gm)) 0), rg_len rg), (SP (prid (am_mem gm)) 0). split; [exact (footprint_region_In t _ _ Hr Hkd Hl)|]. split; [reflexivity|].
    cbn [fst snd loc_addr]. pose proof (stride_pos _ _ _ _ _ (inv_groups HI g gm Hu)) as Sp. assert (0 <= stride_of gm * i) by nia.
    unfold addr_of, loc_addr in *. destruct (am_mem gm) as [r o]. cbn [prid poff] in *. unfold UNIT, IB in *. lia.
  Qed.
  Lemma page_vs_block b n x : ltac2:(tb__ "0|0|
S49S69S6S6A2S73S6S6Vb;Vn;A4S84VL;Vt;A2A3S0S41Vb;Vx;A2S43Vx;S42Vb;Vn;A2A2A2S4S0S41S36Vx;A2S43Vx;S42S36S8A2A2A2A1F_;F_;").
  Proof using HI HL HLG HSI HV HX Hac Hctx. intros Hin Hx. destruct (block_where b n x Hin Hx) as (e & p & He & _ & Rx). exact (page_vs_footprint e x He Rx). Qed.
  Lemma fp_where e x : ltac2:(tb__ "0|3|
S49S69S4dS6A2Ve;S50Vt;A1A3S0S41S51VL;S72S4dS6Ve;A3M0A2M1Vx;A2S43Vx;S42G1S71S4dS6Ve;A3A2A2A2S2S0S1S4dG0S57Z0A1A3S0S41S5dVL;A1M2Vx;A2S43Vx;S42G2S61A2A2A2A2S3S7S7S0S1S4dG0S4fR1A1A3S0S0S41S8Vx;A2S43Vx;S87VL;A1A2A2S4S0S41S86VC;A1Vx;A2S43Vx;S85VC;A1A2A2A1A2A2Lp;A2A2F_;F_;").
  Proof using HLG HV.
    intros He Hx. pose proof HV as (_ & _ & _ & V5 & _). destruct e as [[o|p] n]; cbn [fst snd] in *.
    - left. unfold footprint in He. destruct He as [E|He].
      + injection E as <- <-. cbn [loc_addr] in Hx. split; [reflexivity | lia].
      + exfalso. apply in_app_iff in He as [He|He]; [apply in_map_iff in He as (? & E & _); discriminate|].
        apply in_flat_map in He as (k & _ & He). destruct (region_of t k) as [rg|]; [|destruct He]. destruct (rg_kind rg); try destruct He.
        destruct (rg_live rg); [destruct He as [E|[]]; discriminate | destruct He].
    - right. exists p. split; [reflexivity|]. destruct (V5 p n He) as (e' & He' & R1' & R2'). destruct (HLG e' He') as (G1 & G2 & G3). rewrite <- (vm_ok_top _ _ _ HV) in G2.
      unfold addr_of in R1', R2'. cbn [loc_addr] in Hx. destruct p as [r o]. cbn [loc_addr] in *. lia.
  Qed.
End AREA.
