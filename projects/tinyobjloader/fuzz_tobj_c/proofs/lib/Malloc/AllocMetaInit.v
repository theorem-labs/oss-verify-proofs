(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "PGSZ"; "region"; "mslot"; "st_areas"; "st_metas"; "rkind"; "st_area_head"; "st_area_tail"; "st_avail_meta_area_count"; "st_avail_meta_count"; "st_free_meta_head"; "st_regions"; "brkst"; "padd"; "st_active"; "st_bounces"; "st_brk"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_seq"; "st_unmap_seq"; "st_usage"; "BrkNever"; "MRaw"; "RkMetaRes"; "astate"; "rg_kind"; "rg_live"; "st_avail_meta"; "st_avail_meta_areas"; "BrkCur"; "METAS_PER_AREA"; "META_SIZE"; "RkMap"; "prid"; "rg_len"; "st_init_done"; "AREA_HDR"; "MFree"; "RkBrk"; "SP"; "ameta"; "mkRegion"; "mupdate"; "set_avail_meta"; "set_avail_meta_area_count"; "set_avail_meta_areas"; "set_avail_meta_count"; "set_brk"; "set_init_done"; "set_regions"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "modulo"; "of_nat"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.INIT"; "tI"; "a"; "L'"; "pnew"; "mnew"; "rr"; "vmI"; "tIpre"; "rgI"; "w2"; "wa"; "w1"; "@Stdlib.Lists.List"; "In"; "incl"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.S0"; "tS"; "C_initS"; "C_secS"; "@Corelib.Init.Datatypes"; "prod"; "list"; "option"; "app"; "fst"; "snd"; "cons"; "nil"; "Some"; "pair"; "bool"; "None"; "true"; "nat"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "mcell"; "footprint"; "loc_addr"; "LCtx"; "image"; "region_of"; "LMem"; "ctx_cells"; "keys"; "ly_reg"; "mc_loc"; "user_blocks"; "Inv"; "MCell"; "MT"; "ly_ctx"; "area_cells"; "CTX_SIZE"; "CTX_init_done"; "CTX_secret"; "crange"; "ly_sec"; "sval"; "usedX"; "CTX_avail_meta_areas"; "CTX_brk"; "VP"; "VSec"; "VZ"; "mc_w"; "memb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "maps_subtract"; "mkVmMapsFull"; "vm_start_brk"; "VmMaps"; "iv_subtract"; "vm_brk"; "vm_init_sp"; "vm_limit"; "vm_mmap_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "range_in_maps"; "blocks"; "topL"; "vm_ok"; "wz"; "addr_of"; "mc_img_hi"; "mc_img_lo"; "img_reserved"; "ledger_ok"; "mc_ctx"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk"; "sd"; "C_brkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit"; "guard_kind"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow"; "Lext"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage"; "map_fp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost"; "am_spec_post"; "s0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "layout_extends"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta"; "am_frame"; "open_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw";
"@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame MallocWfRings MallocWfRepr MallocWfMeta MallocWfGeom
  MallocWfSurgery MallocFooter MallocFooterLemmas MallocLayout MallocIface MallocIfaceI MallocLaws FpLaws WalkArith RingFacts Zones2
  AllocMetaPost AllocMetaImage AllocMetaGrow AllocMetaArea AllocMetaBrk MapsWf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac in_list := solve [ cbn; repeat first [ left; reflexivity | right ] ].

Lemma iv_subtract_other (a sz : word) lo hi : ltac2:(tb__ "0|4|
S3dZ0S84Q40M0Vsz;A2M1A2S3bVlo;Vhi;A2S2S3bS3cS84G0Va;A2M2G1A2Vlo;A2S3bVhi;G2A2A2S4fS55S85G0A1M3G3A2S5eG3G3Va;Vsz;A4S8eVa;Vsz;Vlo;Vhi;A4A3F_;F_;F_;").
Proof.
  intros Hsz Hlh Hd. pose proof (urange a) as Ra. pose proof (urange sz) as Rs. unfold iv_subtract.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. left. reflexivity.
  - replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. left. reflexivity.
Qed.
Lemma maps_subtract_other l lo hi e : ltac2:(tb__ "0|5|
S3dZ0S84Q40M0S5aS85G0A1M1G1Ve;A3A2M2A2S3bVlo;Vhi;A2S2S3bS3cS84G0S59G1G1Ve;A3A2M3G2A2Vlo;A2S3bVhi;G3A2A2S4fS55G1G1A2M4Ve;Vl;A3S4fG4Ve;S8aVl;Vlo;Vhi;A3A3F_;F_;F_;F_;").
Proof.
  intros Hsz Hlh Hd Hin. destruct e as [a sz]. cbn [fst snd] in *.
  exact (in_maps_subtract_intro l lo hi a sz (a, sz) Hin (iv_subtract_other a sz lo hi Hsz Hlh Hd)).
Qed.

Section S0.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (t : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S71VX;VR;VU;Vt;A4").
  Hypothesis HX : xraw X t.
  Hypothesis Hinit : st_init_done t = false.
  Hypothesis HL : layout_ok L t.

  Lemma pristine_facts : ltac2:(tb__ "0|4|
S1S0S56S55S7SaA2M0A1ScVt;A1S5cG0A1A3S1S0S56S7A1SbVt;A1S5cS7A1A3S1S0S14S18Vt;A1S1eA3S1S0S6S10Vt;A1Z0M1A3S1S0S57S7A1M2S12Vt;A1S60S7A1M3A3S1S0S6S11Vt;A1G1A3S1S0G2SeVt;A1G3A3S0G2SfVt;A1G3A3A2A2A2A2A2A2A2").
  Proof using HI Hinit.
    pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&_&_&_&_& CI & _). destruct (CI Hinit) as (M & A & B & AC).
    pose proof (inv_keys HI) as (_ & _ & K3 & _). pose proof (inv_areas HI) as (_ & _ & A1 & A2 & _).
    repeat split; try assumption.
    - destruct (st_free_meta_head t) as [q|] eqn:E; [|reflexivity]. exfalso.
      pose proof (head_key X R U t HI q E) as K. unfold keys in K. rewrite M in K. exact K.
    - exact (K3 A).
    - rewrite A1, A. reflexivity.
    - rewrite A2, A. reflexivity.
  Qed.

  Definition tS : astate := s0 t.
  Lemma tS_eq : ltac2:(tb__ "0|0|
S0S21S52S39S61Vt;A2A3"). Proof using . reflexivity. Qed.
  Lemma xraw_tS : xraw X tS. Proof using HX. intros q Hq. unfold tS, s0. rewrite MT_set_init_done. exact (HX q Hq). Qed.
  Lemma tS_fields : ltac2:(tb__ "0|2|
S1S0S5fS2cS52A1S61A3S1S0S14S18S52A1S1eA3S1S0S56S55S7SaA2A1ScS52A1ScVt;A1A3S1S0S56S7A1SbS52A1SbVt;A1A3S1S0S56S9A1S13S52A1S13Vt;A1A3S1S0S57S7A1M0S12S52A1S12Vt;A1A3S1S0S6S11S52A1S11Vt;A1A3S1S0S6S10S52A1S10Vt;A1A3S1S0S6S19S52A1S19Vt;A1A3S1S0S56G0A1S16S52A1S16Vt;A1A3S1S0S56S6A1M1S1dS52A1S1dVt;A1A3S1S0G1S1cS52A1S1cVt;A1A3S1S0G1S17S52A1S17Vt;A1A3S1S0S6S1bS52A1S1bVt;A1A3S1S0S6S1aS52A1S1aVt;A1A3S1S0S7S25S52A1S25Vt;A1A3S1S0G0SeS52A1SeVt;A1A3S1S0G0SfS52A1SfVt;A1A3S0S7S24S52A1S24Vt;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using HI HL HX Hinit. pose proof pristine_facts as (_ & _ & B & _). unfold tS, s0. destruct t; cbn in *. subst. repeat split; reflexivity. Qed.
  Lemma footprint_tS : ltac2:(tb__ "0|0|
S0S56S55S64S6A2A1S66S52A1S66Vt;A1A3"). Proof using . reflexivity. Qed.
  Lemma user_blocks_tS : ltac2:(tb__ "0|0|
S0S56S55S7S6A2A1S70S52A1S70Vt;A1A3"). Proof using . apply co_user_blocks. reflexivity. Qed.
  Lemma footers_tS : ltac2:(tb__ "0|0|
S0S56S65A1S86S52A1S86Vt;A1A3"). Proof using . apply co_footers. reflexivity. Qed.
  Lemma keys_tS : ltac2:(tb__ "0|0|
S0S56S7A1S6dS52A1S6dVt;A1A3"). Proof using . reflexivity. Qed.
  Lemma MT_tS q : ltac2:(tb__ "0|0|
S0S57SaA1S73S52Vq;A2S73Vt;Vq;A2A3"). Proof using . reflexivity. Qed.
  Lemma region_of_tS k : ltac2:(tb__ "0|0|
S0S57S9A1S6aS52Vk;A2S6aVt;Vk;A2A3"). Proof using . reflexivity. Qed.
  Lemma blocks_tS : ltac2:(tb__ "0|0|
S0S56S55S6S6A2A1S94VL;S52A2S94VL;Vt;A2A3"). Proof using . reflexivity. Qed.
  Lemma layout_ok_tS : layout_ok L tS. Proof using HL. exact HL. Qed.

  Definition C_secS : mcell := ltac2:(tb__ "0|0|
S72S68S78A1U8S80A3").
  Definition C_initS : mcell := ltac2:(tb__ "0|0|
S72S68S77A1U4S81Z1A1A3").

  Lemma image_tS c : ltac2:(tb__ "0|1|
S4fS65Vc;S58S65S69S52A1S86S52A1A3A3S2S0S65Vc;S54A3S2S0S65Vc;S53A3S1S4fS65Vc;S58S65S69Vt;A1S86Vt;A1A3A3S1S3S0S64S6fVc;A1M0S68S78A1A3A1S3S0S64G0S68S77A1A3A1A2A2A2A2F_;").
  Proof using HI HL HX Hinit.
    pose proof tS_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
    pose proof pristine_facts as (_ & _ & PB & _).
    intros Hin. apply in_app_iff in Hin as [Hin|Hin].
    - unfold image in Hin. apply in_app_iff in Hin as [Hin|Hin].
      + unfold ctx_cells in Hin. rewrite F1, F2, F4, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19 in Hin.
        apply in_app_iff in Hin as [Hin|Hin].
        * cbn [In] in Hin.
          unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
            CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in *.
          unfold C_secS, C_initS, CTX_secret, CTX_init_done.
          destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
            first [ left; reflexivity | right; left; reflexivity
                  | right; right; (split; [apply in_app_iff; left; unfold image; apply in_app_iff; left; unfold ctx_cells; apply in_app_iff; left; rewrite Hinit, PB; in_list
                                         | cbn [mc_loc]; split; intros E; injection E as E'; lia]) ].
        * right; right. split; [apply in_app_iff; left; unfold image; apply in_app_iff; left; unfold ctx_cells; apply in_app_iff; right; exact Hin|].
          destruct (AllocMetaGrow.ctx_maps_loc _ c Hin) as (o & -> & Ho). unfold CTX_active, CTX_secret, CTX_init_done in *. cbn [mc_loc]. split; intros E; injection E as E'; lia.
      + right; right. rewrite F4, (co_areas_cells t tS F3), (co_used_metas t tS F3) in Hin.
        destruct (AllocMetaGrow.old_noctx_loc X R U t HI HX c (or_introl Hin)) as (H1 & q & Hq). split; [exact H1|]. rewrite Hq. split; discriminate.
    - right; right. rewrite footers_tS in Hin.
      destruct (AllocMetaGrow.old_noctx_loc X R U t HI HX c (or_intror Hin)) as (H1 & q & Hq). split; [exact H1|]. rewrite Hq. split; discriminate.
  Qed.
  Lemma C_secS_image : In C_secS (image tS).
  Proof using HI HL HX Hinit. unfold image, ctx_cells. apply in_app_iff. left. apply in_app_iff. left. pose proof tS_fields as (F1 & _). rewrite F1. left. reflexivity. Qed.
  Lemma C_initS_image : In C_initS (image tS).
  Proof using HI HL HX Hinit. unfold image, ctx_cells. apply in_app_iff. left. apply in_app_iff. left. pose proof tS_fields as (F1 & _). rewrite F1. right. left. reflexivity. Qed.

  Variables (C : mconsts) (vm : VmMaps).
  Hypothesis HV : ltac2:(tb__ "0|0|
S96VL;Vt;Vvm;A3").
  Hypothesis HB : bounded t.
  Lemma vm_ok_tS : ltac2:(tb__ "0|0|
S96VL;S52Vvm;A3").
  Proof using HV. exact HV. Qed.
  Lemma bounded_tS : bounded tS. Proof using HB. exact HB. Qed.

  Lemma Inv_sdI : ltac2:(tb__ "0|0|
S71VX;VR;VU;S9fS52A1A4").
  Proof using HI Hinit.
    pose proof pristine_facts as (_ & _ & B & _). unfold AllocMetaBrk.sd, tS, s0.
    apply (Inv_init_brk_dead X R U t HI). rewrite B. discriminate.
  Qed.

  Lemma image_sdI c : ltac2:(tb__ "0|1|
S4fS65Vc;S58S65S69S9fS52A1M0A1S86G0A1A3A3S2S0S65Vc;Sa0A3S1S4fS65Vc;S58S65S69S52A1S86S52A1A3A3S3S0S64S6fVc;A1S68S7eA1A3A1A2A2F_;").
  Proof using HI HL HX Hinit.
    intros Hin.
    pose proof pristine_facts as (PM & PA & PB & _).
    assert (CTX : forall u d, In d (ctx_cells u) -> mc_loc d = LCtx CTX_brk ->
              d = MCell (LCtx CTX_brk) 8 (match st_brk u with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end)).
    { intros u d Hd Ed. unfold ctx_cells in Hd. apply in_app_iff in Hd as [Hd|Hd].
      - cbn [In] in Hd. unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
          CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in *.
        destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc] in Ed; try (injection Ed as Ed'; lia). reflexivity.
      - exfalso. unfold CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces, CTX_brk in *.
        apply in_app_iff in Hd as [Hd|Hd]; [|apply in_app_iff in Hd as [Hd|Hd]; [|apply in_app_iff in Hd as [Hd|Hd]]];
          apply in_map_iff in Hd as (k & <- & Hk); apply in_seq in Hk; cbn [mc_loc] in Ed; injection Ed as Ed'; lia. }

    assert (NOAREAS : forall u, st_areas u = [] -> st_metas u = [] -> image u ++ footer_cells u = ctx_cells u).
    { intros u A M. unfold image, footer_cells, used_metas. rewrite A, M. cbn. rewrite ?app_nil_r. reflexivity. }
    pose proof (AllocMetaBrk.sd_fields tS (proj1 tS_fields)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
    pose proof tS_fields as (T1 & T2 & T3 & T4 & _).
    rewrite (NOAREAS (AllocMetaBrk.sd tS)) in Hin by (rewrite ?F3, ?F4, ?T3, ?T4; assumption).
    rewrite (NOAREAS tS) by (rewrite ?T3, ?T4; assumption).
    destruct (loc_eq_dec (mc_loc c) (LCtx CTX_brk)) as [E|NE].
    - left. rewrite (CTX _ c Hin E). rewrite F1. reflexivity.
    - right. split; [|exact NE].
      clear - Hin NE F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19.
      unfold ctx_cells in Hin |- *. change (st_init_done (AllocMetaBrk.sd tS)) with (st_init_done tS) in Hin.
      rewrite F4, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19 in Hin.
      apply in_app_iff in Hin as [Hc|Hc]; [|apply in_app_iff; right; exact Hc].
      apply in_app_iff. left.
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
        [do 0 right|do 1 right|do 2 right|do 3 right|do 4 right|do 5 right|do 6 right|do 7 right|do 8 right|do 9 right|do 10 right|do 11 right|];
        try (left; reflexivity). exfalso. apply NE. reflexivity.
  Qed.
End S0.

Inductive guard_kind := GK_kept | GK_ok | GK_dead.

Section INIT.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (t : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S71VX;VR;VU;Vt;A4").
  Hypothesis HX : xraw X t.
  Hypothesis Hinit : st_init_done t = false.
  Hypothesis HL : layout_ok L t.

  Definition rr : nat := length (st_regions t).
  Definition pnew : sptr := SP rr PGSZ.
  Definition mnew : sptr := padd pnew AREA_HDR.
  Definition tI : astate := s_INok t.
  Definition rgI : region := ltac2:(tb__ "0|0|
S32S2fS3eZ2S8A2S5cS6A1S61A4").

  Lemma PF : ltac2:(tb__ "0|4|
S1S0S56S55S7SaA2M0A1ScVt;A1S5cG0A1A3S1S0S56S7A1SbVt;A1S5cS7A1A3S1S0S14S18Vt;A1S1eA3S1S0S6S10Vt;A1Z0M1A3S1S0S57S7A1M2S12Vt;A1S60S7A1M3A3S1S0S6S11Vt;A1G1A3S1S0G2SeVt;A1G3A3S0G2SfVt;A1G3A3A2A2A2A2A2A2A2").
  Proof using HI Hinit. exact (pristine_facts X R U t HI Hinit). Qed.

  Lemma SPECI (zq zu : Z) : ltac2:(tb__ "0|0|
Sa4VX;VR;VU;Vt;S5eS57S7A1S21S5dS7S47A2S43A4A5").
  Proof using HI Hinit.
    pose proof PF as (_ & _ & Hbrk & Hac & Hhd & Hcnt & _).
    pose proof (yields_IN t Hhd Hcnt Hac Hbrk zq 1 zu 0 0) as Y. unfold r_IN in Y. cbn [Z.eqb] in Y.
    exact (am_spec_of_yields X R U t HI _ _ Y).
  Qed.
  Lemma HII : ltac2:(tb__ "0|0|
S71S5bS7S47VX;A3VR;VU;S43A4"). Proof using HI Hinit. exact (proj1 (SPECI 0 0)). Qed.

  Lemma tI_fields : ltac2:(tb__ "0|3|
S1S0S56S9A1S13S43A1S58S9S13Vt;A1S5bS9S4bS5cS9A1A3A3A3S1S0S56S7A1SbS43A1S58S7SbVt;A1S5bS7S46S5cS7A1A3A3A3S1S0S56S55S7SaA2A1ScS43A1S33ScVt;A1S47S1fA3A3S1S0S14S18S43A1S26S48Z2A2A3S1S0S5fS2cS43A1S61A3S1S0S57S7A1M0S12S43A1S60S7A1A3S1S0S7S24S43A1S15S47S28A2A3S1S0S6S11S43A1S42S27Z1A2A3S1S0S6S10S43A1Z0A3S1S0S6S19S43A1S19Vt;A1A3S1S0G0SeS43A1S5dS7S46A2M1A3S1S0G0SfS43A1G1A3S1S0S7S25S43A1S15S46Z1000A2A3S1S0S56G0A1S16S43A1S16Vt;A1A3S1S0S56S6A1M2S1dS43A1S1dVt;A1A3S1S0G2S1cS43A1S1cVt;A1A3S1S0G2S17S43A1S17Vt;A1A3S1S0S6S1bS43A1S1bVt;A1A3S0S6S1aS43A1S1aVt;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using HI HL HX Hinit.
    pose proof PF as (M & A & B & AC & HD & CN & AH & AT).
    unfold tI, s_INok, take, open_st, rgI, mnew, pnew, rr, in_p, in_r, s0. destruct t; cbn -[Z.mul Z.add Z.sub Z.shiftl padd METAS_PER_AREA] in *.
    subst. cbn -[Z.mul Z.add Z.sub padd METAS_PER_AREA]. repeat split; reflexivity.
  Qed.

  Lemma region_of_tI k : ltac2:(tb__ "0|1|
S0S57S9A1M0S6aS43Vk;A2S5fG0L_;SacVk;S48A2S5dS9S4bA2S6aVt;Vk;A2X5fx2A3").
  Proof using HI HL HX Hinit.
    pose proof tI_fields as (F1 & _). unfold region_of. rewrite F1. unfold rr.
    destruct (Nat.eqb k (length (st_regions t))) eqn:E.
    - apply Nat.eqb_eq in E. subst k. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - apply Nat.eqb_neq in E. destruct (Nat.lt_ge_cases k (length (st_regions t))) as [Hlt|Hge].
      + rewrite nth_error_app1 by exact Hlt. reflexivity.
      + rewrite nth_error_app2 by lia. replace (nth_error (st_regions t) k) with (@None region) by (symmetry; apply nth_error_None; lia).
        destruct (k - length (st_regions t))%nat as [|k'] eqn:Ek; [lia|]. cbn. destruct k'; reflexivity.
  Qed.

  Lemma mnew_prid : prid mnew = rr. Proof using . reflexivity. Qed.
  Lemma fresh_slot q : ltac2:(tb__ "0|0|
S0S62S2aVq;A1S48A3S0S57SaA1S73Vt;Vq;A2S60SaA1A3F_;").
  Proof using HI.
    intros Hq. destruct (MT t q) as [x|] eqn:E; [|reflexivity]. exfalso.
    pose proof (key_below X R U t HI q (MT_Some_In_keys _ _ _ E)) as B. unfold rr in Hq. lia.
  Qed.
  Lemma pnew_fresh : ltac2:(tb__ "0|0|
S3S4fS7S46SbVt;A1A3A1").
  Proof using HI Hinit. pose proof PF as (_ & A & _). rewrite A. intros []. Qed.

  Definition tIpre : astate := ltac2:(tb__ "0|2|
S34S15S47S28A2S37S42S27Z1M0A2SaaS46S38S26S48Z2A2S36S46S35G0S3aS58S9S13Sa5Vt;A1M1A1S5bS9S4bS5cS9A1A3A3G1A2A2A2A2A2A2A2").
  Lemma tI_upd : ltac2:(tb__ "0|0|
S0S21S43Sa8S47S1fS4aA3A3").
  Proof using . reflexivity. Qed.
  Lemma tIpre_fields : ltac2:(tb__ "0|0|
S1S0S56S55S7SaA2A1ScS4aA1ScVt;A1A3S1S0S56S7A1SbS4aA1S58S7SbVt;A1S5bS7S46S5cS7A1A3A3A3S0S56S65A1S6cS4aA1S6cS43A1A3A2A2").
  Proof using . repeat split; reflexivity. Qed.

  Lemma area_cells_tI : ltac2:(tb__ "0|1|
S0S56S65A1S75S43S46S60S7A1M0A3S75Vt;S46G0A3A3").
  Proof using HI HL HX Hinit.
    pose proof tI_fields as (_ & _ & F3 & _).
    assert (E : forall k, meta_slot_cells (padd pnew (AREA_HDR + META_SIZE * Z.of_nat k)) (mlookup (st_metas tI) (padd pnew (AREA_HDR + META_SIZE * Z.of_nat k)))
                        = meta_slot_cells (padd pnew (AREA_HDR + META_SIZE * Z.of_nat k)) (mlookup (st_metas t) (padd pnew (AREA_HDR + META_SIZE * Z.of_nat k)))).
    { intros k. rewrite F3. rewrite mlookup_mupdate.
      assert (FR : mlookup (st_metas t) (padd pnew (AREA_HDR + META_SIZE * Z.of_nat k)) = None) by (apply fresh_slot; reflexivity).
      rewrite FR. destruct (sptr_eqb _ _); [apply meta_slot_cells_raw | reflexivity]. }
    unfold area_cells. f_equal.
    induction (seq 0 (Z.to_nat METAS_PER_AREA)) as [|k l IH]; [reflexivity|]. cbn [flat_map]. rewrite (E k), IH. reflexivity.
  Qed.

  Theorem image_tIC c : ltac2:(tb__ "0|1|
S4fS65Vc;S58S65S69S43A1S86S43A1A3A3S2S4fS65Vc;S6cS43A1A3S2S1S3S0S56S7A1SbVt;A1M0S5cS7A1A3A1S0S65Vc;S72S6bS15S51S7G0S30U0Z0A2A3Z8A2A1U8S7fS46A1A3A3A2S2S4fS65Vc;S75S43S46S60S7A1A3A3S1S4fS65Vc;S58S65S69Vt;A1S86Vt;A1A3A3S4S7S7S0S64S6fVc;A1S6bR1A1A3Lq;A2A2A2A2A2F_;").
  Proof using HI HL HX Hinit.
    pose proof tIpre_fields as (P1 & P2 & P3).
    assert (NU : nonused (MT tIpre mnew)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) mnew) with (MT t mnew); rewrite (fresh_slot mnew mnew_prid); exact I).
    intros Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite tI_upd in Hin. destruct (uf_image_In tIpre mnew MRaw NU I c Hin) as [H|H].
      + unfold image in H. apply in_app_iff in H as [H|H]; [left; rewrite <- P3; exact H|].
        rewrite P2, (co_areas_cells t tIpre P1), (co_used_metas t tIpre P1) in H.
        apply in_app_iff in H as [H|H].
        * destruct (ap_areas_cells_In t t pnew eq_refl (st_areas t) c H) as [Ho|[Htn|Hnew]].
          -- right; right; right. apply (AllocMetaGrow.old_noctx_loc X R U t HI HX). left. apply in_app_iff. left. exact Ho.
          -- right; left. exact Htn.
          -- right; right; left. rewrite area_cells_tI. exact Hnew.
        * right; right; right. apply (AllocMetaGrow.old_noctx_loc X R U t HI HX). left. apply in_app_iff. right. exact H.
      + right; right; left. rewrite area_cells_tI. unfold area_cells. apply in_app_iff. right.
        apply in_flat_map. exists 0%nat. split; [apply in_seq; unfold METAS_PER_AREA; lia|].
        replace (padd pnew (AREA_HDR + META_SIZE * Z.of_nat 0)) with mnew by (unfold mnew; f_equal).
        change (mlookup (st_metas t) mnew) with (MT t mnew). rewrite (fresh_slot mnew mnew_prid). rewrite meta_slot_cells_raw in H. exact H.
    - right; right; right. apply (AllocMetaGrow.old_noctx_loc X R U t HI HX). right.
      rewrite tI_upd, (uf_footers tIpre mnew MRaw NU I), (co_footers t tIpre P1) in Hin. exact Hin.
  Qed.

  Lemma image_t_ctx c : ltac2:(tb__ "0|0|
S4fS65Vc;S58S65S69Vt;A1S86Vt;A1A3A3S4fS65Vc;S6cVt;A1A3F_;").
  Proof using HI Hinit.
    pose proof PF as (M & A & _). intros Hin. apply in_app_iff in Hin as [Hin|Hin].
    - unfold image in Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact Hin|]. exfalso.
      rewrite A in Hin. unfold used_metas in Hin. rewrite M in Hin. cbn in Hin. exact Hin.
    - exfalso. unfold footer_cells, used_metas in Hin. rewrite M in Hin. cbn in Hin. exact Hin.
  Qed.

  Lemma ctx_cells_tIC c : ltac2:(tb__ "0|1|
S4fS65Vc;S6cS43A1A3S2S4S6S6S4S62S62S4S7bS7bS1S0S65Vc;S72S68R3A1R2R1A3A3S1S9eU0R2A2S2S1S3bZ0R3A2S3bS3cR3S40R2A1A2M0ZcA2A2S2S1S3bZ10R3A2S3bG0Z50A2A2S1S3bZ398R3A2S3bG0Z3a0A2A2A2A2A2A2Lval;A2Lw;A2Lo;A2S1S4fS65Vc;S6cVt;A1A3S3S0S64S6fVc;A1S68S7dA1A3A1A2A2F_;").
  Proof using HI HL HX Hinit.
    intros Hin.
    pose proof tI_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
    unfold ctx_cells in Hin. rewrite F2, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19 in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    - cbn [In] in Hin.
      unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
        CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in *.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
        first [ left; eexists _, _, _; (split; [reflexivity|]); (split; [cbn; lia | cbn; lia])
              | right; (split; [unfold ctx_cells; apply in_app_iff; left; rewrite ?Hinit; in_list | cbn [mc_loc]; intros E; injection E as E'; lia]) ].
    - right. split; [unfold ctx_cells; apply in_app_iff; right; exact Hin|].
      destruct (AllocMetaGrow.ctx_maps_loc _ c Hin) as (o & -> & Ho). unfold CTX_active, CTX_avail_meta_areas in *. intros E. injection E as E'. lia.
  Qed.

  Lemma fp_t : ltac2:(tb__ "0|1|
S0S56S55S64S6A2M0A1S66Vt;A1S5bG0S5eS64S6S68Z0A1S76A4Sa3Vt;A1A3A3").
  Proof using HI Hinit. pose proof PF as (_ & A & _). rewrite footprint_eq, A. reflexivity. Qed.
  Lemma fp_tI e : ltac2:(tb__ "0|1|
S5S4fS55S64S6A2M0Ve;S66S43A1A3S2S4fG0Ve;S66Vt;A1A3S0G0Ve;S5eS64S6S6bS46A1S8A4A3A2A2").
  Proof using HI HL HX Hinit.
    pose proof tI_fields as (F1 & F2 & _). rewrite !AllocMetaGrow.In_footprint, F2.
    rewrite (map_fp_regions_only (set_regions (st_regions t ++ [rgI]) t) tI) by (rewrite F1; reflexivity).
    rewrite (map_fp_app_nonmap t rgI) by (left; discriminate).
    rewrite map_app, in_app_iff. cbn [map In]. intuition congruence.
  Qed.
  Lemma ub_tI : ltac2:(tb__ "0|0|
S0S56S55S7S6A2A1S70S43A1S70Vt;A1A3").
  Proof using HI.
    pose proof tIpre_fields as (P1 & _).
    assert (NU : nonused (MT tIpre mnew)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) mnew) with (MT t mnew); rewrite (fresh_slot mnew mnew_prid); exact I).
    rewrite tI_upd, (uf_user_blocks tIpre mnew MRaw NU I). exact (co_user_blocks t tIpre P1).
  Qed.
  Lemma footers_tI : ltac2:(tb__ "0|0|
S0S56S65A1S86S43A1S86Vt;A1A3").
  Proof using HI.
    pose proof tIpre_fields as (P1 & _).
    assert (NU : nonused (MT tIpre mnew)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) mnew) with (MT t mnew); rewrite (fresh_slot mnew mnew_prid); exact I).
    rewrite tI_upd, (uf_footers tIpre mnew MRaw NU I). exact (co_footers t tIpre P1).
  Qed.

  Variables (C : mconsts) (vm : VmMaps).
  Hypothesis Hctx : ltac2:(tb__ "0|0|
S0S6S74VL;A1S9dVC;A1A3").
  Hypothesis HSI : statics_in_image C.
  Hypothesis HV : ltac2:(tb__ "0|0|
S96VL;Vt;Vvm;A3").
  Hypothesis HLG : ledger_ok C vm.
  Hypothesis HIR : img_reserved C vm.
  Hypothesis HB : bounded t.
  Hypothesis HMW : maps_wf vm.

  Definition a : Z := ly_brk0 L.

  Hypothesis Ha_lo : PGSZ <= a.
  Hypothesis Ha_ceil : ltac2:(tb__ "0|0|
S3bS3cS44S3eZ2S8A2A2S95VL;A1A2").
  Hypothesis Hfree : ltac2:(tb__ "0|4|
S55S85Q40M0A1M1G1A2M2S4fG2R1S58G2S89Vvm;A1S87Vvm;A1A3A3S2S3bS3cS84G0S59G1G1R2A3A2M3S84G0S5aG1G1R2A3A2A2S44A2S3bS3cS44S3eZ2S8A2A2G3A2A2F_;Fe;").

  Definition L' : layout := ltac2:(tb__ "0|0|
Sa2VL;S48S44A3").
  Definition wa : word := wz a.
  Definition w2 : word := wz (2 * PGSZ).
  Definition w1 : word := wz PGSZ.

  Definition vmI (gk : guard_kind) : VmMaps := ltac2:(tb__ "0|c|
Sa1S8dLgk;Vgk;S8bS89Vvm;A1M0S5bS55S85Q40A1M1G1A2M2S5eG1G1S4dS4cA4S87Vvm;A1A3M3S88Vvm;A1M4S8cVvm;A1M5S97S3cS44S3eZ2S8A2A2A1M6S91Vvm;A1M7S92Vvm;A1M8S90Vvm;A1M9A8S8bG0G3S5bG2S5eG1G1S4dS4eA4S8aG4S44S3cS44S8A2MaA3MbA3G5G6G7G8G9A8S8bG0S8aG3S44GaA3GbG5G6G7G8G9A8Xa1x3").

  Lemma brk0_facts : ltac2:(tb__ "0|1|
S1S0S6S84Q40M0S8fVvm;A1A2S44A3S1S0S6S84G0S8cVvm;A1A2S44A3S0S6S3fS44S8A2Z0A3A2A2").
  Proof using HI HV Hinit. pose proof PF as (_ & _ & B & _). pose proof HV as (_ & _ & V3 & _). rewrite B in V3. exact V3. Qed.
  Lemma a_facts : ltac2:(tb__ "0|2|
S1S3bS8S44A2S1S3dS3cS44S3eZ2M0S8A2A2S41G0Z2fA2A2S1S1S3bZ0M1S44A2S3dS44S41G0Z40A2A2A2S0S6S3fS44S8A2G1A3A2A2A2").
  Proof using HI HV Ha_ceil Ha_lo Hinit. pose proof brk0_facts as (_ & _ & M). top_ranges. unfold PGSZ in *. lia. Qed.
  Lemma ua : bv_unsigned wa = a. Proof using HI HV Ha_ceil Ha_lo Hinit. pose proof a_facts. unfold wa, wz. apply u64. lia. Qed.
  Lemma u2 : ltac2:(tb__ "0|0|
S0S6S84Q40S4cA2S3eZ2S8A2A3"). Proof using . reflexivity. Qed.
  Lemma u1 : bv_unsigned w1 = PGSZ. Proof using . reflexivity. Qed.
  Lemma ubrk : ltac2:(tb__ "0|1|
S0S6S84Q40S97S3cS44S3eZ2S8A2A2M0A1A2G0A3"). Proof using HI HV Ha_ceil Ha_lo Hinit. pose proof a_facts. unfold wz. apply u64. unfold PGSZ in *. lia. Qed.

  Lemma grant_vs_image x : ltac2:(tb__ "0|0|
S1S3bS9aVC;A1Vx;A2S3dVx;S99VC;A1A2A2S3S1S3bS44Vx;A2S3dVx;S3cS44S3eZ2S8A2A2A2A2A1F_;").
  Proof using HIR Hfree. intros Hx Hin. destruct (HIR x Hx) as (e & He & Hex). pose proof (Hfree e ltac:(apply in_app_iff; left; exact He)). lia. Qed.
  Lemma grant_vs_maps e x : ltac2:(tb__ "0|3|
S4fS55S85Q40M0A1M1G1A2Ve;S87Vvm;A1A3S1S3bS84G0S59G1G1Ve;A3A2M2Vx;A2S3dVx;S3cG2S84G0S5aG1G1Ve;A3A2A2A2A2S3S1S3bS44Vx;A2S3dVx;S3cS44S3eZ2S8A2A2A2A2A1F_;F_;").
  Proof using Hfree. intros He Hx Hin. pose proof (Hfree e ltac:(apply in_app_iff; right; exact He)). lia. Qed.
  Lemma grant_vs_footprint e x : ltac2:(tb__ "0|1|
S4fS55S64S6A2Ve;S66Vt;A1A3S1S3bS67VL;S59S64S6Ve;A3A2M0Vx;A2S3dVx;S3cG0S5aS64S6Ve;A3A2A2A2S3S1S3bS44Vx;A2S3dVx;S3cS44S3eZ2S8A2A2A2A2A1F_;F_;").
  Proof using HI HIR HSI HV Hctx Hfree Hinit.
    intros He Hx. pose proof HV as (_ & _ & _ & V5 & _). destruct e as [[o|p] n].
    - pose proof HSI as (_&_&_&_&_&_&_&_&_& [C1 C2] &_). cbn [fst snd loc_addr] in Hx.
      rewrite fp_t in He. destruct He as [E|He].
      + injection E as <- <-. apply grant_vs_image. rewrite Hctx in Hx. lia.
      + exfalso. apply in_flat_map in He as (k & _ & He). destruct (region_of t k) as [rg|]; [|destruct He]. destruct (rg_kind rg); try destruct He.
        destruct (rg_live rg); [destruct He as [E|[]]; discriminate | destruct He].
    - destruct (V5 p n He) as (e' & He' & R1 & R2). cbn [fst snd loc_addr] in Hx. unfold addr_of in R1, R2. cbn [loc_addr] in R1, R2.
      apply (grant_vs_maps e' x He'). destruct p; cbn in *. lia.
  Qed.
  Lemma fp_size e : ltac2:(tb__ "0|0|
S4fS55S64S6A2Ve;S66Vt;A1A3S3dZ0S5aS64S6Ve;A3A2F_;").
  Proof using HV. exact (AllocMetaArea.fp_size t L vm HV e). Qed.

  Lemma L'_ext : ltac2:(tb__ "0|0|
Sa6VL;S45S48A3"). Proof using . apply Lext_extends. Qed.
  Lemma L'_ctx : ltac2:(tb__ "0|0|
S0S6S74S45A1S74VL;A1A3"). Proof using . reflexivity. Qed.
  Lemma L'_sec : ltac2:(tb__ "0|0|
S0S6S7aS45A1S7aVL;A1A3"). Proof using . reflexivity. Qed.
  Lemma L'_brk0 : ly_brk0 L' = a. Proof using . reflexivity. Qed.
  Lemma L'_reg_new : ltac2:(tb__ "0|0|
S0S6S6eS45S48A2S44A3"). Proof using . apply Lext_reg. Qed.
  Lemma L'_top : ltac2:(tb__ "0|0|
S0S6S95S45A1S95VL;A1A3"). Proof using . reflexivity. Qed.
  Lemma L'_fp e : ltac2:(tb__ "0|1|
S4fS55S64S6A2Ve;S66Vt;A1A3S0S6S67S45S59S64S6Ve;A3M0A2S67VL;G0A2A3F_;").
  Proof using HI. intros He. exact (loc_addr_ext L L' rr _ L'_ext (footprint_below X R U t HI e He)). Qed.
  Lemma L'_crange e : ltac2:(tb__ "0|0|
S4fS55S64S6A2Ve;S66Vt;A1A3S0S55S6S6A2S79S45Ve;A2S79VL;Ve;A2A3F_;").
  Proof using HI. intros He. unfold crange. rewrite (L'_fp e He). reflexivity. Qed.
  Lemma L'_ub b : ltac2:(tb__ "0|1|
S4fS55S7S6A2Vb;S70Vt;A1A3S0S6S67S45S6bS59S7S6Vb;A3A1M0A2S67VL;G0A2A3F_;").
  Proof using HI HX. intros Hb. apply (loc_addr_ext L L' rr _ L'_ext). cbn. exact (user_block_below X R U t HI HX b Hb). Qed.
  Lemma L'_addr_of q : ltac2:(tb__ "0|0|
S9eS2aVq;A1S48A2S0S6S98S45Vq;A2S98VL;Vq;A2A3F_;").
  Proof using . intros Hq. unfold addr_of. apply (loc_addr_ext L L' rr _ L'_ext). exact Hq. Qed.
  Lemma L'_pnew : ltac2:(tb__ "0|0|
S0S6S67S45S6bS46A1A2S3cS44S8A2A3").
  Proof using . cbn [loc_addr pnew]. unfold pnew. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.
  Lemma L'_mnew : ltac2:(tb__ "0|0|
S0S6S98S45S47A2S3cS3cS44S8A2S2dA2A3").
  Proof using . unfold addr_of, mnew, pnew. cbn. rewrite Nat.eqb_refl. lia. Qed.
  Lemma OLDREG k rg : ltac2:(tb__ "0|0|
S0S57S9A1S6aVt;Vk;A2S5dS9Vrg;A2A3S0S6S6eS45Vk;A2S6eVL;Vk;A2A3F_;").
  Proof using . intros Hk. unfold L'. apply Lext_old. pose proof (region_of_lt _ _ _ Hk). unfold rr. lia. Qed.

  Theorem layout_ok_tI : layout_ok L' tI.
  Proof using HI HIR HL HSI HV HX Ha_ceil Ha_lo Hctx Hfree Hinit.
    pose proof HL as (A & B & Cc & D). pose proof a_facts as (A1 & A2 & A3 & A4).
    split; [rewrite L'_ctx; exact A|]. split.
    { intros k rg Hk Hl. rewrite region_of_tI in Hk. destruct (Nat.eqb k rr) eqn:E.
      - apply Nat.eqb_eq in E. subst k. rewrite L'_reg_new. exact A4.
      - apply Nat.eqb_neq in E. unfold L'. rewrite Lext_old by exact E. exact (B k rg Hk Hl). }
    pose proof tI_fields as (F1 & F2 & _).
    assert (NEWR : crange L' (LMem pnew, PGSZ) = (a + PGSZ, PGSZ)) by (unfold crange; cbn [fst snd]; rewrite L'_pnew; reflexivity).
    assert (DISJ : forall e, In e (footprint t) -> ranges_disjoint (crange L' e) (crange L' (LMem pnew, PGSZ)) /\ ranges_disjoint (crange L' (LMem pnew, PGSZ)) (crange L' e)).
    { intros e He. rewrite (L'_crange e He), NEWR. unfold ranges_disjoint, crange. cbn [fst snd].
      pose proof (fp_size e He) as SZ.
      destruct (Z_le_dec (loc_addr L (fst e) + snd e) (a + PGSZ)); [lia|].
      destruct (Z_le_dec (a + PGSZ + PGSZ) (loc_addr L (fst e))); [lia|]. exfalso.
      destruct (Z_le_dec (loc_addr L (fst e)) (a + PGSZ)).
      - apply (grant_vs_footprint e (a + PGSZ) He); unfold PGSZ in *; lia.
      - apply (grant_vs_footprint e (loc_addr L (fst e)) He); unfold PGSZ in *; lia. }
    assert (FP2 : footprint tI = ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ (LMem pnew, PGSZ) :: map_fp t).
    { rewrite footprint_eq, F2, map_app. rewrite (map_fp_regions_only (set_regions (st_regions t ++ [rgI]) t) tI) by (rewrite F1; reflexivity).
      rewrite (map_fp_app_nonmap t rgI) by (left; discriminate). cbn [map]. rewrite <- app_assoc. reflexivity. }
    assert (FP0 : footprint t = ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ map_fp t) by (rewrite footprint_eq; reflexivity).
    split.
    - rewrite FP2, map_app.
      change (map (crange L') ((LMem pnew, PGSZ) :: map_fp t)) with (crange L' (LMem pnew, PGSZ) :: map (crange L') (map_fp t)).
      assert (EQ0 : map (crange L') ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ map (crange L') (map_fp t) = map (crange L') (footprint t)).
      { rewrite FP0, map_app. reflexivity. }
      apply pairwise_insert.
      + rewrite EQ0. rewrite (map_ext_in (crange L') (crange L) (footprint t) L'_crange). exact Cc.
      + intros y Hy. rewrite EQ0 in Hy. apply in_map_iff in Hy as (e & <- & He). split; [apply (proj2 (DISJ e He)) | apply (proj1 (DISJ e He))].
    - intros rg Hrg. apply fp_tI in Hrg as [Hrg| ->].
      + rewrite (L'_crange rg Hrg). exact (D rg Hrg).
      + rewrite NEWR. cbn [fst snd]. unfold PGSZ in *. lia.
  Qed.

  Lemma region_live_t k rg : ltac2:(tb__ "0|0|
S0S57S9A1S6aVt;Vk;A2S5dS9Vrg;A2A3S0SdS22Vrg;A1S20A3S0S5fS23Vrg;A1S61A3F_;F_;").
  Proof using HI. intros Hk Hkd. pose proof (inv_areas HI) as (_&_&_&_&A5&_). exact (proj1 (A5 k rg Hk Hkd)). Qed.
  Lemma old_region_vs_grant k rg x : ltac2:(tb__ "0|2|
S0S57S9A1S6aVt;Vk;A2S5dS9Vrg;A2A3S0S5fS23Vrg;A1S61A3S2S0SdS22Vrg;A1M0S29A3S0SdG0S20A3A2S1S3bS6eVL;Vk;A2M1Vx;A2S3dVx;S3cG1S2bVrg;A1A2A2A2S3S1S3bS44Vx;A2S3dVx;S3cS44S3eZ2S8A2A2A2A2A1F_;F_;F_;F_;").
  Proof using HV Hfree.
    intros Hk Hl Hkd Hx. pose proof HV as (V1 & V2 & _ & _ & _ & _ & X3 & X4 & _).
    destruct (X4 k rg Hk Hl) as [B1 B2]. pose proof (X3 k rg Hk Hl) as B3. top_ranges.
    assert (IN : In (wz (ly_reg L k), wz (rg_len rg)) (vm_maps vm)).
    { destruct Hkd as [Hkd|Hkd]; [exact (V1 k rg Hk Hl Hkd) | exact (proj1 (V2 k rg Hk Hkd))]. }
    apply (grant_vs_maps _ x IN). cbn [fst snd]. unfold wz. rewrite !u64 by (unfold PGSZ in *; lia). exact Hx.
  Qed.

  Lemma old_entry_kept gk k rg : ltac2:(tb__ "0|4|
S0S57S9A1S6aVt;Vk;A2S5dS9Vrg;A2A3S0S5fS23Vrg;A1S61A3S2S0SdS22Vrg;A1M0S29A3S0SdG0S20A3A2S4fS55S85Q40A1M1G1A2M2S5eG1G1S97S6eVL;Vk;A2A1S97S2bVrg;A1A1A4M3S87Vvm;A1A3S4fG2G3S87S49Vgk;A1A1A3F_;F_;F_;F_;").
  Proof using HI HV Ha_ceil Ha_lo Hfree Hinit.
    intros Hk Hl Hkd Hin. pose proof HV as (_ & _ & _ & _ & _ & _ & X3 & X4 & _). pose proof a_facts as (A1 & A2 & A3 & A4).
    destruct (X4 k rg Hk Hl) as [B1 B2]. pose proof (X3 k rg Hk Hl) as B3. top_ranges.
    destruct gk; cbn [vmI vm_maps]; [right; exact Hin | right; exact Hin |].
    apply maps_subtract_other; [cbn [snd]; unfold wz; rewrite u64 by (unfold PGSZ in *; lia); unfold PGSZ in *; lia | unfold PGSZ; lia | | right; exact Hin].
    cbn [fst snd]. unfold wz. rewrite !u64 by (unfold PGSZ in *; lia).
    pose proof (grant_vs_maps _ (ly_reg L k) Hin) as G1. pose proof (grant_vs_maps _ a Hin) as G2. cbn [fst snd] in G1, G2. unfold wz in G1, G2.
    rewrite !u64 in G1, G2 by (unfold PGSZ in *; lia). unfold PGSZ in *. lia.
  Qed.

  Lemma page_in_maps gk : ltac2:(tb__ "0|0|
S93S87S49Vgk;A1A1S3cS44S8A2S8A3").
  Proof using HI HV Ha_ceil Ha_lo Hinit.
    pose proof a_facts as (A1 & A2 & A3 & A4).
    destruct gk; cbn [vmI vm_maps].
    - apply range_in_maps_head; cbn [fst snd]; rewrite ?ua, ?u2; unfold PGSZ in *; lia.
    - apply range_in_maps_head; cbn [fst snd]; rewrite ?ua, ?u2; unfold PGSZ in *; lia.
    - apply maps_subtract_keeps; [unfold PGSZ; lia | lia | unfold PGSZ in *; lia | right; lia |].
      apply range_in_maps_head; cbn [fst snd]; rewrite ?ua, ?u2; unfold PGSZ in *; lia.
  Qed.

  Lemma old_range_kept gk x n : ltac2:(tb__ "0|0|
S3dZ0Vn;A2S2S3bS3cVx;Vn;A2S44A2S3bS3cS44S3eZ2S8A2A2Vx;A2A2S93S87Vvm;A1Vx;Vn;A3S93S87S49Vgk;A1A1Vx;Vn;A3F_;F_;F_;").
  Proof using HI HV Ha_ceil Ha_lo Hinit.
    intros Hn Hd Hr. pose proof a_facts as (A1 & A2 & A3 & A4).
    destruct gk; cbn [vmI vm_maps]; [apply range_in_maps_cons; exact Hr | apply range_in_maps_cons; exact Hr |].
    apply maps_subtract_keeps; [exact Hn | lia | unfold PGSZ in *; lia | unfold PGSZ in *; lia | apply range_in_maps_cons; exact Hr].
  Qed.
  Lemma old_noaccess_kept gk x n : ltac2:(tb__ "0|0|
S3dZ0Vn;A2S2S3bS3cVx;Vn;A2S44A2S3bS3cS44S3eZ2S8A2A2Vx;A2A2S93S88Vvm;A1Vx;Vn;A3S93S88S49Vgk;A1A1Vx;Vn;A3F_;F_;F_;").
  Proof using HI HV Ha_ceil Ha_lo Hinit.
    intros Hn Hd Hr. pose proof a_facts as (A1 & A2 & A3 & A4).
    destruct gk; cbn [vmI vm_noaccess]; [exact Hr | |].
    - apply range_in_maps_cons. apply maps_subtract_keeps; [exact Hn | lia | unfold PGSZ in *; lia | unfold PGSZ in *; lia | exact Hr].
    - apply maps_subtract_keeps; [exact Hn | lia | unfold PGSZ in *; lia | unfold PGSZ in *; lia | exact Hr].
  Qed.

  Lemma new_maps_cases gk e : ltac2:(tb__ "0|6|
S4fS55S85Q40M0A1M1G1A2M2Ve;S87S49Vgk;A1A1A3S2S4G2G2S1S4fG2R1S87Vvm;A1A3S1S3bS84G0S59G1G1R1A3A2M3S84G0S59G1G1Ve;A3A2M4A2S3bS3cG4S84G0S5aG1G1Ve;A3A2A2M5S3cG3S84G0S5aG1G1R1A3A2A2A2A2A2Le0;A2S1S3bS44G4A2S3bG5S3cS44S3eZ2S8A2A2A2A2A2F_;").
  Proof using HI HV Ha_ceil Ha_lo Hinit.
    pose proof a_facts as (A1 & A2 & A3 & A4). intros Hin. destruct gk; cbn [vmI vm_maps] in Hin.
    - destruct Hin as [<-|Hin]; [right; cbn [fst snd]; rewrite ua, u2; lia | left; exists e; split; [exact Hin | lia]].
    - destruct Hin as [<-|Hin]; [right; cbn [fst snd]; rewrite ua, u2; lia | left; exists e; split; [exact Hin | lia]].
    - destruct (maps_subtract_piece _ a (a + PGSZ) e ltac:(lia) ltac:(unfold PGSZ; lia) ltac:(unfold PGSZ in *; lia) Hin) as (e0 & He0 & S1 & S2 & _).
      destruct He0 as [<-|He0]; [right; cbn [fst snd] in S1, S2; rewrite ua in S1; rewrite ua, u2 in S2; lia | left; exists e0; split; [exact He0 | lia]].
  Qed.
  Lemma new_noaccess_cases gk e : ltac2:(tb__ "0|6|
S4fS55S85Q40M0A1M1G1A2M2Ve;S88S49Vgk;A1A1A3S2S4G2G2S1S4fG2R1S88Vvm;A1A3S1S3bS84G0S59G1G1R1A3A2M3S84G0S59G1G1Ve;A3A2M4A2S3bS3cG4S84G0S5aG1G1Ve;A3A2A2M5S3cG3S84G0S5aG1G1R1A3A2A2A2A2A2Le0;A2S1S3bS44G4A2S3bG5S3cS44S3eZ2S8A2A2A2A2A2F_;").
  Proof using HI HV Ha_ceil Ha_lo Hinit.
    pose proof a_facts as (A1 & A2 & A3 & A4). intros Hin. destruct gk; cbn [vmI vm_noaccess] in Hin.
    - left. exists e. split; [exact Hin | lia].
    - destruct Hin as [<-|Hin]; [right; cbn [fst snd]; rewrite ua, u1; unfold PGSZ; lia |].
      destruct (maps_subtract_piece _ a (a + PGSZ) e ltac:(lia) ltac:(unfold PGSZ; lia) ltac:(unfold PGSZ in *; lia) Hin) as (e0 & He0 & S1 & S2 & _).
      left. exists e0. split; [exact He0 | lia].
    - destruct (maps_subtract_piece _ a (a + PGSZ) e ltac:(lia) ltac:(unfold PGSZ; lia) ltac:(unfold PGSZ in *; lia) Hin) as (e0 & He0 & S1 & S2 & _).
      left. exists e0. split; [exact He0 | lia].
  Qed.

  Theorem vm_ok_tI gk : ltac2:(tb__ "0|0|
S96S45S43S49Vgk;A1A3").
  Proof using HI HL HV HX Ha_ceil Ha_lo Hfree Hinit.
    pose proof HV as (V1 & V2 & V3 & V5 & X1 & X2 & X3 & X4 & V9 & V10 & V11). pose proof a_facts as (A1 & A2 & A3 & A4).
    pose proof brk0_facts as (B1 & B2 & B3). pose proof tI_fields as (F1 & F2 & F3 & F4 & _).
    assert (RS : vm_reserved (vmI gk) = vm_reserved vm /\ vm_start_brk (vmI gk) = vm_start_brk vm /\ vm_brk (vmI gk) = wz (a + 2 * PGSZ)) by (destruct gk; repeat split; reflexivity).
    destruct RS as (RS1 & RS2 & RS3).
    unfold vm_ok. rewrite F4, RS2, RS3.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|   rewrite L'_top; destruct gk; exact V11]]]]]]]]]].
    - intros r rg Hr Hl Hk. rewrite region_of_tI in Hr. destruct (Nat.eqb r rr) eqn:E; [injection Hr as <-; discriminate|].
      rewrite (OLDREG r rg Hr). exact (old_entry_kept gk r rg Hr Hl (or_introl Hk) (V1 r rg Hr Hl Hk)).
    - intros r rg Hr Hk. rewrite region_of_tI in Hr. destruct (Nat.eqb r rr) eqn:E; [injection Hr as <-; discriminate|].
      rewrite (OLDREG r rg Hr). destruct (V2 r rg Hr Hk) as (W1 & W2 & W3). pose proof (region_live_t r rg Hr Hk) as Hl.
      pose proof (X3 r rg Hr Hl) as SZ. destruct (X4 r rg Hr Hl) as [Q1 Q2].
      split; [exact (old_entry_kept gk r rg Hr Hl (or_intror Hk) W1)|]. split.
      + intros k Hk1 Hk2 Hk3. apply old_noaccess_kept; [unfold PGSZ; lia | | exact (W2 k Hk1 Hk2 Hk3)].
        destruct (Z_le_dec (ly_reg L r + PGSZ * k + PGSZ) a) as [Y|N1]; [left; exact Y|].
        destruct (Z_le_dec (a + 2 * PGSZ) (ly_reg L r + PGSZ * k)) as [Y|N2]; [right; exact Y|]. exfalso.
        destruct (Z_le_dec a (ly_reg L r + PGSZ * k)).
        * apply (old_region_vs_grant r rg (ly_reg L r + PGSZ * k) Hr Hl (or_intror Hk)); clear - Hk1 Hk2 N1 N2 l; unfold PGSZ in *; lia.
        * apply (old_region_vs_grant r rg a Hr Hl (or_intror Hk)); clear - Hk1 Hk2 N1 N2 n A1; unfold PGSZ in *; lia.
      + intros off Hoff e He. destruct (X1 r rg off Hr Hk Hoff) as [O1 O2].
        destruct (new_noaccess_cases gk e He) as [(e0 & He0 & S1 & S2)|[S1 S2]].
        * pose proof (W3 off Hoff e0 He0) as Z0. clear - Z0 S1 S2. lia.
        * destruct (Z_le_dec (ly_reg L r + off + PGSZ) (bv_unsigned (fst e))) as [Y|N1]; [left; exact Y|].
          destruct (Z_le_dec (bv_unsigned (fst e) + bv_unsigned (snd e)) (ly_reg L r + off)) as [Y|N2]; [right; exact Y|]. exfalso.
          pose proof (urange (snd e)) as US.
          destruct (Z_le_dec a (ly_reg L r + off)).
          -- apply (old_region_vs_grant r rg (ly_reg L r + off) Hr Hl (or_intror Hk)); clear - O1 O2 S1 S2 N1 N2 l US; unfold PGSZ in *; lia.
          -- apply (old_region_vs_grant r rg a Hr Hl (or_intror Hk)); clear - O1 O2 S1 S2 N1 N2 n US A1; unfold PGSZ in *; lia.
    - split; [rewrite L'_reg_new; reflexivity|]. split; [rewrite ubrk, L'_brk0; lia|]. split; [rewrite B2, L'_brk0; reflexivity|].
      intros k Hk. replace k with 1 by lia. rewrite L'_brk0. replace (a + PGSZ * 1) with (a + PGSZ) by lia. exact (page_in_maps gk).
    - intros p n Hin. apply fp_tI in Hin as [Hin|E].
      + rewrite (L'_addr_of p) by exact (footprint_below X R U t HI _ Hin).
        pose proof (V5 p n Hin) as RG. pose proof (fp_size _ Hin) as SZ. cbn [snd] in SZ.
        apply old_range_kept; [exact SZ | | exact RG].
        destruct RG as (e0 & He0 & Q1 & Q2).
        pose proof (grant_vs_maps e0 (addr_of L p) He0) as G1. pose proof (grant_vs_maps e0 a He0) as G2.
        clear - Q1 Q2 G1 G2 SZ A1. unfold PGSZ in *. lia.
      + injection E as -> ->. unfold addr_of. rewrite L'_pnew. exact (page_in_maps gk).
    -   intros k rg off Hk' Hkd Hoff. rewrite region_of_tI in Hk'. destruct (Nat.eqb k rr) eqn:E; [injection Hk' as <-; cbn in Hkd; discriminate | exact (X1 k rg off Hk' Hkd Hoff)].
    -   intros r1 r2 q1 q2 Hne H1 H2 K1 K2. rewrite region_of_tI in H1, H2.
      destruct (Nat.eqb r1 rr); [injection H1 as <-; cbn in K1; discriminate|]. destruct (Nat.eqb r2 rr); [injection H2 as <-; cbn in K2; discriminate|].
      rewrite (OLDREG r1 q1 H1), (OLDREG r2 q2 H2). exact (X2 r1 r2 q1 q2 Hne H1 H2 K1 K2).
    -   intros k rg Hk' Hl'. rewrite region_of_tI in Hk'. destruct (Nat.eqb k rr) eqn:E; [injection Hk' as <-; cbn [rgI rg_len]; unfold PGSZ; lia | exact (X3 k rg Hk' Hl')].
    -   intros k rg Hk' Hl'. rewrite region_of_tI in Hk'. destruct (Nat.eqb k rr) eqn:E.
      + apply Nat.eqb_eq in E. subst k. injection Hk' as <-. cbn [rgI rg_len]. rewrite L'_reg_new, L'_top. lia.
      + rewrite (OLDREG k rg Hk'), L'_top. exact (X4 k rg Hk' Hl').
    -   intros k rg q n Hk' Hkd Hl' Hin Hne. apply fp_tI in Hin as [Hin|E].
      + pose proof (L'_fp (LMem q, n) Hin) as EQ. cbn [fst] in EQ. rewrite EQ.
        rewrite region_of_tI in Hk'. destruct (Nat.eqb k rr) eqn:Ek; [injection Hk' as <-; cbn in Hkd; discriminate|].
        rewrite (OLDREG k rg Hk'). exact (V9 k rg q n Hk' Hkd Hl' Hin Hne).
      + injection E as -> ->. rewrite region_of_tI in Hk'. cbn [prid pnew] in Hne. unfold pnew in Hne. cbn [prid] in Hne.
        destruct (Nat.eqb k rr) eqn:Ek; [apply Nat.eqb_eq in Ek; exfalso; exact (Hne (eq_sym Ek))|].
        rewrite L'_pnew, (OLDREG k rg Hk').
        pose proof (region_live_t k rg Hk' Hkd) as Hlv. pose proof (X3 k rg Hk' Hlv) as SZr.
        destruct (Z_le_dec (a + PGSZ + PGSZ) (ly_reg L k)) as [Y|N1]; [left; exact Y|].
        destruct (Z_le_dec (ly_reg L k + rg_len rg) (a + PGSZ)) as [Y|N2]; [right; exact Y|]. exfalso.
        destruct (Z_le_dec a (ly_reg L k)).
        * apply (old_region_vs_grant k rg (ly_reg L k) Hk' Hlv (or_intror Hkd)); unfold PGSZ in *; lia.
        * apply (old_region_vs_grant k rg a Hk' Hlv (or_intror Hkd)); unfold PGSZ in *; lia.
    -
      intros rb p k rgk Hb Hk' Hkd Hl'. injection Hb as <- <-. rewrite region_of_tI in Hk'.
      destruct (Nat.eqb k rr) eqn:Ek; [injection Hk' as <-; cbn in Hkd; discriminate|].
      rewrite L'_reg_new, (OLDREG k rgk Hk').
      pose proof (X3 k rgk Hk' Hl') as SZr.
      destruct (Z_le_dec (ly_reg L k + rg_len rgk) (a + PGSZ)) as [Y|N1]; [left; exact Y|].
      destruct (Z_le_dec (a + PGSZ * 2) (ly_reg L k)) as [Y|N2]; [right; exact Y|]. exfalso.
      destruct (Z_le_dec a (ly_reg L k)).
      + apply (old_region_vs_grant k rgk (ly_reg L k) Hk' Hl' (or_introl Hkd)); unfold PGSZ in *; lia.
      + apply (old_region_vs_grant k rgk a Hk' Hl' (or_introl Hkd)); unfold PGSZ in *; lia.
  Qed.

  Lemma maps_wf_tI gk : maps_wf (vmI gk).
  Proof using HI HMW HV Ha_ceil Ha_lo Hfree Hinit.
    pose proof a_facts as (A1 & A2 & A3 & A4).
    assert (W : mwf ((wa, w2) :: vm_maps vm)).
    { apply mwf_cons; [exact HMW | cbn [snd]; rewrite u2; unfold PGSZ; lia |].
      intros e' He'. unfold wdisj. cbn [fst snd]. rewrite ua, u2.
      destruct (Hfree e' ltac:(apply in_app_iff; right; exact He')) as [H|H]; [right; exact H | left; exact H]. }
    unfold maps_wf. destruct gk; cbn [vmI vm_maps]; [exact W | exact W |].
    apply mwf_subtract; [unfold PGSZ; lia | unfold PGSZ in *; lia | exact W].
  Qed.

  Theorem ledger_tI gk : ltac2:(tb__ "0|2|
S1S9cVC;S49Vgk;A1M0A2S1S9bVC;G0A2S0S56S55S85Q40A1M1G1A2A1S89G0A1S89Vvm;A1A3A2A2").
  Proof using HI HIR HLG HMW HSI HV Ha_ceil Ha_lo Hfree Hinit.
    pose proof a_facts as (A1 & A2 & A3 & A4).
    assert (RS1 : vm_reserved (vmI gk) = vm_reserved vm) by (destruct gk; reflexivity).
    split; [|split; [unfold img_reserved; rewrite RS1; exact HIR | exact RS1]].
    assert (TOPI : alloc_top (vmI gk) = topL L) by (rewrite (vm_ok_top L t vm HV); destruct gk; reflexivity). unfold ledger_ok. rewrite TOPI.
    intros e He. pose proof (mwf_In_pos _ e (maps_wf_tI gk) He) as POS.
    destruct (new_maps_cases gk e He) as [(e0 & He0 & S1 & S2)|[S1 S2]].
    - destruct (HLG e0 He0) as (G1 & G2 & G3). rewrite <- (vm_ok_top L t vm HV) in G2. pose proof (urange (snd e)). lia.
    - split; [lia|]. split; [lia|].
      pose proof (urange (snd e)) as US.
      destruct (Z_le_dec (bv_unsigned (fst e) + bv_unsigned (snd e)) (mc_img_lo C)); [left; lia|]. destruct (Z_le_dec (mc_img_hi C) (bv_unsigned (fst e))); [right; lia|]. exfalso.
      pose proof HSI as (_&_&_&_&_&_&_&_&_& [CX1 CX2] &_).
      destruct (Z_le_dec (bv_unsigned (fst e)) (mc_img_lo C)).
      + apply (grant_vs_image (mc_img_lo C)); unfold CTX_SIZE, PGSZ in *; lia.
      + apply (grant_vs_image (bv_unsigned (fst e))); unfold PGSZ in *; lia.
  Qed.

  Lemma xraw_tI : ltac2:(tb__ "0|0|
SabS5bS7S47VX;A3S43A2").
  Proof using HI HX.
    intros q [<-|Hq].
    - left. rewrite tI_upd. apply MT_upd_same.
    - rewrite tI_upd. rewrite MT_upd_other.
      + unfold MT. rewrite (proj1 tIpre_fields). exact (HX q Hq).
      + intros ->. pose proof (key_below X R U t HI mnew (proj1 (inv_X HI mnew Hq))) as K. rewrite mnew_prid in K. unfold rr in K. lia.
  Qed.
  Lemma mnew_notX : ltac2:(tb__ "0|3|
S1S0S5fS83S47VX;A2S63A3S1S4fS7S47S6dS43A1A3S2S0S57SaA1M0S73S43S47A2M1S5dSaS1fA2A3S0G0G1S5dSaS2eS60S7A1M2G2A2A2A3A2A2A2").
  Proof using HI Hinit. pose proof (SPECI 0 0) as (_ & M & K & R2 & _). cbn [fst snd] in *. auto. Qed.
  Lemma keys_tI : ltac2:(tb__ "0|0|
S50S7S6dVt;A1S6dS43A1A3").
  Proof using HI Hinit. pose proof (SPECI 0 0) as (_ & _ & _ & _ & _ & _ & (ext & E & _)). cbn [fst snd] in E. intros q Hq. rewrite E. apply in_app_iff. left. exact Hq. Qed.
  Lemma am_frame_tI : ltac2:(tb__ "0|0|
S1Sa9Vt;S43A2S1S7S31S5S7cS5bS7S47VX;A3S43R2R1A4S7cVX;Vt;R2R1A4A2Fgm;Fg;Sa7Vt;S43A2A2A2").
  Proof using HI Hinit. pose proof (SPECI 0 0) as (_ & _ & _ & _ & F & U1 & UB). cbn [fst snd] in *. auto. Qed.
  Lemma bounded_tI (gk : guard_kind) : bounded tI.
  Proof using HB HI HIR HL HLG HMW HSI HV HX Ha_ceil Ha_lo Hctx Hfree Hinit.
    pose proof HB as (B1 & B2 & B3 & _).
    pose proof tI_fields as (F1 & F2 & _ & _ & _ & _ & _ & _ & _ & F10 & _ & _ & F13 & _ & F15 & _).
    split; [intros sc; unfold usage_of; rewrite F15; apply B1|]. split; [rewrite F10; exact B2|].
    split; [exact (areas_bound (mnew :: X) R U tI L' C (vmI gk) HII layout_ok_tI (vm_ok_tI gk) (proj1 (ledger_tI gk)))|].
    right. rewrite F13, F1. cbn [prid padd pnew]. unfold pnew. cbn [prid]. rewrite length_app. cbn. unfold rr. lia.
  Qed.
  Lemma cell_whereI c x : ltac2:(tb__ "0|4|
S4fS65Vc;S58S65S69S43A1S86S43A1A3A3S1S3bS67S45S6fVc;A1A2M0Vx;A2S3dVx;S3cG0S40S82Vc;A1A1A2A2A2S2S4S55S64S6A2M1G1S1S4fG1R1S66Vt;A1A3S1S3bS67VL;S59S64S6R1A3A2M2Vx;A2S3dVx;S3cG2S5aS64S6R1A3A2A2A2A2Le;A2S1S3bS3cS44S8A2M3Vx;A2S3dVx;S3cG3S8A2A2A2A2F_;F_;").
  Proof using HI HL HX Hinit.
    intros Hc Hx. destruct (cell_in_footprintI (mnew :: X) R U tI L' HII xraw_tI c Hc) as (e & He & [I1 I2]).
    unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2. apply fp_tI in He as [He| ->].
    - left. exists e. split; [exact He|]. rewrite (L'_fp e He) in I1, I2. lia.
    - right. cbn [fst snd] in I1, I2. rewrite L'_pnew in I1, I2. lia.
  Qed.
  Lemma fp_where e x : ltac2:(tb__ "0|3|
S4fS55S64S6A2Ve;S66Vt;A1A3S1S3bS67VL;S59S64S6Ve;A3M0A2M1Vx;A2S3dVx;S3cG1S5aS64S6Ve;A3A2A2A2S2S1S0S64G0S68Z0A1A3S1S3bS74VL;A1M2Vx;A2S3dVx;S3cG2S76A2A2A2A2S4S7S7S1S0S64G0S6bR1A1A3S1S1S3bS8Vx;A2S3dVx;S95VL;A1A2A2S3S1S3bS9aVC;A1Vx;A2S3dVx;S99VC;A1A2A2A1A2A2Lp;A2A2F_;F_;").
  Proof using HI HLG HV Hinit.
    intros He Hx. pose proof HV as (_ & _ & _ & V5 & _). destruct e as [[o|p] n]; cbn [fst snd] in *.
    - left. rewrite fp_t in He. destruct He as [E|He].
      + injection E as <- <-. cbn [loc_addr] in Hx. split; [reflexivity | lia].
      + exfalso. apply in_flat_map in He as (k & _ & He). destruct (region_of t k) as [rg|]; [|destruct He]. destruct (rg_kind rg); try destruct He.
        destruct (rg_live rg); [destruct He as [E|[]]; discriminate | destruct He].
    - right. exists p. split; [reflexivity|]. destruct (V5 p n He) as (e' & He' & R1 & R2). destruct (HLG e' He') as (G1 & G2 & G3). rewrite <- (vm_ok_top _ _ _ HV) in G2.
      unfold addr_of in R1, R2. cbn [loc_addr] in Hx. destruct p as [r o]. cbn [loc_addr] in *. lia.
  Qed.
  Lemma block_where b n x : ltac2:(tb__ "0|3|
S4fS55S6S6A2S5eS6S6Vb;Vn;A4S94VL;Vt;A2A3S1S3bVb;Vx;A2S3dVx;S3cVb;Vn;A2A2A2S4S55S64S6A2M0G0S4S7S7S1S4fG0R2S66Vt;A1A3S1S0S64S59S64S6R2A3M1S6bR1A1A3S1S3bS67VL;G1A2M2Vx;A2S3dVx;S3cG2S5aS64S6R2A3A2A2A2A2A2Lp;A2Le;A2F_;F_;").
  Proof using HI HX. exact (AllocMetaArea.block_where X R U t L HI HX b n x). Qed.
  Lemma grant_vs_block b n x : ltac2:(tb__ "0|0|
S4fS55S6S6A2S5eS6S6Vb;Vn;A4S94VL;Vt;A2A3S1S3bVb;Vx;A2S3dVx;S3cVb;Vn;A2A2A2S3S1S3bS44Vx;A2S3dVx;S3cS44S3eZ2S8A2A2A2A2A1F_;F_;").
  Proof using HI HIR HSI HV HX Hctx Hfree Hinit. intros Hin Hx. destruct (block_where b n x Hin Hx) as (e & p & He & _ & Rx). exact (grant_vs_footprint e x He Rx). Qed.
End INIT.
