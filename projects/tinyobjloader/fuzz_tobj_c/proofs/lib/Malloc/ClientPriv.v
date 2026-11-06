(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@Corelib.Init.Logic"; "and"; "not"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "META_SIZE"; "PGSZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "option"; "prod"; "bool"; "list"; "app"; "fst"; "snd"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "C_U"; "mc_img_hi"; "mc_img_lo"; "addr_of"; "mc_ctx"; "topL"; "blocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "client_addr"; "wseg_addr"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "Inv"; "layout"; "CTX_SIZE"; "keys"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "vm_maps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsP"; "segsU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws"; "wseg_in_image_P"; "wseg_in_image_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv"; "client_not_ctx"; "client_not_fresh"; "client_not_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws"; "statics_in_image_P"; "statics_in_image_U"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocWfSurgery MallocWfGeom MallocWfRepr MallocLayout MallocFooter MallocIface MallocIfaceI MallocLaws
  Contract ClientLaws ClientLawsI FpLaws Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Close Scope bv_scope.

Section CP.
  Variables (segs : list Segment) (C : mconsts).
  Hypothesis HS : statics_in_image C.
  Hypothesis HWS : ltac2:(tb__ "0|2|
ScQ40M0A1S6S10S20Vsegs;R1A2S16A3S4S1S1aVC;A1SdG0R2A2M1A2S2G1S19VC;A1A2A2F_;Fa;").
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
  Variables (rd : word -> option byte) (wok : word -> bool) (vm : VmMaps).
  Hypothesis HM : ltac2:(tb__ "0|0|
S22VC;S23VX;VR;VU;A3SbVs;VL;A2Vrd;Vwok;Vvm;A6").
  Hypothesis HX : xraw X s.

  Let HI : Inv X R U s := mig_I HM.
  Let HL : layout_ok L s := mig_layout HM.
  Let HV : vm_ok L s vm := mig_vm HM.
  Let HLG : ledger_ok C vm := mig_ledger HM.
  Let HC : ly_ctx L = mc_ctx C := mig_ctx HM.

  Lemma block_byte_where b n x : ltac2:(tb__ "0|2|
S21SfS0S0A2S15S0S0Vb;Vn;A4S1eVL;Vs;A2A3S4S1Vb;Vx;A2S2Vx;S3Vb;Vn;A2A2A2S4S4S1SaVx;A2S2Vx;S1dVL;A1A2A2S4S5S4S1S1aVC;A1Vx;A2S2Vx;S19VC;A1A2A2A1S4S5S4S1S1cVC;A1M0Vx;A2S2Vx;S3G0S25A2A2A2A1S7S21S7R1S26Vs;A1A3S5S4S1S1bVL;R2A2M1Vx;A2S2Vx;S3G1S9A2A2A2A1F_;Fq;A2A2A2F_;F_;").
  Proof using HC HI HL HLG HV HX.
    intros Hin Hx. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U s L HI HX (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    cbn [fst snd] in B1, B2, B3.
    pose proof (group_range X R U s L HI HL C vm g am Hu HV HLG) as (G1 & G2 & G3 & G4).
    pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
    assert (Hsi : 0 <= stride_of am * i) by nia.
    unfold UNIT, IB in *.
    assert (D : 16 <= x - addr_of L (am_mem am) < group_extent am) by lia.
    split; [lia|]. split; [lia|]. split; [rewrite <- HC; lia|].
    intros q Hq. pose proof (meta_vs_group X R U s L HI HL q g am (x - addr_of L (am_mem am)) Hq Hu ltac:(unfold IB; lia)) as M. lia.
  Qed.

  Theorem client_not_ctx a : ltac2:(tb__ "0|1|
S1fVsegs;VC;SbVs;VL;A2Va;A4S5S4S1S1cVC;A1M0Va;A2S2Va;S3G0S25A2A2A2A1F_;").
  Proof using HC HI HL HLG HS HV HX.
    pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta in HS0.
    destruct HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ictx & _ & _ & Hceil).
    intros [Ha | [(b & n & Hin & Hr) | (Hw & Hnctx & _)]] Hc.
    - cbn [ma_L] in Ha. pose proof (topL_range L). unfold UNIT in Hceil. lia.
    - exact (proj1 (proj2 (proj2 (block_byte_where b n a Hin Hr))) Hc).
    - exact (Hnctx Hc).
  Qed.

  Theorem client_not_meta a q : ltac2:(tb__ "0|1|
S1fVsegs;VC;SbVs;VL;A2Va;A4S21S7Vq;S26Vs;A1A3S5S4S1S1bVL;Vq;A2M0Va;A2S2Va;S3G0S9A2A2A2A1F_;F_;").
  Proof using HC HI HL HLG HS HV HWS HX.
    pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta in HS0.
    destruct HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hceil).
    intros [Ha | [(b & n & Hin & Hr) | (Hw & Hnctx & _)]] Hq Hc.
    - cbn [ma_L] in Ha. pose proof (key_range X R U s L HI HL C vm q Hq HV HLG) as (K1 & K2 & _). lia.
    - exact (proj2 (proj2 (proj2 (block_byte_where b n a Hin Hr))) q Hq Hc).
    - pose proof (key_range X R U s L HI HL C vm q Hq HV HLG) as (K1 & K2 & K3 & _).
      assert (Ha : 0 <= a < 2 ^ 64) by (top_ranges; unfold META_SIZE, PGSZ in *; lia).
      pose proof (HWS _ Hw) as R0. rewrite Z_to_bv_unsigned, (bv_wrap_small 64 a) in R0 by (change (bv_modulus 64) with (2 ^ 64); lia).
      unfold META_SIZE in *. lia.
  Qed.

  Theorem client_not_fresh a za len : ltac2:(tb__ "0|6|
SfScQ40M0A1M1G1A2M2S21G2R1S12G2S29Vvm;A1S28Vvm;A1A3A3S0S4S1SdG0S13G1G1R3A3A2M3R1A2S2R1S3G3SdG0S14G1G1R3A3A2A2A2A2S5S4S1Vza;R2A2S2R2S3Vza;Vlen;A2M4A2A2A1M5F_;Fy;F_;Fe;S1Z0Vza;A2S1G4S1dVL;A1A2S0S4S1S1aVC;A1R1A2S2R1S19VC;A1A2A2G5F_;Fy;S1fVsegs;VC;SbVs;VL;A2Va;A4S5S4S1Vza;Va;A2S2Va;G4A2A2A1F_;F_;F_;F_;F_;").
  Proof using HI HV HWS HX.
    intros Hfree Hza Hceil Himg [Ha | [(b & n & Hin & Hr) | (Hw & Hnctx & _)]] Hc.
    - cbn [ma_L] in Ha. lia.
    - unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
      destruct (user_block_in_group X R U s L HI HX (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
      cbn [fst snd] in B1, B2, B3.
      destruct (used_group_region X R U s g am HI Hu) as (rg & Hrg & Hkd & Hl & Ho & Hext & _).
      pose proof (footprint_region_In s _ _ Hrg Hkd Hl) as ER.
      pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
      assert (Hsi : 0 <= stride_of am * i) by nia.
      destruct (proj1 (proj2 (proj2 (proj2 HV))) (SP (prid (am_mem am)) 0) (rg_len rg) ER) as (e & He & E1 & E2). cbn [ma_L] in E1, E2.
      apply (Hfree e ltac:(apply in_app_iff; right; exact He) a); [|exact Hc].
      unfold group_extent in Hext, B4. unfold addr_of, loc_addr in *. destruct (am_mem am) as [r o]. cbn [prid poff padd fst snd] in *.
      unfold UNIT, IB in *. lia.
    - pose proof (HWS _ Hw) as R0.
      assert (Ha : 0 <= a < 2 ^ 64) by (top_ranges; lia).
      rewrite Z_to_bv_unsigned, (bv_wrap_small 64 a) in R0 by (change (bv_modulus 64) with (2 ^ 64); lia).
      exact (Himg a R0 Hc).
  Qed.
End CP.

Definition client_not_ctx_P := client_not_ctx segsP C_P statics_in_image_P.
Definition client_not_meta_P := client_not_meta segsP C_P statics_in_image_P wseg_in_image_P.
Definition client_not_fresh_P := client_not_fresh segsP C_P wseg_in_image_P.
Definition client_not_ctx_U := client_not_ctx segsU C_U statics_in_image_U.
Definition client_not_meta_U := client_not_meta segsU C_U statics_in_image_U wseg_in_image_U.
Definition client_not_fresh_U := client_not_fresh segsU C_U wseg_in_image_U.
