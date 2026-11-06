(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "option"; "bool"; "list"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_s"; "ma_owned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "Inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "C_U"; "mc_img_hi"; "mc_img_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsP"; "segsU"; "@Corelib.Init.Logic"; "not"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "client_addr"; "mem_kept"; "mem_kept_owned"; "wseg_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws"; "wseg_in_image_P"; "wseg_in_image_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI"; "client_addr_not_ownedG"; "mem_kept_of_ownedG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws"; "statics_in_image_P"; "statics_in_image_U"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocWfSurgery MallocWfGeom MallocWfRepr MallocLayout MallocFooter MallocIface MallocIfaceI MallocLaws
  Contract ClientLaws FpLaws Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Close Scope bv_scope.

Section CI.
  Variables (segs : list Segment) (C : mconsts).
  Hypothesis HS : statics_in_image C.
  Hypothesis HWS : ltac2:(tb__ "0|2|
S1Q40M0A1S18S4S1cVsegs;R1A2S7A3S17S23S12VC;A1S2G0R2A2M1A2S24G1S11VC;A1A2A2F_;Fa;").

  Theorem client_addr_not_ownedG : ltac2:(tb__ "0|1|
S5S8A1S3S6S8S0A2A1S0S0F_;SaS1Q40A1M0S3S1Q8A1A1F_;G0S4F_;S9S0SdVC;SeR8R7R6A3R5R4R3R2A6S13R9SbR6A1A2S19Vsegs;VC;R7R3A4S16ScVC;R8R4A3A1F_;F_;F_;Fa;Fvm;Fwok;Frd;FA;FU;FR;FX;").
  Proof using HS HWS.
    intros X R U [s L] rd wok vm a HM HXr Hca. cbn [ma_s] in HXr.
    pose proof (mig_I HM) as HI. pose proof (mig_layout HM) as HL. pose proof (mig_vm HM) as HV.
    pose proof (mig_ledger HM) as HLG. pose proof (mig_ctx HM) as HC. cbn [ma_s ma_L] in *.
    pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta delta [CTX_SIZE PGSZ UNIT] in HS0.
    destruct HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & Ilock & Ictx & Ierr & Hpg & Hceil).

    assert (OWN : forall x, alloc_owned L s x ->
              (mc_ctx C <= x < mc_ctx C + CTX_SIZE)
              \/ (PGSZ <= x /\ x < topL L /\ ~ (mc_img_lo C <= x < mc_img_hi C))).
    { intros x [([l n] & Hrg & Hx) _]. cbn [fst snd] in Hx.
      destruct (footprint_entry_cases s l n Hrg) as [[-> ->] | [p ->]].
      - left. unfold loc_addr in Hx. rewrite HC in Hx. lia.
      - right. pose proof (fp_mem_range C L s vm p n HV HLG Hrg ltac:(lia)) as (G1 & G2 & G3).
        unfold addr_of in G1, G2, G3. lia. }

    assert (BLK : forall b n x, In (b, n) (ma_blocks (mkMA s L)) -> b <= x < b + n ->
              PGSZ <= x /\ x < topL L /\ ~ (mc_img_lo C <= x < mc_img_hi C)).
    { intros b n x Hin Hx. unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin.
      apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
      destruct (user_block_in_group X R U s L HI HXr (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
      cbn [fst snd] in B1, B2, B3.
      destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
      pose proof (footprint_region_In s _ _ Hr Hkd Hl) as ER.
      pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as ((Glast & _) & _).
      assert (Hsi : 0 <= stride_of am * i) by nia. assert (Hsl : stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia.
      unfold group_extent in Hext, B4.
      pose proof (fp_mem_range C L s vm (SP (prid (am_mem am)) 0) (rg_len rg) HV HLG ER ltac:(unfold UNIT, IB in *; lia)) as (G1 & G2 & G3).
      unfold addr_of, loc_addr in *. destruct (am_mem am) as [r o]. cbn [prid poff padd] in *.
      unfold IB, UNIT in *. lia. }
    pose proof (topL_range L) as TR.
    intros [Ho | Hl].
    -
      destruct Hca as [H | [(b & n & Hin & Hr) | (Hw & Hnctx & Hnlock & Hnerr)]].
      + cbn [ma_L] in H. destruct (OWN a Ho) as [X0|X0]; unfold CTX_SIZE, PGSZ, UNIT in *; lia.
      + destruct Ho as [_ Hnu]. apply Hnu.
        unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin.
        apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
        exists (p, n). split; [exact Hin|]. cbn [fst snd]. unfold addr_of in Hr. exact Hr.
      + pose proof (HWS _ Hw) as R0.
        destruct (OWN a Ho) as [X0|X0].
        * exact (Hnctx X0).
        * assert (Ha : 0 <= a < 2 ^ 64).
          { unfold PGSZ in X0. lia. }
          rewrite Z_to_bv_unsigned, (bv_wrap_small 64 a) in R0 by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
    -
      destruct Hca as [H | [(b & n & Hin & Hr) | (Hw & Hnctx & Hnlock & Hnerr)]].
      + cbn [ma_L] in H. unfold UNIT in *. lia.
      + pose proof (BLK b n a Hin Hr) as (_ & _ & NI). apply NI. lia.
      + exact (Hnlock Hl).
  Qed.

  Theorem mem_kept_of_ownedG : ltac2:(tb__ "0|6|
S5S8A1M0S3S6S8S0A2A1M1S0S0F_;M2G0G1G2SaSaS1Q40A1M3S3S1Q8A1A1F_;M4G3S4F_;M5S9G4G5S9G4G4SdVC;SeR10RfReA3RaR8R7R6A6S13R11SbRbA1A2SdVC;SeRfReRdA3RbR7R6R5A6S13R10SbRcA1A2S1bVC;ReRdR6R5A5S1aVsegs;VC;RfReR7R6A6F_;F_;F_;F_;F_;Fm1;Fm0;Fvm';Fwok';Frd';Fvm;Fwok;Frd;FA';FA;FU';FR';FX';FU;FR;FX;").
  Proof using HS HWS.
    intros X R U X' R' U' A A' rd wok vm rd' wok' vm' m0 m1 HM HX HM' HX' Hk a Ha Hc Hc' He Hst.
    exact (Hk a Ha (client_addr_not_ownedG X R U A rd wok vm a HM HX Hc) (client_addr_not_ownedG X' R' U' A' rd' wok' vm' a HM' HX' Hc') He Hst).
  Qed.
End CI.

Definition client_addr_not_ownedG_P : ltac2:(tb__ "0|1|
S5S8A1S3S6S8S0A2A1S0S0F_;SaS1Q40A1M0S3S1Q8A1A1F_;G0S4F_;S9S0SdSfSeR8R7R6A3R5R4R3R2A6S13R9SbR6A1A2S19S14SfR7R3A4S16ScSfR8R4A3A1F_;F_;F_;Fa;Fvm;Fwok;Frd;FA;FU;FR;FX;") := ltac2:(tb__ "0|0|
S1fS14SfS21S1dA4").
Definition client_addr_not_ownedG_U : ltac2:(tb__ "0|1|
S5S8A1S3S6S8S0A2A1S0S0F_;SaS1Q40A1M0S3S1Q8A1A1F_;G0S4F_;S9S0SdS10SeR8R7R6A3R5R4R3R2A6S13R9SbR6A1A2S19S15S10R7R3A4S16ScS10R8R4A3A1F_;F_;F_;Fa;Fvm;Fwok;Frd;FA;FU;FR;FX;") := ltac2:(tb__ "0|0|
S1fS15S10S22S1eA4").
Definition mem_kept_of_ownedG_P := mem_kept_of_ownedG segsP C_P statics_in_image_P wseg_in_image_P.
Definition mem_kept_of_ownedG_U := mem_kept_of_ownedG segsU C_U statics_in_image_U wseg_in_image_U.
