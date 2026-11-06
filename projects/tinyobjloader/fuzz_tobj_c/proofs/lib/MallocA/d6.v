(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_073.   (* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cb F0A_drain ax dy.

(* [comment removed for export] *)
Module F0A_rcore.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "sub"; "div"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "option"; "bool"; "Some"; "pair"; "prod"; "false"; "list"; "true"; "app"; "cons"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_thread"; "aa_live"; "topG"; "AA"; "aa_cls"; "class_state"; "cs_empty"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.F0A_limbo"; "LZ0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "nthZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refillA"; "needs_populate"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.F0A_rzone"; "RZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "kUserMapSize"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "MUCAP"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SMGlue RebuildM SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_rebuildW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.F0A_limbo OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.F0A_rzone.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BACK.
Variables (A : AA) (rhoE rhoL rho5 : valuation) (tp tpL : list word) (md md5 : Model) (p n : Z) (l1 l2 : list (Z * Z)).
Hypothesis HA : ltac2:(tb__ "0|0|
S2aS6VA;VrhoE;Vtp;Vmd;A5").
Hypothesis HLV : ltac2:(tb__ "0|1|
S1S1bS19S0S0A2M0A1S22VA;A1S1dG0Vl1;S1eG0S18S0S0Vp;Vn;A4Vl2;A3A3A3").
Hypothesis HCLS : blk_cls p n.
Hypothesis HROOM : ltac2:(tb__ "0|2|
S1S16S2eZ18M0S2bS26S25VA;A1G0S27A4M1A2S1cA3S9S7S28G1A1S34A2S36G0A1A2F_;").
Hypothesis HQL : ltac2:(tb__ "0|0|
S2cS2dVA;Z18A2VrhoL;VtpL;Vmd5;A4").
#[local] Abbreviation G := (aa_geom A).
#[local] Abbreviation T := (ag_thread (aa_geom A)).
#[local] Abbreviation RZa := (RZ A).

Variable xzb : Z -> bool.
Hypothesis XZT : ltac2:(tb__ "0|1|
S0S1S16Vxzb;R1A1S1cA3S2S9S7S21S20VA;A1A1M0Zae8A2R2A2S8R2S7G0Zc60A2A2A2F_;Fz;").
Hypothesis V1 : ltac2:(tb__ "0|0|
S0S3S32VA;R1A2A1S1S16Vxzb;R2A1S1aA3S1S15S13Q8A1A1SdS6S11Vrho5;A1R3A3SdS6S11VrhoE;A1R3A3A3F_;F_;Fz;").
Hypothesis VL : ltac2:(tb__ "0|2|
S0S8R1S23S20VA;A1M0A1A2S3S29Vp;Vn;R2A3A1S1S16Vxzb;R3A1S1aA3S3S2S9S7S21G0A1M1Z50A2R4A2S8R4S7G1Z70A2A2A2A1S1S15S13Q8A1A1SdS6S11Vrho5;A1R5A3SdS6S11VrhoL;A1R5A3A3F_;F_;F_;F_;Fz;").
Hypothesis V3 : ltac2:(tb__ "0|1|
S0S1S16Vxzb;R1A1S1cA3S4S13Q8A1M0G0S1S15G0A1SdS6S11Vrho5;A1R3A3S17G0R1A2A3Lb;A2F_;Fz;").

Lemma XZF : ltac2:(tb__ "0|1|
S0S3S2S9S21S20VA;A1A1M0R1A2S8R1S7G0Z1000A2A2A2A1S1S16Vxzb;R2A1S1aA3F_;Fz;").
Proof. intros z Hz. destruct (xzb z) eqn:E; [exfalso; pose proof (XZT z E); lia | reflexivity]. Qed.
Lemma HLin : ltac2:(tb__ "0|0|
S2fS19S0S0A2S18S0S0Vp;Vn;A4S22VA;A1A3").
Proof. rewrite HLV. apply in_or_app. right. left. reflexivity. Qed.

Lemma V_live : ltac2:(tb__ "0|1|
S0S0S0S2fS19S0S0A2S18S0S0R3R2A4S22VA;A1A3S5S2S9SaR4S35R3A1A2R2A2S8R2S7R4R3A2A2A2S2S9S33R4A1M0R2A2S8R2S7G0SbS7R3Z7A2Z8A2A2A2A2A2S1S15S13Q8A1A1SdS6S11Vrho5;A1R3A3SdS6S11VrhoE;A1R3A3A3F_;F_;Fz;Fm;Fb;").
Proof.
  intros b m z Hin Hz. apply V1; [exact (RZ_live A rhoE tp md HA HROOM b m z Hin Hz) | apply XZF; exact (live_offT A rhoE tp md HA b m z Hin Hz)].
Qed.

Lemma cell_present : ltac2:(tb__ "0|1|
SeS0S1fS0S0SfR5S10R4R3R2A3A2S2S9R5R2A2S8R2S7R5ScR4A1A2A2A2S4S13Q8A1M0G0S1S15G0A1R8R4A1S17G0R1A2A3Lb;A2F_;F_;Fz;Fv;Fw;Fa;Fm;").
Proof.
  intros m a w v z Hc Hz. specialize (Hc (Z.to_nat (z - a)) ltac:(cbn [c_w]; lia)). cbn [c_addr c_w c_val] in Hc.
  rewrite Z2Nat.id in Hc by lia. replace (a + (z - a)) with z in Hc by lia. eexists; exact Hc.
Qed.
Lemma QC_present : ltac2:(tb__ "0|2|
S0S2S9S7S21S20VA;A1A1M0Z50A2R1A2S8R1S7G0Z70A2A2A2S4S13Q8A1M1G1S1S15G1A1SdS6S11VrhoE;A1R3A3S17G1R1A2A3Lb;A2F_;Fz;").
Proof.
  intros z Hz. destruct (AInvB_Q kQuarantineCacheMax A rhoE tp md HA) as (_ & HQM & _).
  destruct HQM as (_ & _ & _ & (C0 & _ & PR & C24) & _). change (ag_thread (aa_geom A) + 0x50) with (T + 80) in C0, PR, C24.
  destruct (Z_lt_dec z (T + 88)) as [L|L]; [exact (cell_present _ _ _ _ z C0 ltac:(cbn; lia))|].
  destruct (Z_lt_dec z (T + 104)) as [L2|L2]; [exact (PR z ltac:(lia)) | exact (cell_present _ _ _ _ z C24 ltac:(cbn; lia))].
Qed.

Theorem refill_back : ltac2:(tb__ "0|0|
S2aS6S2dVA;Z18A2Vrho5;VtpL;Vmd5;A5").
Proof.
  pose proof HA as (HG & _ & _ & (Hsep & Hlive & _) & _).
  destruct (Hsep p n HLin) as (N1 & _). pose proof (rz_bound n) as RB.
  pose proof (F0A_rebuild.BLK A rhoE tp md p n l1 l2 0 HA HLV HCLS) as (_ & _ & _ & B4 & B5 & _).

  assert (HQ5 : AInvQC (refillA A 24) rho5 tpL md5).
  { set (xq := fun z => xzb z || ((T + 80 <=? z) && (z <? T + 112))).
    assert (XQ : forall z, xq z = false -> xzb z = false /\ ~ (T + 80 <= z < T + 112)).
    { intros z Hz. unfold xq in Hz. apply orb_false_iff in Hz as [Hz1 Hz2]. split; [exact Hz1|]. apply andb_false_iff in Hz2.
      destruct Hz2 as [Hz2|Hz2]; [apply Z.leb_gt in Hz2 | apply Z.ltb_ge in Hz2]; clear -Hz2; lia. }
    apply (AInvQC_limbo_top A rhoE tp md p n l1 l2 (refillA A 24) rhoL rho5 tpL md5 xq HA HLV HCLS eq_refl eq_refl eq_refl eq_refl HQL).
    - intros z Hz. unfold xq in Hz. apply orb_true_iff in Hz as [Hz|Hz]; [right; pose proof (XZT z Hz) as X; clear -X; lia | left].
      apply andb_true_iff in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. clear -Hz1 Hz2. lia.
    - intros z Hz HL Hx. destruct (XQ z Hx) as [X1 X2]. exact (VL z Hz HL X1 X2).
    - intros z Hz Hu.
      assert (HCZ : F0A_rebuild.CZ p n z) by (unfold F0A_rebuild.CZ; destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.F0A_limbo.LZ_cases A rhoE tp md p n l1 l2 HA HLV HCLS z Hz) as [K|K]; [left | right]; exact K).
      rewrite (V1 z (RZ_CZ A rhoE tp md HA HROOM p n l1 l2 HLV HCLS z HCZ) (XZF z (CZ_offT A rhoE tp md HA p n l1 l2 HLV HCLS z HCZ))).
      destruct (blkF_mem A rhoE tp md p n HA HLin HCLS) as (t & _ & _ & CW & CL & PSH & PTL).
      destruct Hz as [Hz|[Hz|Hz]].
      + destruct (Z_lt_dec z (p - 12)) as [L|L].
        * specialize (CW (Z.to_nat (z - (p - 16))) ltac:(cbn; lia)). cbn [c_addr] in CW. rewrite Z2Nat.id in CW by lia. replace (p - 16 + (z - (p - 16))) with z in CW by lia. eexists; exact CW.
        * specialize (CL (Z.to_nat (z - (p - 12))) ltac:(cbn; lia)). cbn [c_addr] in CL. rewrite Z2Nat.id in CL by lia. replace (p - 12 + (z - (p - 12))) with z in CL by lia. eexists; exact CL.
      + apply PTL. clear -Hz Hu. lia.
      + exact (PSH z Hz).
    - intros z Hz. destruct (xzb z) eqn:EX; [exact (V3 z EX)|]. unfold xq in Hz. rewrite EX in Hz. cbn [orb] in Hz.
      apply andb_true_iff in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2.
      rewrite (V1 z ltac:(apply (RZ_T A rhoE tp md HA HROOM z); left; clear -Hz1 Hz2; lia) EX). apply QC_present. clear -Hz1 Hz2. lia.
    - intros _. apply (lb_body_agree (maskv (fs_footb G) (view segsA (rm rhoE))) _ A p n N1); [|exact (Hlive p n HLin)].
      intros z Hz. unfold maskv. rewrite (V_live p n z HLin Hz). reflexivity. }

  assert (HQ : AInvQ (refillA A 24) rho5 tpL md5).
  { apply (AInvQC_back (refillA A 24) rho5 tpL md5); [|exact HQ5]. intros b m Hin. change (aa_live (refillA A 24)) with (aa_live A) in Hin.
    change (aa_geom (refillA A 24)) with G. destruct (Hlive b m Hin) as (B1 & _). destruct (Hsep b m Hin) as (M1 & _). pose proof (rz_bound m) as RBm.
    unfold maskv in B1 |- *. change InvLaws.segsA with segsA. rewrite (V_live b m (b - 16) Hin ltac:(left; clear -M1 RBm; lia)). exact B1. }

  destruct (AInvB_Q kQuarantineCacheMax A rhoE tp md HA) as (HAQ & HQM & QB1 & QB2).
  pose proof HAQ as (_ & _ & _ & (_ & _ & _ & _ & (HQP & _) & _) & _).
  pose proof (F0A_rebuild.GEO A rhoE tp md 0 0 HA) as (_ & _ & _ & _ & _ & _ & _ & _ & TI & _).
  apply (AInvQ_back (refillA A 24) rho5 tpL md5 HQ); [|exact QB1|exact QB2].
  change (q_mem (view segsA (rm rho5)) A). apply (q_mem_frame A (view segsA (rm rhoE)) (view segsA (rm rho5)) HQP); [| | |exact HQM].
  - intros z Hz. apply V1; [exact (RZ_qfoot A rhoE tp md HA HROOM z Hz) | apply XZF; exact (qfoot_offT A rhoE tp md HA z Hz)].
  - intros z Hz. apply V1; [apply (RZ_T A rhoE tp md HA HROOM z); left; clear -Hz; lia|]. destruct (xzb z) eqn:E; [exfalso; pose proof (XZT z E); clear -Hz H; lia | reflexivity].
  - intros z Hz. apply V1; [apply (RZ_img A rhoE tp md HA HROOM z); unfold QG, IMG_LO, IMG_HI in *; clear -Hz; lia|].
    apply XZF. unfold QG in Hz. clear -Hz TI. lia.
Qed.
End BACK.

Theorem refill_fwd : ltac2:(tb__ "0|c|
S24S12S12S1bS13Q40A1A1S30S0S0S1bS19S0S0A2M0A1M1G1S2aS6R9R8R6R5A5S1G1S22RaA1S1dG0R3S1eG0S18S0S0R5R4A4R2A3A3A3S31R6R5A2S0S8R1S23S20RdA1A1A2S3S29R9R8R2A3A1S3S2S9S7S21S20RfA1A1M2Z50M3A2R3A2S8R3S7G2Z70M4A2A2A2A1S1S15S13Q8M5A1M6A1M7SdS6S11ReA1M8R4A3SdS6S11RfA1M9R4A3A3F_;F_;F_;Fz;S0S2S9S7S21S20ReA1A1MaG3A2R1A2S8R1S7GaG4A2A2A2S4G6G6S1G7SdS6G8R3A3S17G6R1A2MbA3Lb;A2F_;Fz;S0S29RaR9R1A3S4G6G6S1G7SdS6G9R3A3GbA3Lb;A2F_;Fz;S4G6G6S2S1G7SdS6G8SaRbZ10A2A3GbA3S3S1G6R1S14G5Z2A2A3A1A2Lx;A2S2cR10ReRdRcA4F_;F_;F_;F_;F_;F_;F_;Fl2;Fl1;Fn;Fp;Fmd;Ftp;FrhoC;FrhoE;FA;").
Proof.
  intros A rhoE rhoC tp md p n l1 l2 HA HLV HCLS F1 FQ F2 (x & F3 & F3n).
  set (xq := fun z => (ag_thread (aa_geom A) + 80 <=? z) && (z <? ag_thread (aa_geom A) + 112)).
  assert (XQ : forall z, xq z = true <-> ag_thread (aa_geom A) + 80 <= z < ag_thread (aa_geom A) + 112).
  { intros z. unfold xq. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. }
  apply (AInvQC_limbo_top A rhoE tp md p n l1 l2 A rhoE rhoC tp md xq HA HLV HCLS eq_refl eq_refl eq_refl eq_refl (AInvA_QC A rhoE tp md HA)).
  - intros z Hz. left. exact (proj1 (XQ z) Hz).
  - intros z Hz HL Hx. apply (F1 z Hz HL). intros Hq. rewrite (proj2 (XQ z) Hq) in Hx. discriminate Hx.
  - intros z Hz _. exact (F2 z Hz).
  - intros z Hz. exact (FQ z (proj1 (XQ z) Hz)).
  - intros H2. exfalso. rewrite F3 in H2. injection H2 as E. exact (F3n E).
Qed.
End F0A_rcore.

(* [comment removed for export] *)
Module SpineMallocQp.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "entailsA"; "ax_X"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "ss_facts"; "ss_objs"; "SAlu"; "ss_lenient"; "swf"; "SVar"; "reg_sv"; "SPNot"; "SPBranch"; "sprop_below"; "valuation"; "SPUle"; "rw"; "ss_pc"; "sv_below"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "factsQ"; "BASEFq"; "BASEOq"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQi"; "e3r"; "FUEL"; "W0"; "icc"; "r_2_0"; "nob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "cX"; "GR"; "beg1"; "beg2"; "cE1"; "keepn"; "cP2"; "cXL"; "nobj"; "O_pcm"; "PV4"; "cE2"; "LV0"; "O_ri"; "cL1"; "cT1"; "cD"; "cPa"; "cPb"; "LV2"; "PV6"; "rMS"; "sMS"; "LV3"; "O_pccK"; "vMU"; "cFm"; "vK"; "HINT_au"; "HINT_k"; "HINT_map"; "LNX"; "PNX"; "idx_rot"; "k_e"; "relM"; "ri_has"; "rotM"; "vAU"; "vMFA"; "F_new"; "vNEW"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.SpineMallocQp"; "r_xF_0"; "r_xU_0"; "cmcF"; "cmcU"; "r_9M_0"; "r_9P_0"; "cl0M"; "cl0P"; "cp2c"; "ct0M"; "ct0P"; "nobFM"; "nobFP"; "r_lM_1"; "r_lP_1"; "r_p1_0"; "r_p1_1"; "r_d_0"; "r_f_0"; "cfm"; "r_f_1"; "r_h_0"; "r_mF_0"; "r_mU_0"; "rf1"; "ru1"; "dmF"; "dmU"; "r_jM_0"; "r_jP_0"; "r_p2a_0"; "r_p2a_1"; "r_p2b_0"; "r_p2b_1"; "s_fbkM"; "s_fbkP"; "s_finM"; "s_finP"; "r_lM_0"; "r_lP_0"; "r_t1M_0"; "r_t1P_0"; "s_bkM"; "s_bkP"; "s_inM"; "s_inP"; "xlM"; "xlP"; "r_t1M_1"; "r_t1P_1"; "cellsfM"; "cellsfP"; "r_flM_0"; "r_flP_0"; "r_t0M_0"; "r_t0P_0"; "s_fM"; "s_fP"; "sa0"; "sa1"; "sb0"; "sb1"; "y4M"; "y4P"; "y3M"; "y3P"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "instr"; "ALU_SLL"; "ALU_XOR"; "Ecall"; "BC_LTU"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4"; "swM"; "O_rif"; "idx_sw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "phase"; "JR"; "gh_new"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ10"; "cMr"; "a2_e"; "cMc";
"dMSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQ13"; "F_lt"; "O_fcell"; "faend_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7"; "F_mu0"; "F_hi"; "x19_e0"; "x19_e1"; "popfacts"; "size_e_hi"; "size_e_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ9"; "O_piece"; "O_shp"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "L_rf"; "NXRC"; "JLRf"; "NXR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQ12"; "F_geu"; "new_e"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQ14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15"; "fillT"; "phUF3"; "pieceT"; "fmT"; "headT"; "midT"; "phFin"; "phU3"; "runT"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP"; "PF"; "PU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQ12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQ13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQ14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQi.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_p1__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ415c0SaS2aZ41600SdS2aA1A3A3S4S33A1SbA5").
Local Strategy expand [R_p1__R].
Definition r_p1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_p1__R).
Definition r_p1_0 := Eval vm_compute in (nth 0 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition r_p1_1 := Eval vm_compute in (nth 1 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition R_p2a__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41630SdS2aA1A3S47S2bS2fA1S4S76A1A2SbA5").
Local Strategy expand [R_p2a__R].
Definition r_p2a := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_p2a__R).
Definition r_p2a_0 := Eval vm_compute in (nth 0 r_p2a (mkLeafA (cPa (factsQ e3r) (la_state r_p1_0)) RsCut)).
Definition r_p2a_1 := Eval vm_compute in (nth 1 r_p2a (mkLeafA (cPa (factsQ e3r) (la_state r_p1_0)) RsCut)).
Definition R_p2b__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41630SdS2aA1A3S48S2bS2fA1S4S77A1A2SbA5").
Local Strategy expand [R_p2b__R].
Definition r_p2b := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_p2b__R).
Definition r_p2b_0 := Eval vm_compute in (nth 0 r_p2b (mkLeafA (cPb (factsQ e3r) (la_state r_p1_1)) RsCut)).
Definition r_p2b_1 := Eval vm_compute in (nth 1 r_p2b (mkLeafA (cPb (factsQ e3r) (la_state r_p1_1)) RsCut)).
Definition cp2c := Eval vm_compute in (cP2c (factsQ e3r) (la_state r_p2a_1)).
Lemma FP_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18S23SafS60S51A3SdS18A1A3S1bS3S4S33A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p1 : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ415c0SaS2aZ41600SdS2aA1A3A3S4S33A1SbA5S10G0SaS5S76SaS5S77SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p1__R <: R_p1__R = Some [r_p1_0; r_p1_1]). Qed.
Lemma LN_p1 : ltac2:(tb__ "0|0|
S0ScS1eS3S4S33A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p1 : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S4S33A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18Sd2SdS18A1A3S1bS3S4S76A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22Sd2A1SdS18A1A3S1bS3S4S77A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pa : ltac2:(tb__ "0|0|
S0ScS1fS3S47S2bS2fA1S4S76A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pa : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S76A1M4A1S3S47S2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd6S20Sb9A1A4SdG0A1A3SaS18S54SaS18S26S4fS1aZdffc0000A1A2SdS18A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pa : ltac2:(tb__ "0|1|
S0ScS64S19S3S47S2bS2fA1S4S76A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pb : ltac2:(tb__ "0|0|
S0ScS1fS3S48S2bS2fA1S4S77A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pb : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S77A1M4A1S3S48S2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd7S20Sb9A1A4SdG0A1A3SaS18S54SaS18S26S4fS1aZdffc0000A1A2SdS18A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pb : ltac2:(tb__ "0|1|
S0ScS64S19S3S48S2bS2fA1S4S77A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2a : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41630SdS2aA1A3S47S2bS2fA1S4S76A1A2SbA5S10G0SaS5S85SaS5S86SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2a__R <: R_p2a__R = Some [r_p2a_0; r_p2a_1]). Qed.
Lemma LN_p2a : ltac2:(tb__ "0|0|
S0ScS1eS3S47S2bS2fA1S4S76A1A2A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2a : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S47S2bS2fA1S4S76A1A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2b : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41630SdS2aA1A3S48S2bS2fA1S4S77A1A2SbA5S10G0SaS5S87SaS5S88SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2b__R <: R_p2b__R = Some [r_p2b_0; r_p2b_1]). Qed.
Lemma LN_p2b : ltac2:(tb__ "0|0|
S0ScS1eS3S48S2bS2fA1S4S77A1A2A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2b : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S48S2bS2fA1S4S77A1A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa0_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18Sd1SdS18A1A3S1bS3S4S85A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a0 : ltac2:(tb__ "0|0|
S0ScS1fS3S3cS2bS2fA1S4S85A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a0 : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S85A1M4A1S3S3cS2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd3S1aZ40000A1A4SaG0S12S17S17S1aZ0A1S4fA4SdG0A1A3A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a0 : ltac2:(tb__ "0|1|
S0ScS64S19S3S3cS2bS2fA1S4S85A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsQ e3r) (la_state r_p2a_0))) (ax_S cp2c)).
Lemma ENT_a0 : ltac2:(tb__ "0|0|
S0ScS8S3cS2bS2fA1S4S85A1A2S6fSa1A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a0 : ltac2:(tb__ "0|0|
S0ScS66Sa1S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa1_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22Sd1A1SdS18A1A3S1bS3S4S86A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a1 : ltac2:(tb__ "0|0|
S0ScS1fS3S3cS2bS2fA1S4S86A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a1 : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S86A1M4A1S3S3cS2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd4S1aZ40000A1A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a1 : ltac2:(tb__ "0|1|
S0ScS64S19S3S3cS2bS2fA1S4S86A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsQ e3r) (la_state r_p2a_1))) (ax_S cp2c)).
Lemma ENT_a1 : ltac2:(tb__ "0|0|
S0ScS8S3cS2bS2fA1S4S86A1A2S6fSa2A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a1 : ltac2:(tb__ "0|0|
S0ScS66Sa2S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb0_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18Sd1SdS18A1A3S1bS3S4S87A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0ScS1fS3S3cS2bS2fA1S4S87A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S87A1M4A1S3S3cS2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd3S1aZ40000A1A4SaG0S12S17S17S1aZ0A1S4fA4SdG0A1A3A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0ScS64S19S3S3cS2bS2fA1S4S87A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsQ e3r) (la_state r_p2b_0))) (ax_S cp2c)).
Lemma ENT_b0 : ltac2:(tb__ "0|0|
S0ScS8S3cS2bS2fA1S4S87A1A2S6fSa3A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b0 : ltac2:(tb__ "0|0|
S0ScS66Sa3S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb1_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22Sd1A1SdS18A1A3S1bS3S4S88A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0ScS1fS3S3cS2bS2fA1S4S88A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S88A1M4A1S3S3cS2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd4S1aZ40000A1A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0ScS64S19S3S3cS2bS2fA1S4S88A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsQ e3r) (la_state r_p2b_1))) (ax_S cp2c)).
Lemma ENT_b1 : ltac2:(tb__ "0|0|
S0ScS8S3cS2bS2fA1S4S88A1A2S6fSa4A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b1 : ltac2:(tb__ "0|0|
S0ScS66Sa4S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma head_i : ltac2:(tb__ "0|0|
Sf9S31Sb2S4S33A1S6fA4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE HC.
  exact (populate_head A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE FUEL e3r (la_state r_2_0) r_p1_0 r_p1_1 r_p2a_0 r_p2a_1 r_p2b_0 r_p2b_1 cp2c sa0 sa1 sb0 sb1
           (In_of_inclb _ _ FP_inb) R_p1 LN_p1 NX_p1 (In_of_inclb _ _ Fa_inb) (In_of_inclb _ _ Fb_inb) W_pa D_pa NXe_pa W_pb D_pb NXe_pb R_p2a LN_p2a NX_p2a R_p2b LN_p2b NX_p2b
           (In_of_inclb _ _ Fa0_inb) (In_of_inclb _ _ Fa1_inb) (In_of_inclb _ _ Fb0_inb) (In_of_inclb _ _ Fb1_inb) W_a0 W_a1 W_b0 W_b1 D_a0 D_a1 D_b0 D_b1 NXe_a0 NXe_a1 NXe_b0 NXe_b1
           ENT_a0 ENT_a1 ENT_b0 ENT_b1 SID_a0 SID_a1 SID_b0 SID_b1 r tp Q HC).
Qed.
Definition R_xU__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ7050cSdS2aA1A3S6fSbA5").
Local Strategy expand [R_xU__R].
Definition r_xU := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_xU__R).
Definition r_xU_0 := Eval vm_compute in (nth 0 r_xU (mkLeafA cp2c RsCut)).
Definition R_mU__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZde378SdS2aA1A3SbbS36S4S68A1S38A2S38Z40000A3SbA5").
Local Strategy expand [R_mU__R].
Definition r_mU := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_mU__R).
Definition r_mU_0 := Eval vm_compute in (nth 0 r_mU (mkLeafA (commit_post (cX (la_state r_xU_0) beg1) beg1 262144) RsCut)).
Definition cmcU := Eval vm_compute in (cMc (la_state r_mU_0) beg1).
Lemma CMCU_eq : ltac2:(tb__ "0|0|
S0S7Sc9S4S7eA1S38A2S6aA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmU := Eval vm_compute in (dMSf cmcU).
Lemma DMU_eq : ltac2:(tb__ "0|0|
S0S7ScaS6aA1S82A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition ru1 := Eval vm_compute in (relM dmU).
Lemma RU1_eq : ltac2:(tb__ "0|0|
S0S7S59S82A1S80A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xU : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ7050cSdS2aA1A3S6fSbA5S10G0SaS5S68SdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xU__R <: R_xU__R = Some [r_xU_0]). Qed.
Lemma LN_xU : ltac2:(tb__ "0|0|
S0ScS1eS3S6fA1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xU : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S6fA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xU : ltac2:(tb__ "0|0|
S0ScS1fS3S36S4S68A1S38A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xU : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S68A1M4A1S3S36G4S38A2A1A2S10G3S12G1G2SaG0S12S17S17SecS38A1S38A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xU : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S36S4S68A1S38A2A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xUb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S36S4S68A1S38A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xU : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S36S4S68A1S38A2A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xU : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S36S4S68A1S38A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xU : ltac2:(tb__ "0|0|
S0S11SabA1Se5S35S28S3S36S4S68A1S38A2A1A1A2S10SabSaeA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1Z11A2S1aZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZaA2S38A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZbA2S1aZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZcA2S1aZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZdA2S1aZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZeA2S1aZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZfA2S1aZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xU : ltac2:(tb__ "0|0|
S0ScS29S19S3S36S4S68A1S38A2A1A1S38A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mU : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZde378SdS2aA1A3SbbS36S4S68A1S38A2S38Z40000A3SbA5S10G0SaS5S7eSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mU__R <: R_mU__R = Some [r_mU_0]). Qed.
Lemma LN_mU : ltac2:(tb__ "0|0|
S0ScS1eS3SbbS36S4S68A1S38A2S38Z40000A3A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mU : ltac2:(tb__ "0|0|
S0ScS63S37S19S3SbbS36S4S68A1S38A2S38Z40000A3A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mU : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S4S7eA1A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SaS16Sd8S38A1SdS16A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mUb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S4S7eA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mU : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S4S7eA1A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrU : ltac2:(tb__ "0|0|
S0ScS1fS3Sc7S4S7eA1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrU : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S7eA1M4A1S3Sc7G4A1A1A2S10G3S12G1G2SaG0S12S17S17Sc8S38A1S1aZ8000A1A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcU : ltac2:(tb__ "0|0|
S0ScS1fS3S6aA1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msU : ltac2:(tb__ "0|1|
S0S11SeS16A1M0A1Se7S6aSc0S4cS6aA1A3S10G0S4bS6aA1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msU : ltac2:(tb__ "0|0|
S0ScSe6S6aSc0S4cS6aA1S4bS6aA1Sb0S5S7S4Sc1A4A5SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msU : ltac2:(tb__ "0|0|
S0ScS63Se4S19S3S6aA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msU : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S6aA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msU : ltac2:(tb__ "0|1|
S0ScSdbS18S24S19S3S6aA1M0A1A1S1bG0A1A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msU : ltac2:(tb__ "0|0|
S0ScSdbS18S24S19S3SbcS6aS4cS6aA1S4bS6aA1A3A1A1A1S1bS3S6aA1A1A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rU : ltac2:(tb__ "0|0|
S0ScSc2S57S82A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rUb : ltac2:(tb__ "0|0|
S0ScSdaU1S3eS82A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rU : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S5bS82A1A1A1M0S13S16Sb1S16Sb6S3eS82A1U2A2G0A3SaS16Sd8S38A1SaS16Sd9S38A1SdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceU_i : ltac2:(tb__ "0|0|
Sf7S31Sb2S109S38S6fS80A6").
Proof.
  rewrite <- RU1_eq, <- DMU_eq, <- CMCU_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PU beg1 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cp2c r_xU_0 r_mU_0
           R_xU LN_xU NX_xU W_xU D_xU SK_xU (inclb_incl _ _ XF_xUb) XX_xU NXc_xU IC_xU R17_xU R10_xU BEL_xU R11_xU R12_xU R13_xU R14_xU R15_xU
           R_mU LN_mU NX_mU SK_mU (inclb_incl _ _ XF_mUb) XX_mU W_mrU D_mrU _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCU_eq, ?DMU_eq; [exact W_mcU | exact E_msU | exact CHK_msU | exact NF_msU | exact NX_msU | exact FBC_msU | exact FBT_msU | exact ND_rU | apply Nat.leb_le; exact NO_rUb | exact OB_rU].
Qed.
Definition R_d__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ416f0SdS2aA1A3S80SbA5").
Local Strategy expand [R_d__R].
Definition r_d := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_d__R).
Definition r_d_0 := Eval vm_compute in (nth 0 r_d (mkLeafA ru1 RsCut)).
Definition R_f__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ3f270SaS2aZ4172cSdS2aA1A3A3S46S2bS2fA1S4S78A1A2SbA5").
Local Strategy expand [R_f__R].
Definition r_f := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_f__R).
Definition r_f_0 := Eval vm_compute in (nth 0 r_f (mkLeafA (cD (factsQ e3r) (la_state r_d_0)) RsCut)).
Definition r_f_1 := Eval vm_compute in (nth 1 r_f (mkLeafA (cD (factsQ e3r) (la_state r_d_0)) RsCut)).
Lemma R_d : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ416f0SdS2aA1A3S80SbA5S10G0SaS5S78SdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_d__R <: R_d__R = Some [r_d_0]). Qed.
Lemma LN_d : ltac2:(tb__ "0|0|
S0ScS1eS3S80A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_d : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S80A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_d : ltac2:(tb__ "0|0|
S0ScS1fS3S46S2bS2fA1S4S78A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_d : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S78A1M4A1S3S46S2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17SeeS5fA4SdG0A1A3S5eA4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_d : ltac2:(tb__ "0|1|
S0ScS64S19S3S46S2bS2fA1S4S78A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_f : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ3f270SaS2aZ4172cSdS2aA1A3A3S46S2bS2fA1S4S78A1A2SbA5S10G0SaS5S79SaS5S7bSdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_f__R <: R_f__R = Some [r_f_0; r_f_1]). Qed.
Lemma LN_f : ltac2:(tb__ "0|0|
S0ScS1eS3S46S2bS2fA1S4S78A1A2A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_f : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S46S2bS2fA1S4S78A1A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma F0_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18SedSdS18A1A3S1bS3S4S79A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fm_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22SedA1SdS18A1A3S1bS3S4S7bA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma mid_i : ltac2:(tb__ "0|0|
SfaS31Sb2S80S4S79A1S4S7bA1A5").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (populate_mid A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE PF ph FUEL e3r ru1 r_d_0 r_f_0 r_f_1 R_d LN_d NX_d W_d D_d NXe_d R_f LN_f NX_f (In_of_inclb _ _ F0_inb) (In_of_inclb _ _ Fm_inb) r tp Q).
Qed.
Definition cfm := Eval vm_compute in (cFm (la_state r_f_1)).
Lemma CFM_eq : ltac2:(tb__ "0|0|
S0S7S50S4S7bA1A1S7aA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0ScS1fS3S50S4S7bA1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S7bA1M4A1S3S50G4A1A1A2S10G3S12G1G2SaG0S12S17S17SefS1dSa9S5dS1aZ40000A1A3A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma fm_i : ltac2:(tb__ "0|0|
Sf8S31Sb2S4S7bA1S7aA4").
Proof.
  rewrite <- CFM_eq. intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (famap_restate A Kc rb tp0 md0 TR KIT W0 UStopLe rho HE PF (la_state r_f_1) W_fm D_fm ph r tp Q).
Qed.
Definition R_xF__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ7050cSdS2aA1A3S7aSbA5").
Local Strategy expand [R_xF__R].
Definition r_xF := Eval vm_compute in ((fun ro8__ : option (list leafA) => (match ro8__ with Some l => l | None => [] end)) R_xF__R).
Definition r_xF_0 := Eval vm_compute in (nth 0 r_xF (mkLeafA cfm RsCut)).
Definition R_mF__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZde378SdS2aA1A3SbbS36S4S67A1S39A2S39Z40000A3SbA5").
Local Strategy expand [R_mF__R].
Definition r_mF := Eval vm_compute in ((fun ro9__ : option (list leafA) => (match ro9__ with Some l => l | None => [] end)) R_mF__R).
Definition r_mF_0 := Eval vm_compute in (nth 0 r_mF (mkLeafA (commit_post (cX (la_state r_xF_0) beg2) beg2 262144) RsCut)).
Definition cmcF := Eval vm_compute in (cMc (la_state r_mF_0) beg2).
Lemma CMCF_eq : ltac2:(tb__ "0|0|
S0S7Sc9S4S7dA1S39A2S69A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmF := Eval vm_compute in (dMSf cmcF).
Lemma DMF_eq : ltac2:(tb__ "0|0|
S0S7ScaS69A1S81A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition rf1 := Eval vm_compute in (relM dmF).
Lemma RF1_eq : ltac2:(tb__ "0|0|
S0S7S59S81A1S7fA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xF : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ7050cSdS2aA1A3S7aSbA5S10G0SaS5S67SdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xF__R <: R_xF__R = Some [r_xF_0]). Qed.
Lemma LN_xF : ltac2:(tb__ "0|0|
S0ScS1eS3S7aA1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xF : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S7aA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xF : ltac2:(tb__ "0|0|
S0ScS1fS3S36S4S67A1S39A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xF : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S67A1M4A1S3S36G4S39A2A1A2S10G3S12G1G2SaG0S12S17S17SecS39A1S39A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xF : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S36S4S67A1S39A2A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xFb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S36S4S67A1S39A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xF : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S36S4S67A1S39A2A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xF : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S36S4S67A1S39A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xF : ltac2:(tb__ "0|0|
S0S11SabA1Se5S35S28S3S36S4S67A1S39A2A1A1A2S10SabSaeA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1Z11A2S1aZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZaA2S39A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZbA2S1aZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZcA2S1aZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZdA2S1aZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZeA2S1aZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZfA2S1aZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xF : ltac2:(tb__ "0|0|
S0ScS29S19S3S36S4S67A1S39A2A1A1S39A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mF : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZde378SdS2aA1A3SbbS36S4S67A1S39A2S39Z40000A3SbA5S10G0SaS5S7dSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mF__R <: R_mF__R = Some [r_mF_0]). Qed.
Lemma LN_mF : ltac2:(tb__ "0|0|
S0ScS1eS3SbbS36S4S67A1S39A2S39Z40000A3A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mF : ltac2:(tb__ "0|0|
S0ScS63S37S19S3SbbS36S4S67A1S39A2S39Z40000A3A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mF : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S4S7dA1A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SaS16Sd8S39A1SdS16A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mFb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S4S7dA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mF : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S4S7dA1A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrF : ltac2:(tb__ "0|0|
S0ScS1fS3Sc7S4S7dA1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrF : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S7dA1M4A1S3Sc7G4A1A1A2S10G3S12G1G2SaG0S12S17S17Sc8S39A1S1aZ8000A1A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcF : ltac2:(tb__ "0|0|
S0ScS1fS3S69A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msF : ltac2:(tb__ "0|1|
S0S11SeS16A1M0A1Se7S69Sc0S4cS69A1A3S10G0S4bS69A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msF : ltac2:(tb__ "0|0|
S0ScSe6S69Sc0S4cS69A1S4bS69A1Sb0S5S7S4Sc1A4A5SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msF : ltac2:(tb__ "0|0|
S0ScS63Se4S19S3S69A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msF : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S69A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msF : ltac2:(tb__ "0|1|
S0ScSdbS18S24S19S3S69A1M0A1A1S1bG0A1A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msF : ltac2:(tb__ "0|0|
S0ScSdbS18S24S19S3SbcS69S4cS69A1S4bS69A1A3A1A1A1S1bS3S69A1A1A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rF : ltac2:(tb__ "0|0|
S0ScSc2S57S81A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rFb : ltac2:(tb__ "0|0|
S0ScSdaU1S3eS81A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rF : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S5bS81A1A1A1M0S13S16Sb1S16Sb6S3eS81A1U2A2G0A3SaS16Sd8S39A1SaS16Sd9S39A1SdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceF_i : ltac2:(tb__ "0|0|
Sf7S31Sb2S108S39S7aS7fA6").
Proof.
  rewrite <- RF1_eq, <- DMF_eq, <- CMCF_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP.PF beg2 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cfm r_xF_0 r_mF_0
           R_xF LN_xF NX_xF W_xF D_xF SK_xF (inclb_incl _ _ XF_xFb) XX_xF NXc_xF IC_xF R17_xF R10_xF BEL_xF R11_xF R12_xF R13_xF R14_xF R15_xF
           R_mF LN_mF NX_mF SK_mF (inclb_incl _ _ XF_mFb) XX_mF W_mrF D_mrF _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCF_eq, ?DMF_eq; [exact W_mcF | exact E_msF | exact CHK_msF | exact NF_msF | exact NX_msF | exact FBC_msF | exact FBT_msF | exact ND_rF | apply Nat.leb_le; exact NO_rFb | exact OB_rF].
Qed.
Definition R_h__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ4172cSdS2aA1A3S7fSbA5").
Local Strategy expand [R_h__R].
Definition r_h := Eval vm_compute in ((fun ro10__ : option (list leafA) => (match ro10__ with Some l => l | None => [] end)) R_h__R).
Definition r_h_0 := Eval vm_compute in (nth 0 r_h (mkLeafA rf1 RsCut)).
Lemma R_h : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ4172cSdS2aA1A3S7fSbA5S10G0SaS5S7cSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_h__R <: R_h__R = Some [r_h_0]). Qed.
Lemma LN_h : ltac2:(tb__ "0|0|
S0ScS1eS3S7fA1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_h : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S7fA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run_i : ltac2:(tb__ "0|0|
SfdS7fS4S7cA1A2").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc ph r tp Q HC.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc FUEL [0x4172c] rf1 [r_h_0] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _. exact (HC r1).
Qed.
Definition R_fhP__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41740SdS2aA1A3S4S79A1SbA5").
Local Strategy expand [R_fhP__R].
Definition r_flP := Eval vm_compute in ((fun ro12__ : option (list leafA) => (match ro12__ with Some l => l | None => [] end)) R_fhP__R).
Definition r_flP_0 := Eval vm_compute in (nth 0 r_flP (mkLeafA (la_state r_f_0) RsCut)).
Definition cl0P := Eval vm_compute in (cL0 (factsQ e3r) (la_state r_flP_0)).
Definition R_l1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41740SaS2aZ4174cSdS2aA1A3A3S44S6eA1SbA5").
Local Strategy expand [R_l1P__R].
Definition r_lP := Eval vm_compute in ((fun ro11__ : option (list leafA) => (match ro11__ with Some l => l | None => [] end)) R_l1P__R).
Definition r_lP_0 := Eval vm_compute in (nth 0 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition r_lP_1 := Eval vm_compute in (nth 1 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition nobFP := Eval vm_compute in (length (ss_objs (ax_S cl0P))).
Definition s_fbkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lP_0) nobFP)) (ax_S cl0P)).
Definition s_finP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flP_0)) (ax_S cl0P)).
Definition R_fjP__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413ccSdS2aA1A3S3dS2bS2fA1S3bS4S75A1S73A2A2SbA5").
Local Strategy expand [R_fjP__R].
Definition r_jP := Eval vm_compute in ((fun ro13__ : option (list leafA) => (match ro13__ with Some l => l | None => [] end)) R_fjP__R).
Definition r_jP_0 := Eval vm_compute in (nth 0 r_jP (mkLeafA (cXL (factsQ e3r) (keepn (la_state r_lP_1) nobFP)) RsCut)).
Lemma SK_lP : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S6eA1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lP : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S6eA1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lPb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S6eA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lP : ltac2:(tb__ "0|0|
S0ScS64S19S3S6eA1A1S55A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1P : ltac2:(tb__ "0|0|
S0ScS1fS3S44S6eA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1P : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41740SaS2aZ4174cSdS2aA1A3A3S44S6eA1SbA5S10G0SaS5S8eSaS5S75SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1P__R <: R_l1P__R = Some [r_lP_0; r_lP_1]). Qed.
Lemma LN_l1P : ltac2:(tb__ "0|0|
S0ScS1eS3S44S6eA1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbP : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S8eA1A1A1M0S13S16Sb1S16S73G0A3SaS16SccSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxP : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S75A1A1A1M0S13S16Sb1S16S73G0A3SaS16SccSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkP : ltac2:(tb__ "0|0|
S0ScS8S3bS4S8eA1S73A2S6eS8aA3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkP : ltac2:(tb__ "0|0|
S0ScS66S8aS37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0P : ltac2:(tb__ "0|0|
S0S17S65S8aS42A2S1dSa9S20S42A1S1aZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2P : ltac2:(tb__ "0|0|
S0S17S65S8aS49A2S1dSa9S20S49A1S20Sb9A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3P : ltac2:(tb__ "0|0|
S0S17S65S8aS4dA2S1dSa9ScdS1dSacS1dSadS20S42A1S1aZffffffffffffffffA1A3S1aZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbPb : ltac2:(tb__ "0|0|
S0ScS61SaS18ScbSdS18A1A3S1bS3S4S8eA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxPb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22ScbA1SdS18A1A3S1bS3S4S75A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhP : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41740SdS2aA1A3S4S79A1SbA5S10G0SaS5S9cSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhP__R <: R_fhP__R = Some [r_flP_0]). Qed.
Lemma LN_fhP : ltac2:(tb__ "0|0|
S0ScS1eS3S4S79A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhP : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S4S79A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finP : ltac2:(tb__ "0|0|
S0ScS8S4S9cA1S6eS8cA3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finP : ltac2:(tb__ "0|0|
S0ScS66S8cS37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0P : ltac2:(tb__ "0|0|
S0S17S65S8cS42A2S1aZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2P : ltac2:(tb__ "0|0|
S0S17S65S8cS49A2S5cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3P : ltac2:(tb__ "0|0|
S0S17S65S8cS4dA2S1dSa9ScdS1aN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlP : ltac2:(tb__ "0|0|
S0ScS1fS3S3dS2bS2fA1S3bS4S75A1S73A2A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlP : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S3bS4S75A1S73A2M4A1S3S3dS2bS2fA1G4A2A1A2S10G3S12G1G2SdG0A1SaS18S52SaS18S53SdS18A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlP : ltac2:(tb__ "0|1|
S0ScS64S19S3S3dS2bS2fA1S3bS4S75A1S73A2M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjP : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413ccSdS2aA1A3S3dS2bS2fA1S3bS4S75A1S73A2A2SbA5S10G0SaS5S84SdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjP__R <: R_fjP__R = Some [r_jP_0]). Qed.
Lemma LN_fxlP : ltac2:(tb__ "0|0|
S0ScS1eS3S3dS2bS2fA1S3bS4S75A1S73A2A2A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlP : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S3dS2bS2fA1S3bS4S75A1S73A2A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillP_i : ltac2:(tb__ "0|0|
Sf5S31Sb2S4S79A1S4S84A1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0P r_lP_0 r_lP_1 nobFP s_fbkP SK_lP XX_lP (inclb_incl _ _ XF_lPb) NX_lP W_l1P R_l1P LN_l1P
           OB_fbP OB_fxP ENT_fbkP SID_fbkP S_bk0P S_bk2P S_bk3P (In_of_inclb _ _ FB_fbPb) (In_of_inclb _ _ FB_fxPb) e3r (la_state r_f_0) r_flP_0 r_jP_0 s_finP
           R_fhP LN_fhP NX_fhP ENT_finP SID_finP S_in0P S_in2P S_in3P W_xlP D_xlP NXe_xlP R_fjP LN_fxlP NX_fxlP r tp Q HC).
Qed.
Definition R_fhM__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41740SdS2aA1A3S4S7cA1SbA5").
Local Strategy expand [R_fhM__R].
Definition r_flM := Eval vm_compute in ((fun ro15__ : option (list leafA) => (match ro15__ with Some l => l | None => [] end)) R_fhM__R).
Definition r_flM_0 := Eval vm_compute in (nth 0 r_flM (mkLeafA (la_state r_h_0) RsCut)).
Definition cl0M := Eval vm_compute in (cL0 (factsQ e3r) (la_state r_flM_0)).
Definition R_l1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41740SaS2aZ4174cSdS2aA1A3A3S44S6dA1SbA5").
Local Strategy expand [R_l1M__R].
Definition r_lM := Eval vm_compute in ((fun ro14__ : option (list leafA) => (match ro14__ with Some l => l | None => [] end)) R_l1M__R).
Definition r_lM_0 := Eval vm_compute in (nth 0 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition r_lM_1 := Eval vm_compute in (nth 1 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition nobFM := Eval vm_compute in (length (ss_objs (ax_S cl0M))).
Definition s_fbkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lM_0) nobFM)) (ax_S cl0M)).
Definition s_finM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flM_0)) (ax_S cl0M)).
Definition R_fjM__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413ccSdS2aA1A3S3dS2bS2fA1S3bS4S74A1S72A2A2SbA5").
Local Strategy expand [R_fjM__R].
Definition r_jM := Eval vm_compute in ((fun ro16__ : option (list leafA) => (match ro16__ with Some l => l | None => [] end)) R_fjM__R).
Definition r_jM_0 := Eval vm_compute in (nth 0 r_jM (mkLeafA (cXL (factsQ e3r) (keepn (la_state r_lM_1) nobFM)) RsCut)).
Lemma SK_lM : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S6dA1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lM : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S6dA1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lMb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S6dA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lM : ltac2:(tb__ "0|0|
S0ScS64S19S3S6dA1A1S55A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1M : ltac2:(tb__ "0|0|
S0ScS1fS3S44S6dA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1M : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41740SaS2aZ4174cSdS2aA1A3A3S44S6dA1SbA5S10G0SaS5S8dSaS5S74SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1M__R <: R_l1M__R = Some [r_lM_0; r_lM_1]). Qed.
Lemma LN_l1M : ltac2:(tb__ "0|0|
S0ScS1eS3S44S6dA1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbM : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S8dA1A1A1M0S13S16Sb1S16S72G0A3SaS16SccSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxM : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S74A1A1A1M0S13S16Sb1S16S72G0A3SaS16SccSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkM : ltac2:(tb__ "0|0|
S0ScS8S3bS4S8dA1S72A2S6dS89A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkM : ltac2:(tb__ "0|0|
S0ScS66S89S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0M : ltac2:(tb__ "0|0|
S0S17S65S89S42A2S1dSa9S20S42A1S1aZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2M : ltac2:(tb__ "0|0|
S0S17S65S89S49A2S1dSa9S20S49A1S20Sb9A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3M : ltac2:(tb__ "0|0|
S0S17S65S89S4dA2S1dSa9ScdS1dSacS1dSadS20S42A1S1aZffffffffffffffffA1A3S1aZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbMb : ltac2:(tb__ "0|0|
S0ScS61SaS18ScbSdS18A1A3S1bS3S4S8dA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxMb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22ScbA1SdS18A1A3S1bS3S4S74A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhM : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41740SdS2aA1A3S4S7cA1SbA5S10G0SaS5S9bSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhM__R <: R_fhM__R = Some [r_flM_0]). Qed.
Lemma LN_fhM : ltac2:(tb__ "0|0|
S0ScS1eS3S4S7cA1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhM : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S4S7cA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finM : ltac2:(tb__ "0|0|
S0ScS8S4S9bA1S6dS8bA3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finM : ltac2:(tb__ "0|0|
S0ScS66S8bS37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0M : ltac2:(tb__ "0|0|
S0S17S65S8bS42A2S1aZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2M : ltac2:(tb__ "0|0|
S0S17S65S8bS49A2S5cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3M : ltac2:(tb__ "0|0|
S0S17S65S8bS4dA2S1dSa9ScdS1aN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlM : ltac2:(tb__ "0|0|
S0ScS1fS3S3dS2bS2fA1S3bS4S74A1S72A2A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlM : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S3bS4S74A1S72A2M4A1S3S3dS2bS2fA1G4A2A1A2S10G3S12G1G2SdG0A1SaS18S52SaS18S53SdS18A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlM : ltac2:(tb__ "0|1|
S0ScS64S19S3S3dS2bS2fA1S3bS4S74A1S72A2M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjM : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413ccSdS2aA1A3S3dS2bS2fA1S3bS4S74A1S72A2A2SbA5S10G0SaS5S83SdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjM__R <: R_fjM__R = Some [r_jM_0]). Qed.
Lemma LN_fxlM : ltac2:(tb__ "0|0|
S0ScS1eS3S3dS2bS2fA1S3bS4S74A1S72A2A2A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlM : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S3dS2bS2fA1S3bS4S74A1S72A2A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillM_i : ltac2:(tb__ "0|0|
Sf5S31Sb2S4S7cA1S4S83A1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0M r_lM_0 r_lM_1 nobFM s_fbkM SK_lM XX_lM (inclb_incl _ _ XF_lMb) NX_lM W_l1M R_l1M LN_l1M
           OB_fbM OB_fxM ENT_fbkM SID_fbkM S_bk0M S_bk2M S_bk3M (In_of_inclb _ _ FB_fbMb) (In_of_inclb _ _ FB_fxMb) e3r (la_state r_h_0) r_flM_0 r_jM_0 s_finM
           R_fhM LN_fhM NX_fhM ENT_finM SID_finM S_in0M S_in2M S_in3M W_xlM D_xlM NXe_xlM R_fjM LN_fxlM NX_fxlM r tp Q HC).
Qed.
Definition R_t0P__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S4S84A1SbA5").
Local Strategy expand [R_t0P__R].
Definition r_t0P := Eval vm_compute in ((fun ro18__ : option (list leafA) => (match ro18__ with Some l => l | None => [] end)) R_t0P__R).
Definition r_t0P_0 := Eval vm_compute in (nth 0 r_t0P (mkLeafA (la_state r_jP_0) RsCut)).
Definition ct0P := Eval vm_compute in (cT0 (la_state r_t0P_0)).
Definition R_t1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S45S71A1SbA5").
Local Strategy expand [R_t1P__R].
Definition r_t1P := Eval vm_compute in ((fun ro17__ : option (list leafA) => (match ro17__ with Some l => l | None => [] end)) R_t1P__R).
Definition r_t1P_0 := Eval vm_compute in (nth 0 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition r_t1P_1 := Eval vm_compute in (nth 1 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition s_inP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0P_0)) (ax_S ct0P)).
Definition s_bkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1P_0) nob)) (ax_S ct0P)).
Lemma SK_tP : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S71A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tP : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S71A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tPb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S71A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tP : ltac2:(tb__ "0|0|
S0ScS64S19S3S71A1A1S56A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1P : ltac2:(tb__ "0|0|
S0ScS1fS3S45S71A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1P : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S45S71A1SbA5S10G0SaS5S90SaS5S98SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1P__R <: R_t1P__R = Some [r_t1P_0; r_t1P_1]). Qed.
Lemma LN_t1P : ltac2:(tb__ "0|0|
S0ScS1eS3S45S71A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bP : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S90A1A1A1M0S13S16Sb1S16S34G0A3SaS16ScfSaS16SceSdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xP : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S98A1A1A1M0S13S16Sb1S16S34G0A3SaS16ScfSaS16SceSdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkP : ltac2:(tb__ "0|0|
S0ScS8S3bS4S90A1S34A2S71S92A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkP : ltac2:(tb__ "0|0|
S0ScS66S92S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4P : ltac2:(tb__ "0|0|
S0S17S65S92S40A2S1dSa9S20S40A1S1aZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6P : ltac2:(tb__ "0|0|
S0S17S65S92S4aA2S1dSa9S20S4aA1S1aZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bPb : ltac2:(tb__ "0|0|
S0ScS61SaS18S23SaaS1dSa9S20S40A1S1aZ4A1A3Sd0A3SdS18A1A3S1bS3S4S90A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xPb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22S23SaaS1dSa9S20S40A1S1aZ4A1A3Sd0A3A1SdS18A1A3S1bS3S4S98A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0P : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S4S84A1SbA5S10G0SaS5S9eSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0P__R <: R_t0P__R = Some [r_t0P_0]). Qed.
Lemma LN_t0P : ltac2:(tb__ "0|0|
S0ScS1eS3S4S84A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0P : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S4S84A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inP : ltac2:(tb__ "0|0|
S0ScS8S4S9eA1S71S94A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inP : ltac2:(tb__ "0|0|
S0ScS66S94S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4P : ltac2:(tb__ "0|0|
S0S17S65S94S40A2S1dSa9SbaS1aZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6P : ltac2:(tb__ "0|0|
S0S17S65S94S4aA2Sf3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlP := Eval vm_compute in (keepn (la_state r_t1P_1) nob).
Definition R_9P__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ411c0SdS2aA1A3S96SbA5").
Local Strategy expand [R_9P__R].
Definition r_9P := Eval vm_compute in ((fun ro19__ : option (list leafA) => (match ro19__ with Some l => l | None => [] end)) R_9P__R).
Definition r_9P_0 := Eval vm_compute in (nth 0 r_9P (mkLeafA xlP RsCut)).
Definition cellsfP := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9P_0) icc))) O_ri)).
Definition y3P := Eval vm_compute in (swM (cE2 (cE1 (la_state r_9P_0) icc))).
Definition y4P := Eval vm_compute in (keepn y3P (nobj y3P - 1)).
Definition s_fP := Eval vm_compute in (infer_sub NXRC (ax_S y4P) (ax_S L_rf)).
Lemma R_9P : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ411c0SdS2aA1A3S96SbA5S10G0SaS5S6cSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9P__R <: R_9P__R = Some [r_9P_0]). Qed.
Lemma LN_9P : ltac2:(tb__ "0|0|
S0ScS1eS3S96A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9P : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S96A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_y1P : ltac2:(tb__ "0|0|
S0ScS1fS3S3aS4S6cA1S32A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_y1P : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S6cA1M4A1S3S3aG4S32A2A1A2S10G3S12G1G2SaG0S12S17S17S58S51A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_y1P : ltac2:(tb__ "0|1|
S0ScS64S19S3S3aS4S6cA1M0S32A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_y1P : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S3aS4S6cA1S32A2A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_y1P : ltac2:(tb__ "0|0|
S0S11S16A1SdcS16S1cS3S3aS4S6cA1S32A2A1A1S32A3S10S16S4eA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y1P : ltac2:(tb__ "0|2|
S0SeS16A1S1cS3S3aS4S6cA1S32A2M0A1A1M1S13S16Sb1S16Sb6S3eG0A1U2A2G1A3SaS16S3fSaS16SbeS9aA1SdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_y1P : ltac2:(tb__ "0|0|
S0ScS5aS9aSf0S5dSf1Sf2A5SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_y3P : ltac2:(tb__ "0|0|
S0ScSc2SbfS41S3aS4S6cA1S32A2A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_y3P : ltac2:(tb__ "0|0|
S0ScSdaU2S3eS41S3aS4S6cA1S32A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Y3_eqP : ltac2:(tb__ "0|0|
S0S7SbdS41S3aS4S6cA1S32A2A1A1Sa8A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma Y4_eqP : ltac2:(tb__ "0|1|
S0S7S3bSbdS41S3aS4S6cA1S32A2A1A1M0Sb6S3eG0A1U1A2A2Sa6A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y3P : ltac2:(tb__ "0|2|
S0SeS16A1S1cS3SbdS41S3aS4S6cA1S32A2A1A1M0A1A1M1S13S16Sb1S16Sb6S3eG0A1U1A2G1A3SaS16S4eSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fP : ltac2:(tb__ "0|0|
S0ScS8Sa6Se0Sa0A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fP : ltac2:(tb__ "0|0|
S0ScS66Sa0Se1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0P r_t1P_0 r_t1P_1 nob s_bkP
    SK_tP XX_tP (inclb_incl _ _ XF_tPb) NX_tP W_t1P R_t1P LN_t1P OB_bP OB_xP ENT_bkP SID_bkP S_bk4P S_bk6P (In_of_inclb _ _ FB_bPb) (In_of_inclb _ _ FB_xPb)
    (la_state r_jP_0) r_t0P_0 s_inP e_srcP R_t0P LN_t0P NX_t0P ENT_inP SID_inP S_in4P S_in6P.
Definition exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv :=
  exit_stepsQ A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE phX PHX HFILLX Hini e16P vMFA e32P e48P HRIv FUEL xlP icc LN_9P NX_9P r_9P_0 cellsfP
    R_9P W_y1P D_y1P NX_y1P XX_y1P IC_y1P OB_y1P RI_y1P ND_y3P NO_y3P OB_y3P.
Definition fin_P A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq HREB HZD HPOST :=
  fin_leaf A Kc rb tp0 md0 W0 UStopLe rho HE HKc phF HREB HZD TR KIT y4P s_fP ENT_fP SID_fP rhoQ tpQ JLq HPOST.
Definition R_t0M__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S4S83A1SbA5").
Local Strategy expand [R_t0M__R].
Definition r_t0M := Eval vm_compute in ((fun ro21__ : option (list leafA) => (match ro21__ with Some l => l | None => [] end)) R_t0M__R).
Definition r_t0M_0 := Eval vm_compute in (nth 0 r_t0M (mkLeafA (la_state r_jM_0) RsCut)).
Definition ct0M := Eval vm_compute in (cT0 (la_state r_t0M_0)).
Definition R_t1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S45S70A1SbA5").
Local Strategy expand [R_t1M__R].
Definition r_t1M := Eval vm_compute in ((fun ro20__ : option (list leafA) => (match ro20__ with Some l => l | None => [] end)) R_t1M__R).
Definition r_t1M_0 := Eval vm_compute in (nth 0 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition r_t1M_1 := Eval vm_compute in (nth 1 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition s_inM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0M_0)) (ax_S ct0M)).
Definition s_bkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1M_0) nob)) (ax_S ct0M)).
Lemma SK_tM : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S70A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tM : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S70A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tMb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S70A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tM : ltac2:(tb__ "0|0|
S0ScS64S19S3S70A1A1S56A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1M : ltac2:(tb__ "0|0|
S0ScS1fS3S45S70A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1M : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S45S70A1SbA5S10G0SaS5S8fSaS5S97SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1M__R <: R_t1M__R = Some [r_t1M_0; r_t1M_1]). Qed.
Lemma LN_t1M : ltac2:(tb__ "0|0|
S0ScS1eS3S45S70A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bM : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S8fA1A1A1M0S13S16Sb1S16S34G0A3SaS16ScfSaS16SceSdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xM : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S97A1A1A1M0S13S16Sb1S16S34G0A3SaS16ScfSaS16SceSdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkM : ltac2:(tb__ "0|0|
S0ScS8S3bS4S8fA1S34A2S70S91A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkM : ltac2:(tb__ "0|0|
S0ScS66S91S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4M : ltac2:(tb__ "0|0|
S0S17S65S91S40A2S1dSa9S20S40A1S1aZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6M : ltac2:(tb__ "0|0|
S0S17S65S91S4aA2S1dSa9S20S4aA1S1aZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bMb : ltac2:(tb__ "0|0|
S0ScS61SaS18S23SaaS1dSa9S20S40A1S1aZ4A1A3Sd0A3SdS18A1A3S1bS3S4S8fA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xMb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22S23SaaS1dSa9S20S40A1S1aZ4A1A3Sd0A3A1SdS18A1A3S1bS3S4S97A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0M : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S4S83A1SbA5S10G0SaS5S9dSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0M__R <: R_t0M__R = Some [r_t0M_0]). Qed.
Lemma LN_t0M : ltac2:(tb__ "0|0|
S0ScS1eS3S4S83A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0M : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S4S83A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inM : ltac2:(tb__ "0|0|
S0ScS8S4S9dA1S70S93A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inM : ltac2:(tb__ "0|0|
S0ScS66S93S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4M : ltac2:(tb__ "0|0|
S0S17S65S93S40A2S1dSa9SbaS1aZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6M : ltac2:(tb__ "0|0|
S0S17S65S93S4aA2Sf3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlM := Eval vm_compute in (keepn (la_state r_t1M_1) nob).
Definition R_9M__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ411c0SdS2aA1A3S95SbA5").
Local Strategy expand [R_9M__R].
Definition r_9M := Eval vm_compute in ((fun ro22__ : option (list leafA) => (match ro22__ with Some l => l | None => [] end)) R_9M__R).
Definition r_9M_0 := Eval vm_compute in (nth 0 r_9M (mkLeafA xlM RsCut)).
Definition cellsfM := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9M_0) icc))) O_ri)).
Definition y3M := Eval vm_compute in (swM (cE2 (cE1 (la_state r_9M_0) icc))).
Definition y4M := Eval vm_compute in (keepn y3M (nobj y3M - 1)).
Definition s_fM := Eval vm_compute in (infer_sub NXRC (ax_S y4M) (ax_S L_rf)).
Lemma R_9M : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ411c0SdS2aA1A3S95SbA5S10G0SaS5S6bSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9M__R <: R_9M__R = Some [r_9M_0]). Qed.
Lemma LN_9M : ltac2:(tb__ "0|0|
S0ScS1eS3S95A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9M : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S95A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_y1M : ltac2:(tb__ "0|0|
S0ScS1fS3S3aS4S6bA1S32A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_y1M : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S6bA1M4A1S3S3aG4S32A2A1A2S10G3S12G1G2SaG0S12S17S17S58S51A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_y1M : ltac2:(tb__ "0|1|
S0ScS64S19S3S3aS4S6bA1M0S32A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_y1M : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S3aS4S6bA1S32A2A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_y1M : ltac2:(tb__ "0|0|
S0S11S16A1SdcS16S1cS3S3aS4S6bA1S32A2A1A1S32A3S10S16S4eA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y1M : ltac2:(tb__ "0|2|
S0SeS16A1S1cS3S3aS4S6bA1S32A2M0A1A1M1S13S16Sb1S16Sb6S3eG0A1U2A2G1A3SaS16S3fSaS16SbeS99A1SdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_y1M : ltac2:(tb__ "0|0|
S0ScS5aS99Sf0Sf4Sf1Sf2A5SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_y3M : ltac2:(tb__ "0|0|
S0ScSc2SbfS41S3aS4S6bA1S32A2A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_y3M : ltac2:(tb__ "0|0|
S0ScSdaU2S3eS41S3aS4S6bA1S32A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Y3_eqM : ltac2:(tb__ "0|0|
S0S7SbdS41S3aS4S6bA1S32A2A1A1Sa7A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma Y4_eqM : ltac2:(tb__ "0|1|
S0S7S3bSbdS41S3aS4S6bA1S32A2A1A1M0Sb6S3eG0A1U1A2A2Sa5A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y3M : ltac2:(tb__ "0|2|
S0SeS16A1S1cS3SbdS41S3aS4S6bA1S32A2A1A1M0A1A1M1S13S16Sb1S16Sb6S3eG0A1U1A2G1A3SaS16S4eSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fM : ltac2:(tb__ "0|0|
S0ScS8Sa5Se0S9fA3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fM : ltac2:(tb__ "0|0|
S0ScS66S9fSe1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0M r_t1M_0 r_t1M_1 nob s_bkM
    SK_tM XX_tM (inclb_incl _ _ XF_tMb) NX_tM W_t1M R_t1M LN_t1M OB_bM OB_xM ENT_bkM SID_bkM S_bk4M S_bk6M (In_of_inclb _ _ FB_bMb) (In_of_inclb _ _ FB_xMb)
    (la_state r_jM_0) r_t0M_0 s_inM e_srcP R_t0M LN_t0M NX_t0M ENT_inM SID_inM S_in4M S_in6M.
Definition exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv :=
  exit_stepsQ A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE phX PHX HFILLX Hini e16P e24M e32P e48P HRIv FUEL xlM icc LN_9M NX_9M r_9M_0 cellsfM
    R_9M W_y1M D_y1M NX_y1M XX_y1M IC_y1M OB_y1M RI_y1M ND_y3M NO_y3M OB_y3M.
Definition fin_M A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq HREB HZD HPOST :=
  fin_leaf A Kc rb tp0 md0 W0 UStopLe rho HE HKc phF HREB HZD TR KIT y4M s_fM ENT_fM SID_fM rhoQ tpQ JLq HPOST.

Theorem refill_populate_i : ltac2:(tb__ "0|4|
S103Sb3S2aS25SeSffQ40M0A1A1M1SdfSdfOF_;F_;S101R5R1A2Sb4R6A1S0ScS104R8A1SbA3Se9S35Se3R6R5SaSfS7Se8A2M2S12S7Se8Se0Se2R9R8R7A3A4SdG2A1A3A5SdfSddS2eRbR8R7R1S31Sb2R8A7Sd5RcR9A2Sc3S2S0Sc3R1SfcA3S0Sc3R1Sf6A3A2SfeG0S27RcPcM3A2A2S2aSeaR1A1S2aSebR11R2A2S105S1S0Sc3R5Sf6A3S10dS107R1A1S10eZ4S10cS10fS15S2aS106R1A1A2A1Sc5R12RfA2A2A2A2A2S25G1SeSdeA1SddSc4R17R16R14R13RdSfbRaSc5R17R14A2S10aR7A1A3R4R3R2R1AaS102S10bR18R8A2R5R4R2A4F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;SddS25S0S2aRbSeaSfeG0S27RaG3A2A2A1A3S2eReRbRaR3S31Sb2RbA7RaS100S35Sc4RfReRcRbR4Sc6A6S4S33A1R3RbA5R6A2F_;F_;Fr';Fmd0;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;Fc0;FKc;FA;").
Proof.
  apply (refill_populate W0 UStopLe (la_state r_2_0) cp2c ru1 (la_state r_f_0) (la_state r_f_1) cfm rf1 (la_state r_h_0)
           (la_state r_jP_0) xlP y4P (la_state r_jM_0) xlM y4M head_i pieceU_i mid_i fm_i pieceF_i run_i fillP_i fillM_i).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq. exact (fin_P A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq. exact (fin_M A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq).
Qed.
End SpineMallocQp.

(* [comment removed for export] *)
Module RefillCQ0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "iff"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "phase"; "gh_new"; "JR"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "length"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "budget_bound"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15"; "phUF3"; "phFin"; "phU3"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "JLRf"; "JRf"; "L_rf"; "NXR"; "Pre_rf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7"; "popfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQi"; "W0"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQ14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.RebuildQN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.RebuildQQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.
Local Notation W0 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQi.W0.

Lemma hreb_Q : ltac2:(tb__ "0|2|
S1bS18SfS7S24Q40M0A1A1M1S0S8S1cR4A1S9A3S11S33R6R4R3R1S35S1aR4A7S34R7R5A2S4S2S0S4R1S23A3S0S4R1S21A3A2S25G0S10R8PcA2A2S3S31R1A1S3S32RcR2A2S1eS1S0S4R5S21A3S38S20R1A1S39Z4S36S3aSbS3S1fR1A1A2A1S5RdRbA2A2A2A2A2SfG1S7S12A1S11S6R12R11R10RfRdS22RaS5R12R10A2S2aR7A1A3R4R3R2R1AaS29S2bR13R8A2R5R4R2A4F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Hini md0 HE PF phX [-> | ->] nv c cs HB r tp' tr md HJ.
  - rewrite phQ_P in HJ. apply (refill_rebuild_Q A Kc rho tp md0 W0 UStopLe rho HE PF false Hini) with (tr := tr); [|exact HJ].
    split; [discriminate|]. intros HLT. apply HB in HLT. unfold phU3, phUF3 in HLT. discriminate HLT.
  - rewrite phQ_M in HJ. apply (refill_rebuild_Q A Kc rho tp md0 W0 UStopLe rho HE PF true Hini) with (tr := tr); [|exact HJ].
    split; [intros _; apply HB; reflexivity | reflexivity].
Qed.

Theorem refill_inited : ltac2:(tb__ "0|1|
S18S13S13OF_;F_;S28R2R1A2S19R3A1S1bS3S3SfS7S24Q40A1A1S37S1dR5A1S27A2S0S8S1cR6A1S9A3RaS26S17S2dR7RbR6R5A4S30R4R3A5S16S17S2fR4R3SaSeS14S15A2M0SdS14S15S2eS2cR7RbR6A3A4ScG0A1A3A5A2F_;F_;Ftp;Frho;Fnv0;Fc0;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  intros Kc TR KIT HKc A c0 nv0 rho tp HBUD Hini.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQi.refill_N_i A Kc c0 nv0 rho tp TR KIT HKc HBUD Hini).
  - intros md0 HE HNP r tp' tr md HJ. exact (refill_rebuild_N A Kc rho tp md0 W0 UStopLe rho HE Hini HNP r tp' tr md HJ).
  - intros md0 r' E0 HE. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.SpineMallocQp.refill_populate_i A Kc c0 rho tp TR KIT HKc Hini (hreb_Q A Kc rho tp Hini) md0 r' E0 HE).
Qed.
End RefillCQ0.

(* [comment removed for export] *)
Module SpineMallocQpu.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "entailsA"; "ax_X"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "ss_facts"; "ss_objs"; "SAlu"; "ss_lenient"; "swf"; "SVar"; "reg_sv"; "SPNot"; "SPBranch"; "sprop_below"; "valuation"; "SPUle"; "rw"; "ss_pc"; "sv_below"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "factsQ"; "BASEFq"; "BASEOq"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQiu"; "e3r"; "FUEL"; "W0"; "icc"; "r_2_0"; "nob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "cX"; "GR"; "beg1"; "beg2"; "cE1"; "keepn"; "cP2"; "cXL"; "nobj"; "O_pcm"; "PV4"; "cE2"; "LV0"; "O_ri"; "cL1"; "cT1"; "cD"; "cPa"; "cPb"; "LV2"; "PV6"; "rMS"; "sMS"; "LV3"; "O_pccK"; "vMU"; "cFm"; "vK"; "HINT_au"; "HINT_k"; "HINT_map"; "LNX"; "PNX"; "idx_rot"; "k_e"; "relM"; "ri_has"; "rotM"; "vAU"; "vMFA"; "F_new"; "vNEW"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.SpineMallocQpu"; "r_xF_0"; "r_xU_0"; "cmcF"; "cmcU"; "r_9M_0"; "r_9P_0"; "cl0M"; "cl0P"; "cp2c"; "ct0M"; "ct0P"; "nobFM"; "nobFP"; "r_lM_1"; "r_lP_1"; "r_p1_0"; "r_p1_1"; "r_d_0"; "r_f_0"; "cfm"; "r_f_1"; "r_h_0"; "r_mF_0"; "r_mU_0"; "rf1"; "ru1"; "dmF"; "dmU"; "r_jM_0"; "r_jP_0"; "r_p2a_0"; "r_p2a_1"; "r_p2b_0"; "r_p2b_1"; "s_fbkM"; "s_fbkP"; "s_finM"; "s_finP"; "r_lM_0"; "r_lP_0"; "r_t1M_0"; "r_t1P_0"; "s_bkM"; "s_bkP"; "s_inM"; "s_inP"; "xlM"; "xlP"; "r_t1M_1"; "r_t1P_1"; "cellsfM"; "cellsfP"; "r_flM_0"; "r_flP_0"; "r_t0M_0"; "r_t0P_0"; "s_fM"; "s_fP"; "sa0"; "sa1"; "sb0"; "sb1"; "y4M"; "y4P"; "y3M"; "y3P"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "instr"; "ALU_SLL"; "ALU_XOR"; "Ecall"; "BC_LTU"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4"; "swM"; "O_rif"; "idx_sw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "phase"; "JR"; "gh_new"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ10"; "cMr"; "a2_e"; "cMc";
"dMSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQ13"; "F_lt"; "O_fcell"; "faend_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7"; "F_mu0"; "F_hi"; "x19_e0"; "x19_e1"; "popfacts"; "size_e_hi"; "size_e_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ9"; "O_piece"; "O_shp"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "L_rf"; "NXRC"; "JLRf"; "NXR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQ12"; "F_geu"; "new_e"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQ14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15"; "fillT"; "phUF3"; "pieceT"; "fmT"; "headT"; "midT"; "phFin"; "phU3"; "runT"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP"; "PF"; "PU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQ12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQ13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQ14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQiu.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_p1__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ415c0SaS2aZ41600SdS2aA1A3A3S4S33A1SbA5").
Local Strategy expand [R_p1__R].
Definition r_p1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_p1__R).
Definition r_p1_0 := Eval vm_compute in (nth 0 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition r_p1_1 := Eval vm_compute in (nth 1 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition R_p2a__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41630SdS2aA1A3S47S2bS2fA1S4S76A1A2SbA5").
Local Strategy expand [R_p2a__R].
Definition r_p2a := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_p2a__R).
Definition r_p2a_0 := Eval vm_compute in (nth 0 r_p2a (mkLeafA (cPa (factsQ e3r) (la_state r_p1_0)) RsCut)).
Definition r_p2a_1 := Eval vm_compute in (nth 1 r_p2a (mkLeafA (cPa (factsQ e3r) (la_state r_p1_0)) RsCut)).
Definition R_p2b__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41630SdS2aA1A3S48S2bS2fA1S4S77A1A2SbA5").
Local Strategy expand [R_p2b__R].
Definition r_p2b := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_p2b__R).
Definition r_p2b_0 := Eval vm_compute in (nth 0 r_p2b (mkLeafA (cPb (factsQ e3r) (la_state r_p1_1)) RsCut)).
Definition r_p2b_1 := Eval vm_compute in (nth 1 r_p2b (mkLeafA (cPb (factsQ e3r) (la_state r_p1_1)) RsCut)).
Definition cp2c := Eval vm_compute in (cP2c (factsQ e3r) (la_state r_p2a_1)).
Lemma FP_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18S23SafS60S51A3SdS18A1A3S1bS3S4S33A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p1 : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ415c0SaS2aZ41600SdS2aA1A3A3S4S33A1SbA5S10G0SaS5S76SaS5S77SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p1__R <: R_p1__R = Some [r_p1_0; r_p1_1]). Qed.
Lemma LN_p1 : ltac2:(tb__ "0|0|
S0ScS1eS3S4S33A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p1 : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S4S33A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18Sd2SdS18A1A3S1bS3S4S76A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22Sd2A1SdS18A1A3S1bS3S4S77A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pa : ltac2:(tb__ "0|0|
S0ScS1fS3S47S2bS2fA1S4S76A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pa : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S76A1M4A1S3S47S2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd6S20Sb9A1A4SdG0A1A3SaS18S54SaS18S26S4fS1aZdffc0000A1A2SdS18A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pa : ltac2:(tb__ "0|1|
S0ScS64S19S3S47S2bS2fA1S4S76A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pb : ltac2:(tb__ "0|0|
S0ScS1fS3S48S2bS2fA1S4S77A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pb : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S77A1M4A1S3S48S2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd7S20Sb9A1A4SdG0A1A3SaS18S54SaS18S26S4fS1aZdffc0000A1A2SdS18A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pb : ltac2:(tb__ "0|1|
S0ScS64S19S3S48S2bS2fA1S4S77A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2a : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41630SdS2aA1A3S47S2bS2fA1S4S76A1A2SbA5S10G0SaS5S85SaS5S86SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2a__R <: R_p2a__R = Some [r_p2a_0; r_p2a_1]). Qed.
Lemma LN_p2a : ltac2:(tb__ "0|0|
S0ScS1eS3S47S2bS2fA1S4S76A1A2A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2a : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S47S2bS2fA1S4S76A1A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2b : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41630SdS2aA1A3S48S2bS2fA1S4S77A1A2SbA5S10G0SaS5S87SaS5S88SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2b__R <: R_p2b__R = Some [r_p2b_0; r_p2b_1]). Qed.
Lemma LN_p2b : ltac2:(tb__ "0|0|
S0ScS1eS3S48S2bS2fA1S4S77A1A2A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2b : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S48S2bS2fA1S4S77A1A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa0_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18Sd1SdS18A1A3S1bS3S4S85A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a0 : ltac2:(tb__ "0|0|
S0ScS1fS3S3cS2bS2fA1S4S85A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a0 : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S85A1M4A1S3S3cS2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd3S1aZ40000A1A4SaG0S12S17S17S1aZ0A1S4fA4SdG0A1A3A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a0 : ltac2:(tb__ "0|1|
S0ScS64S19S3S3cS2bS2fA1S4S85A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsQ e3r) (la_state r_p2a_0))) (ax_S cp2c)).
Lemma ENT_a0 : ltac2:(tb__ "0|0|
S0ScS8S3cS2bS2fA1S4S85A1A2S6fSa1A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a0 : ltac2:(tb__ "0|0|
S0ScS66Sa1S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa1_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22Sd1A1SdS18A1A3S1bS3S4S86A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a1 : ltac2:(tb__ "0|0|
S0ScS1fS3S3cS2bS2fA1S4S86A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a1 : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S86A1M4A1S3S3cS2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd4S1aZ40000A1A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a1 : ltac2:(tb__ "0|1|
S0ScS64S19S3S3cS2bS2fA1S4S86A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsQ e3r) (la_state r_p2a_1))) (ax_S cp2c)).
Lemma ENT_a1 : ltac2:(tb__ "0|0|
S0ScS8S3cS2bS2fA1S4S86A1A2S6fSa2A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a1 : ltac2:(tb__ "0|0|
S0ScS66Sa2S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb0_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18Sd1SdS18A1A3S1bS3S4S87A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0ScS1fS3S3cS2bS2fA1S4S87A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S87A1M4A1S3S3cS2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd3S1aZ40000A1A4SaG0S12S17S17S1aZ0A1S4fA4SdG0A1A3A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0ScS64S19S3S3cS2bS2fA1S4S87A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsQ e3r) (la_state r_p2b_0))) (ax_S cp2c)).
Lemma ENT_b0 : ltac2:(tb__ "0|0|
S0ScS8S3cS2bS2fA1S4S87A1A2S6fSa3A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b0 : ltac2:(tb__ "0|0|
S0ScS66Sa3S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb1_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22Sd1A1SdS18A1A3S1bS3S4S88A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0ScS1fS3S3cS2bS2fA1S4S88A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S88A1M4A1S3S3cS2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17Sd4S1aZ40000A1A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0ScS64S19S3S3cS2bS2fA1S4S88A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsQ e3r) (la_state r_p2b_1))) (ax_S cp2c)).
Lemma ENT_b1 : ltac2:(tb__ "0|0|
S0ScS8S3cS2bS2fA1S4S88A1A2S6fSa4A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b1 : ltac2:(tb__ "0|0|
S0ScS66Sa4S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma head_i : ltac2:(tb__ "0|0|
Sf9S31Sb2S4S33A1S6fA4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE HC.
  exact (populate_head A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE FUEL e3r (la_state r_2_0) r_p1_0 r_p1_1 r_p2a_0 r_p2a_1 r_p2b_0 r_p2b_1 cp2c sa0 sa1 sb0 sb1
           (In_of_inclb _ _ FP_inb) R_p1 LN_p1 NX_p1 (In_of_inclb _ _ Fa_inb) (In_of_inclb _ _ Fb_inb) W_pa D_pa NXe_pa W_pb D_pb NXe_pb R_p2a LN_p2a NX_p2a R_p2b LN_p2b NX_p2b
           (In_of_inclb _ _ Fa0_inb) (In_of_inclb _ _ Fa1_inb) (In_of_inclb _ _ Fb0_inb) (In_of_inclb _ _ Fb1_inb) W_a0 W_a1 W_b0 W_b1 D_a0 D_a1 D_b0 D_b1 NXe_a0 NXe_a1 NXe_b0 NXe_b1
           ENT_a0 ENT_a1 ENT_b0 ENT_b1 SID_a0 SID_a1 SID_b0 SID_b1 r tp Q HC).
Qed.
Definition R_xU__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ7050cSdS2aA1A3S6fSbA5").
Local Strategy expand [R_xU__R].
Definition r_xU := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_xU__R).
Definition r_xU_0 := Eval vm_compute in (nth 0 r_xU (mkLeafA cp2c RsCut)).
Definition R_mU__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZde378SdS2aA1A3SbbS36S4S68A1S38A2S38Z40000A3SbA5").
Local Strategy expand [R_mU__R].
Definition r_mU := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_mU__R).
Definition r_mU_0 := Eval vm_compute in (nth 0 r_mU (mkLeafA (commit_post (cX (la_state r_xU_0) beg1) beg1 262144) RsCut)).
Definition cmcU := Eval vm_compute in (cMc (la_state r_mU_0) beg1).
Lemma CMCU_eq : ltac2:(tb__ "0|0|
S0S7Sc9S4S7eA1S38A2S6aA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmU := Eval vm_compute in (dMSf cmcU).
Lemma DMU_eq : ltac2:(tb__ "0|0|
S0S7ScaS6aA1S82A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition ru1 := Eval vm_compute in (relM dmU).
Lemma RU1_eq : ltac2:(tb__ "0|0|
S0S7S59S82A1S80A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xU : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ7050cSdS2aA1A3S6fSbA5S10G0SaS5S68SdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xU__R <: R_xU__R = Some [r_xU_0]). Qed.
Lemma LN_xU : ltac2:(tb__ "0|0|
S0ScS1eS3S6fA1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xU : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S6fA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xU : ltac2:(tb__ "0|0|
S0ScS1fS3S36S4S68A1S38A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xU : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S68A1M4A1S3S36G4S38A2A1A2S10G3S12G1G2SaG0S12S17S17SecS38A1S38A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xU : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S36S4S68A1S38A2A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xUb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S36S4S68A1S38A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xU : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S36S4S68A1S38A2A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xU : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S36S4S68A1S38A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xU : ltac2:(tb__ "0|0|
S0S11SabA1Se5S35S28S3S36S4S68A1S38A2A1A1A2S10SabSaeA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1Z11A2S1aZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZaA2S38A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZbA2S1aZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZcA2S1aZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZdA2S1aZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZeA2S1aZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xU : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S68A1S38A2A1ZfA2S1aZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xU : ltac2:(tb__ "0|0|
S0ScS29S19S3S36S4S68A1S38A2A1A1S38A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mU : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZde378SdS2aA1A3SbbS36S4S68A1S38A2S38Z40000A3SbA5S10G0SaS5S7eSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mU__R <: R_mU__R = Some [r_mU_0]). Qed.
Lemma LN_mU : ltac2:(tb__ "0|0|
S0ScS1eS3SbbS36S4S68A1S38A2S38Z40000A3A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mU : ltac2:(tb__ "0|0|
S0ScS63S37S19S3SbbS36S4S68A1S38A2S38Z40000A3A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mU : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S4S7eA1A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SaS16Sd8S38A1SdS16A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mUb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S4S7eA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mU : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S4S7eA1A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrU : ltac2:(tb__ "0|0|
S0ScS1fS3Sc7S4S7eA1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrU : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S7eA1M4A1S3Sc7G4A1A1A2S10G3S12G1G2SaG0S12S17S17Sc8S38A1S1aZ8000A1A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcU : ltac2:(tb__ "0|0|
S0ScS1fS3S6aA1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msU : ltac2:(tb__ "0|1|
S0S11SeS16A1M0A1Se7S6aSc0S4cS6aA1A3S10G0S4bS6aA1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msU : ltac2:(tb__ "0|0|
S0ScSe6S6aSc0S4cS6aA1S4bS6aA1Sb0S5S7S4Sc1A4A5SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msU : ltac2:(tb__ "0|0|
S0ScS63Se4S19S3S6aA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msU : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S6aA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msU : ltac2:(tb__ "0|1|
S0ScSdbS18S24S19S3S6aA1M0A1A1S1bG0A1A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msU : ltac2:(tb__ "0|0|
S0ScSdbS18S24S19S3SbcS6aS4cS6aA1S4bS6aA1A3A1A1A1S1bS3S6aA1A1A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rU : ltac2:(tb__ "0|0|
S0ScSc2S57S82A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rUb : ltac2:(tb__ "0|0|
S0ScSdaU1S3eS82A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rU : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S5bS82A1A1A1M0S13S16Sb1S16Sb6S3eS82A1U2A2G0A3SaS16Sd8S38A1SaS16Sd9S38A1SdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceU_i : ltac2:(tb__ "0|0|
Sf7S31Sb2S109S38S6fS80A6").
Proof.
  rewrite <- RU1_eq, <- DMU_eq, <- CMCU_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PU beg1 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cp2c r_xU_0 r_mU_0
           R_xU LN_xU NX_xU W_xU D_xU SK_xU (inclb_incl _ _ XF_xUb) XX_xU NXc_xU IC_xU R17_xU R10_xU BEL_xU R11_xU R12_xU R13_xU R14_xU R15_xU
           R_mU LN_mU NX_mU SK_mU (inclb_incl _ _ XF_mUb) XX_mU W_mrU D_mrU _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCU_eq, ?DMU_eq; [exact W_mcU | exact E_msU | exact CHK_msU | exact NF_msU | exact NX_msU | exact FBC_msU | exact FBT_msU | exact ND_rU | apply Nat.leb_le; exact NO_rUb | exact OB_rU].
Qed.
Definition R_d__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ416f0SdS2aA1A3S80SbA5").
Local Strategy expand [R_d__R].
Definition r_d := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_d__R).
Definition r_d_0 := Eval vm_compute in (nth 0 r_d (mkLeafA ru1 RsCut)).
Definition R_f__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ3f270SaS2aZ4172cSdS2aA1A3A3S46S2bS2fA1S4S78A1A2SbA5").
Local Strategy expand [R_f__R].
Definition r_f := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_f__R).
Definition r_f_0 := Eval vm_compute in (nth 0 r_f (mkLeafA (cD (factsQ e3r) (la_state r_d_0)) RsCut)).
Definition r_f_1 := Eval vm_compute in (nth 1 r_f (mkLeafA (cD (factsQ e3r) (la_state r_d_0)) RsCut)).
Lemma R_d : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ416f0SdS2aA1A3S80SbA5S10G0SaS5S78SdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_d__R <: R_d__R = Some [r_d_0]). Qed.
Lemma LN_d : ltac2:(tb__ "0|0|
S0ScS1eS3S80A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_d : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S80A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_d : ltac2:(tb__ "0|0|
S0ScS1fS3S46S2bS2fA1S4S78A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_d : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S78A1M4A1S3S46S2bS2fA1G4A2A1A2S10G3S12G1G2SaG0S12S17S17SeeS5fA4SdG0A1A3S5eA4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_d : ltac2:(tb__ "0|1|
S0ScS64S19S3S46S2bS2fA1S4S78A1M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_f : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ3f270SaS2aZ4172cSdS2aA1A3A3S46S2bS2fA1S4S78A1A2SbA5S10G0SaS5S79SaS5S7bSdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_f__R <: R_f__R = Some [r_f_0; r_f_1]). Qed.
Lemma LN_f : ltac2:(tb__ "0|0|
S0ScS1eS3S46S2bS2fA1S4S78A1A2A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_f : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S46S2bS2fA1S4S78A1A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma F0_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18SedSdS18A1A3S1bS3S4S79A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fm_inb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22SedA1SdS18A1A3S1bS3S4S7bA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma mid_i : ltac2:(tb__ "0|0|
SfaS31Sb2S80S4S79A1S4S7bA1A5").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (populate_mid A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE PF ph FUEL e3r ru1 r_d_0 r_f_0 r_f_1 R_d LN_d NX_d W_d D_d NXe_d R_f LN_f NX_f (In_of_inclb _ _ F0_inb) (In_of_inclb _ _ Fm_inb) r tp Q).
Qed.
Definition cfm := Eval vm_compute in (cFm (la_state r_f_1)).
Lemma CFM_eq : ltac2:(tb__ "0|0|
S0S7S50S4S7bA1A1S7aA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0ScS1fS3S50S4S7bA1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S7bA1M4A1S3S50G4A1A1A2S10G3S12G1G2SaG0S12S17S17SefS1dSa9S5dS1aZ40000A1A3A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma fm_i : ltac2:(tb__ "0|0|
Sf8S31Sb2S4S7bA1S7aA4").
Proof.
  rewrite <- CFM_eq. intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (famap_restate A Kc rb tp0 md0 TR KIT W0 UStopLe rho HE PF (la_state r_f_1) W_fm D_fm ph r tp Q).
Qed.
Definition R_xF__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ7050cSdS2aA1A3S7aSbA5").
Local Strategy expand [R_xF__R].
Definition r_xF := Eval vm_compute in ((fun ro8__ : option (list leafA) => (match ro8__ with Some l => l | None => [] end)) R_xF__R).
Definition r_xF_0 := Eval vm_compute in (nth 0 r_xF (mkLeafA cfm RsCut)).
Definition R_mF__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZde378SdS2aA1A3SbbS36S4S67A1S39A2S39Z40000A3SbA5").
Local Strategy expand [R_mF__R].
Definition r_mF := Eval vm_compute in ((fun ro9__ : option (list leafA) => (match ro9__ with Some l => l | None => [] end)) R_mF__R).
Definition r_mF_0 := Eval vm_compute in (nth 0 r_mF (mkLeafA (commit_post (cX (la_state r_xF_0) beg2) beg2 262144) RsCut)).
Definition cmcF := Eval vm_compute in (cMc (la_state r_mF_0) beg2).
Lemma CMCF_eq : ltac2:(tb__ "0|0|
S0S7Sc9S4S7dA1S39A2S69A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmF := Eval vm_compute in (dMSf cmcF).
Lemma DMF_eq : ltac2:(tb__ "0|0|
S0S7ScaS69A1S81A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition rf1 := Eval vm_compute in (relM dmF).
Lemma RF1_eq : ltac2:(tb__ "0|0|
S0S7S59S81A1S7fA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xF : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ7050cSdS2aA1A3S7aSbA5S10G0SaS5S67SdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xF__R <: R_xF__R = Some [r_xF_0]). Qed.
Lemma LN_xF : ltac2:(tb__ "0|0|
S0ScS1eS3S7aA1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xF : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S7aA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xF : ltac2:(tb__ "0|0|
S0ScS1fS3S36S4S67A1S39A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xF : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S67A1M4A1S3S36G4S39A2A1A2S10G3S12G1G2SaG0S12S17S17SecS39A1S39A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xF : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S36S4S67A1S39A2A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xFb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S36S4S67A1S39A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xF : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S36S4S67A1S39A2A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xF : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S36S4S67A1S39A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xF : ltac2:(tb__ "0|0|
S0S11SabA1Se5S35S28S3S36S4S67A1S39A2A1A1A2S10SabSaeA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1Z11A2S1aZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZaA2S39A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZbA2S1aZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZcA2S1aZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZdA2S1aZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZeA2S1aZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xF : ltac2:(tb__ "0|0|
S0S17S21S3S36S4S67A1S39A2A1ZfA2S1aZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xF : ltac2:(tb__ "0|0|
S0ScS29S19S3S36S4S67A1S39A2A1A1S39A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mF : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZde378SdS2aA1A3SbbS36S4S67A1S39A2S39Z40000A3SbA5S10G0SaS5S7dSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mF__R <: R_mF__R = Some [r_mF_0]). Qed.
Lemma LN_mF : ltac2:(tb__ "0|0|
S0ScS1eS3SbbS36S4S67A1S39A2S39Z40000A3A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mF : ltac2:(tb__ "0|0|
S0ScS63S37S19S3SbbS36S4S67A1S39A2S39Z40000A3A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mF : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S4S7dA1A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SaS16Sd8S39A1SdS16A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mFb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S4S7dA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mF : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S4S7dA1A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrF : ltac2:(tb__ "0|0|
S0ScS1fS3Sc7S4S7dA1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrF : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S7dA1M4A1S3Sc7G4A1A1A2S10G3S12G1G2SaG0S12S17S17Sc8S39A1S1aZ8000A1A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcF : ltac2:(tb__ "0|0|
S0ScS1fS3S69A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msF : ltac2:(tb__ "0|1|
S0S11SeS16A1M0A1Se7S69Sc0S4cS69A1A3S10G0S4bS69A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msF : ltac2:(tb__ "0|0|
S0ScSe6S69Sc0S4cS69A1S4bS69A1Sb0S5S7S4Sc1A4A5SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msF : ltac2:(tb__ "0|0|
S0ScS63Se4S19S3S69A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msF : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S69A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msF : ltac2:(tb__ "0|1|
S0ScSdbS18S24S19S3S69A1M0A1A1S1bG0A1A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msF : ltac2:(tb__ "0|0|
S0ScSdbS18S24S19S3SbcS69S4cS69A1S4bS69A1A3A1A1A1S1bS3S69A1A1A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rF : ltac2:(tb__ "0|0|
S0ScSc2S57S81A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rFb : ltac2:(tb__ "0|0|
S0ScSdaU1S3eS81A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rF : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S5bS81A1A1A1M0S13S16Sb1S16Sb6S3eS81A1U2A2G0A3SaS16Sd8S39A1SaS16Sd9S39A1SdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceF_i : ltac2:(tb__ "0|0|
Sf7S31Sb2S108S39S7aS7fA6").
Proof.
  rewrite <- RF1_eq, <- DMF_eq, <- CMCF_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP.PF beg2 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cfm r_xF_0 r_mF_0
           R_xF LN_xF NX_xF W_xF D_xF SK_xF (inclb_incl _ _ XF_xFb) XX_xF NXc_xF IC_xF R17_xF R10_xF BEL_xF R11_xF R12_xF R13_xF R14_xF R15_xF
           R_mF LN_mF NX_mF SK_mF (inclb_incl _ _ XF_mFb) XX_mF W_mrF D_mrF _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCF_eq, ?DMF_eq; [exact W_mcF | exact E_msF | exact CHK_msF | exact NF_msF | exact NX_msF | exact FBC_msF | exact FBT_msF | exact ND_rF | apply Nat.leb_le; exact NO_rFb | exact OB_rF].
Qed.
Definition R_h__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ4172cSdS2aA1A3S7fSbA5").
Local Strategy expand [R_h__R].
Definition r_h := Eval vm_compute in ((fun ro10__ : option (list leafA) => (match ro10__ with Some l => l | None => [] end)) R_h__R).
Definition r_h_0 := Eval vm_compute in (nth 0 r_h (mkLeafA rf1 RsCut)).
Lemma R_h : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ4172cSdS2aA1A3S7fSbA5S10G0SaS5S7cSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_h__R <: R_h__R = Some [r_h_0]). Qed.
Lemma LN_h : ltac2:(tb__ "0|0|
S0ScS1eS3S7fA1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_h : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S7fA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run_i : ltac2:(tb__ "0|0|
SfdS7fS4S7cA1A2").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc ph r tp Q HC.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc FUEL [0x4172c] rf1 [r_h_0] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _. exact (HC r1).
Qed.
Definition R_fhP__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41740SdS2aA1A3S4S79A1SbA5").
Local Strategy expand [R_fhP__R].
Definition r_flP := Eval vm_compute in ((fun ro12__ : option (list leafA) => (match ro12__ with Some l => l | None => [] end)) R_fhP__R).
Definition r_flP_0 := Eval vm_compute in (nth 0 r_flP (mkLeafA (la_state r_f_0) RsCut)).
Definition cl0P := Eval vm_compute in (cL0 (factsQ e3r) (la_state r_flP_0)).
Definition R_l1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41740SaS2aZ4174cSdS2aA1A3A3S44S6eA1SbA5").
Local Strategy expand [R_l1P__R].
Definition r_lP := Eval vm_compute in ((fun ro11__ : option (list leafA) => (match ro11__ with Some l => l | None => [] end)) R_l1P__R).
Definition r_lP_0 := Eval vm_compute in (nth 0 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition r_lP_1 := Eval vm_compute in (nth 1 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition nobFP := Eval vm_compute in (length (ss_objs (ax_S cl0P))).
Definition s_fbkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lP_0) nobFP)) (ax_S cl0P)).
Definition s_finP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flP_0)) (ax_S cl0P)).
Definition R_fjP__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413ccSdS2aA1A3S3dS2bS2fA1S3bS4S75A1S73A2A2SbA5").
Local Strategy expand [R_fjP__R].
Definition r_jP := Eval vm_compute in ((fun ro13__ : option (list leafA) => (match ro13__ with Some l => l | None => [] end)) R_fjP__R).
Definition r_jP_0 := Eval vm_compute in (nth 0 r_jP (mkLeafA (cXL (factsQ e3r) (keepn (la_state r_lP_1) nobFP)) RsCut)).
Lemma SK_lP : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S6eA1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lP : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S6eA1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lPb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S6eA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lP : ltac2:(tb__ "0|0|
S0ScS64S19S3S6eA1A1S55A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1P : ltac2:(tb__ "0|0|
S0ScS1fS3S44S6eA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1P : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41740SaS2aZ4174cSdS2aA1A3A3S44S6eA1SbA5S10G0SaS5S8eSaS5S75SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1P__R <: R_l1P__R = Some [r_lP_0; r_lP_1]). Qed.
Lemma LN_l1P : ltac2:(tb__ "0|0|
S0ScS1eS3S44S6eA1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbP : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S8eA1A1A1M0S13S16Sb1S16S73G0A3SaS16SccSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxP : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S75A1A1A1M0S13S16Sb1S16S73G0A3SaS16SccSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkP : ltac2:(tb__ "0|0|
S0ScS8S3bS4S8eA1S73A2S6eS8aA3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkP : ltac2:(tb__ "0|0|
S0ScS66S8aS37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0P : ltac2:(tb__ "0|0|
S0S17S65S8aS42A2S1dSa9S20S42A1S1aZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2P : ltac2:(tb__ "0|0|
S0S17S65S8aS49A2S1dSa9S20S49A1S20Sb9A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3P : ltac2:(tb__ "0|0|
S0S17S65S8aS4dA2S1dSa9ScdS1dSacS1dSadS20S42A1S1aZffffffffffffffffA1A3S1aZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbPb : ltac2:(tb__ "0|0|
S0ScS61SaS18ScbSdS18A1A3S1bS3S4S8eA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxPb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22ScbA1SdS18A1A3S1bS3S4S75A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhP : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41740SdS2aA1A3S4S79A1SbA5S10G0SaS5S9cSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhP__R <: R_fhP__R = Some [r_flP_0]). Qed.
Lemma LN_fhP : ltac2:(tb__ "0|0|
S0ScS1eS3S4S79A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhP : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S4S79A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finP : ltac2:(tb__ "0|0|
S0ScS8S4S9cA1S6eS8cA3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finP : ltac2:(tb__ "0|0|
S0ScS66S8cS37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0P : ltac2:(tb__ "0|0|
S0S17S65S8cS42A2S1aZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2P : ltac2:(tb__ "0|0|
S0S17S65S8cS49A2S5cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3P : ltac2:(tb__ "0|0|
S0S17S65S8cS4dA2S1dSa9ScdS1aN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlP : ltac2:(tb__ "0|0|
S0ScS1fS3S3dS2bS2fA1S3bS4S75A1S73A2A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlP : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S3bS4S75A1S73A2M4A1S3S3dS2bS2fA1G4A2A1A2S10G3S12G1G2SdG0A1SaS18S52SaS18S53SdS18A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlP : ltac2:(tb__ "0|1|
S0ScS64S19S3S3dS2bS2fA1S3bS4S75A1S73A2M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjP : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413ccSdS2aA1A3S3dS2bS2fA1S3bS4S75A1S73A2A2SbA5S10G0SaS5S84SdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjP__R <: R_fjP__R = Some [r_jP_0]). Qed.
Lemma LN_fxlP : ltac2:(tb__ "0|0|
S0ScS1eS3S3dS2bS2fA1S3bS4S75A1S73A2A2A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlP : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S3dS2bS2fA1S3bS4S75A1S73A2A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillP_i : ltac2:(tb__ "0|0|
Sf5S31Sb2S4S79A1S4S84A1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0P r_lP_0 r_lP_1 nobFP s_fbkP SK_lP XX_lP (inclb_incl _ _ XF_lPb) NX_lP W_l1P R_l1P LN_l1P
           OB_fbP OB_fxP ENT_fbkP SID_fbkP S_bk0P S_bk2P S_bk3P (In_of_inclb _ _ FB_fbPb) (In_of_inclb _ _ FB_fxPb) e3r (la_state r_f_0) r_flP_0 r_jP_0 s_finP
           R_fhP LN_fhP NX_fhP ENT_finP SID_finP S_in0P S_in2P S_in3P W_xlP D_xlP NXe_xlP R_fjP LN_fxlP NX_fxlP r tp Q HC).
Qed.
Definition R_fhM__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41740SdS2aA1A3S4S7cA1SbA5").
Local Strategy expand [R_fhM__R].
Definition r_flM := Eval vm_compute in ((fun ro15__ : option (list leafA) => (match ro15__ with Some l => l | None => [] end)) R_fhM__R).
Definition r_flM_0 := Eval vm_compute in (nth 0 r_flM (mkLeafA (la_state r_h_0) RsCut)).
Definition cl0M := Eval vm_compute in (cL0 (factsQ e3r) (la_state r_flM_0)).
Definition R_l1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ41740SaS2aZ4174cSdS2aA1A3A3S44S6dA1SbA5").
Local Strategy expand [R_l1M__R].
Definition r_lM := Eval vm_compute in ((fun ro14__ : option (list leafA) => (match ro14__ with Some l => l | None => [] end)) R_l1M__R).
Definition r_lM_0 := Eval vm_compute in (nth 0 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition r_lM_1 := Eval vm_compute in (nth 1 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition nobFM := Eval vm_compute in (length (ss_objs (ax_S cl0M))).
Definition s_fbkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lM_0) nobFM)) (ax_S cl0M)).
Definition s_finM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flM_0)) (ax_S cl0M)).
Definition R_fjM__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413ccSdS2aA1A3S3dS2bS2fA1S3bS4S74A1S72A2A2SbA5").
Local Strategy expand [R_fjM__R].
Definition r_jM := Eval vm_compute in ((fun ro16__ : option (list leafA) => (match ro16__ with Some l => l | None => [] end)) R_fjM__R).
Definition r_jM_0 := Eval vm_compute in (nth 0 r_jM (mkLeafA (cXL (factsQ e3r) (keepn (la_state r_lM_1) nobFM)) RsCut)).
Lemma SK_lM : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S6dA1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lM : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S6dA1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lMb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S6dA1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lM : ltac2:(tb__ "0|0|
S0ScS64S19S3S6dA1A1S55A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1M : ltac2:(tb__ "0|0|
S0ScS1fS3S44S6dA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1M : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41740SaS2aZ4174cSdS2aA1A3A3S44S6dA1SbA5S10G0SaS5S8dSaS5S74SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1M__R <: R_l1M__R = Some [r_lM_0; r_lM_1]). Qed.
Lemma LN_l1M : ltac2:(tb__ "0|0|
S0ScS1eS3S44S6dA1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbM : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S8dA1A1A1M0S13S16Sb1S16S72G0A3SaS16SccSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxM : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S74A1A1A1M0S13S16Sb1S16S72G0A3SaS16SccSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkM : ltac2:(tb__ "0|0|
S0ScS8S3bS4S8dA1S72A2S6dS89A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkM : ltac2:(tb__ "0|0|
S0ScS66S89S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0M : ltac2:(tb__ "0|0|
S0S17S65S89S42A2S1dSa9S20S42A1S1aZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2M : ltac2:(tb__ "0|0|
S0S17S65S89S49A2S1dSa9S20S49A1S20Sb9A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3M : ltac2:(tb__ "0|0|
S0S17S65S89S4dA2S1dSa9ScdS1dSacS1dSadS20S42A1S1aZffffffffffffffffA1A3S1aZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbMb : ltac2:(tb__ "0|0|
S0ScS61SaS18ScbSdS18A1A3S1bS3S4S8dA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxMb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22ScbA1SdS18A1A3S1bS3S4S74A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhM : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ41740SdS2aA1A3S4S7cA1SbA5S10G0SaS5S9bSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhM__R <: R_fhM__R = Some [r_flM_0]). Qed.
Lemma LN_fhM : ltac2:(tb__ "0|0|
S0ScS1eS3S4S7cA1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhM : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S4S7cA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finM : ltac2:(tb__ "0|0|
S0ScS8S4S9bA1S6dS8bA3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finM : ltac2:(tb__ "0|0|
S0ScS66S8bS37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0M : ltac2:(tb__ "0|0|
S0S17S65S8bS42A2S1aZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2M : ltac2:(tb__ "0|0|
S0S17S65S8bS49A2S5cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3M : ltac2:(tb__ "0|0|
S0S17S65S8bS4dA2S1dSa9ScdS1aN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlM : ltac2:(tb__ "0|0|
S0ScS1fS3S3dS2bS2fA1S3bS4S74A1S72A2A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlM : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S3bS4S74A1S72A2M4A1S3S3dS2bS2fA1G4A2A1A2S10G3S12G1G2SdG0A1SaS18S52SaS18S53SdS18A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlM : ltac2:(tb__ "0|1|
S0ScS64S19S3S3dS2bS2fA1S3bS4S74A1S72A2M0A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjM : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413ccSdS2aA1A3S3dS2bS2fA1S3bS4S74A1S72A2A2SbA5S10G0SaS5S83SdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjM__R <: R_fjM__R = Some [r_jM_0]). Qed.
Lemma LN_fxlM : ltac2:(tb__ "0|0|
S0ScS1eS3S3dS2bS2fA1S3bS4S74A1S72A2A2A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlM : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S3dS2bS2fA1S3bS4S74A1S72A2A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillM_i : ltac2:(tb__ "0|0|
Sf5S31Sb2S4S7cA1S4S83A1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0M r_lM_0 r_lM_1 nobFM s_fbkM SK_lM XX_lM (inclb_incl _ _ XF_lMb) NX_lM W_l1M R_l1M LN_l1M
           OB_fbM OB_fxM ENT_fbkM SID_fbkM S_bk0M S_bk2M S_bk3M (In_of_inclb _ _ FB_fbMb) (In_of_inclb _ _ FB_fxMb) e3r (la_state r_h_0) r_flM_0 r_jM_0 s_finM
           R_fhM LN_fhM NX_fhM ENT_finM SID_finM S_in0M S_in2M S_in3M W_xlM D_xlM NXe_xlM R_fjM LN_fxlM NX_fxlM r tp Q HC).
Qed.
Definition R_t0P__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S4S84A1SbA5").
Local Strategy expand [R_t0P__R].
Definition r_t0P := Eval vm_compute in ((fun ro18__ : option (list leafA) => (match ro18__ with Some l => l | None => [] end)) R_t0P__R).
Definition r_t0P_0 := Eval vm_compute in (nth 0 r_t0P (mkLeafA (la_state r_jP_0) RsCut)).
Definition ct0P := Eval vm_compute in (cT0 (la_state r_t0P_0)).
Definition R_t1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S45S71A1SbA5").
Local Strategy expand [R_t1P__R].
Definition r_t1P := Eval vm_compute in ((fun ro17__ : option (list leafA) => (match ro17__ with Some l => l | None => [] end)) R_t1P__R).
Definition r_t1P_0 := Eval vm_compute in (nth 0 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition r_t1P_1 := Eval vm_compute in (nth 1 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition s_inP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0P_0)) (ax_S ct0P)).
Definition s_bkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1P_0) nob)) (ax_S ct0P)).
Lemma SK_tP : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S71A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tP : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S71A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tPb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S71A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tP : ltac2:(tb__ "0|0|
S0ScS64S19S3S71A1A1S56A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1P : ltac2:(tb__ "0|0|
S0ScS1fS3S45S71A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1P : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S45S71A1SbA5S10G0SaS5S90SaS5S98SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1P__R <: R_t1P__R = Some [r_t1P_0; r_t1P_1]). Qed.
Lemma LN_t1P : ltac2:(tb__ "0|0|
S0ScS1eS3S45S71A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bP : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S90A1A1A1M0S13S16Sb1S16S34G0A3SaS16ScfSaS16SceSdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xP : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S98A1A1A1M0S13S16Sb1S16S34G0A3SaS16ScfSaS16SceSdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkP : ltac2:(tb__ "0|0|
S0ScS8S3bS4S90A1S34A2S71S92A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkP : ltac2:(tb__ "0|0|
S0ScS66S92S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4P : ltac2:(tb__ "0|0|
S0S17S65S92S40A2S1dSa9S20S40A1S1aZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6P : ltac2:(tb__ "0|0|
S0S17S65S92S4aA2S1dSa9S20S4aA1S1aZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bPb : ltac2:(tb__ "0|0|
S0ScS61SaS18S23SaaS1dSa9S20S40A1S1aZ4A1A3Sd0A3SdS18A1A3S1bS3S4S90A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xPb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22S23SaaS1dSa9S20S40A1S1aZ4A1A3Sd0A3A1SdS18A1A3S1bS3S4S98A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0P : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S4S84A1SbA5S10G0SaS5S9eSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0P__R <: R_t0P__R = Some [r_t0P_0]). Qed.
Lemma LN_t0P : ltac2:(tb__ "0|0|
S0ScS1eS3S4S84A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0P : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S4S84A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inP : ltac2:(tb__ "0|0|
S0ScS8S4S9eA1S71S94A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inP : ltac2:(tb__ "0|0|
S0ScS66S94S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4P : ltac2:(tb__ "0|0|
S0S17S65S94S40A2S1dSa9SbaS1aZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6P : ltac2:(tb__ "0|0|
S0S17S65S94S4aA2Sf3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlP := Eval vm_compute in (keepn (la_state r_t1P_1) nob).
Definition R_9P__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ411c0SdS2aA1A3S96SbA5").
Local Strategy expand [R_9P__R].
Definition r_9P := Eval vm_compute in ((fun ro19__ : option (list leafA) => (match ro19__ with Some l => l | None => [] end)) R_9P__R).
Definition r_9P_0 := Eval vm_compute in (nth 0 r_9P (mkLeafA xlP RsCut)).
Definition cellsfP := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9P_0) icc))) O_ri)).
Definition y3P := Eval vm_compute in (swM (cE2 (cE1 (la_state r_9P_0) icc))).
Definition y4P := Eval vm_compute in (keepn y3P (nobj y3P - 1)).
Definition s_fP := Eval vm_compute in (infer_sub NXRC (ax_S y4P) (ax_S L_rf)).
Lemma R_9P : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ411c0SdS2aA1A3S96SbA5S10G0SaS5S6cSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9P__R <: R_9P__R = Some [r_9P_0]). Qed.
Lemma LN_9P : ltac2:(tb__ "0|0|
S0ScS1eS3S96A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9P : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S96A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_y1P : ltac2:(tb__ "0|0|
S0ScS1fS3S3aS4S6cA1S32A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_y1P : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S6cA1M4A1S3S3aG4S32A2A1A2S10G3S12G1G2SaG0S12S17S17S58S51A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_y1P : ltac2:(tb__ "0|1|
S0ScS64S19S3S3aS4S6cA1M0S32A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_y1P : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S3aS4S6cA1S32A2A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_y1P : ltac2:(tb__ "0|0|
S0S11S16A1SdcS16S1cS3S3aS4S6cA1S32A2A1A1S32A3S10S16S4eA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y1P : ltac2:(tb__ "0|2|
S0SeS16A1S1cS3S3aS4S6cA1S32A2M0A1A1M1S13S16Sb1S16Sb6S3eG0A1U2A2G1A3SaS16S3fSaS16SbeS9aA1SdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_y1P : ltac2:(tb__ "0|0|
S0ScS5aS9aSf0S5dSf1Sf2A5SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_y3P : ltac2:(tb__ "0|0|
S0ScSc2SbfS41S3aS4S6cA1S32A2A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_y3P : ltac2:(tb__ "0|0|
S0ScSdaU2S3eS41S3aS4S6cA1S32A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Y3_eqP : ltac2:(tb__ "0|0|
S0S7SbdS41S3aS4S6cA1S32A2A1A1Sa8A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma Y4_eqP : ltac2:(tb__ "0|1|
S0S7S3bSbdS41S3aS4S6cA1S32A2A1A1M0Sb6S3eG0A1U1A2A2Sa6A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y3P : ltac2:(tb__ "0|2|
S0SeS16A1S1cS3SbdS41S3aS4S6cA1S32A2A1A1M0A1A1M1S13S16Sb1S16Sb6S3eG0A1U1A2G1A3SaS16S4eSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fP : ltac2:(tb__ "0|0|
S0ScS8Sa6Se0Sa0A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fP : ltac2:(tb__ "0|0|
S0ScS66Sa0Se1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0P r_t1P_0 r_t1P_1 nob s_bkP
    SK_tP XX_tP (inclb_incl _ _ XF_tPb) NX_tP W_t1P R_t1P LN_t1P OB_bP OB_xP ENT_bkP SID_bkP S_bk4P S_bk6P (In_of_inclb _ _ FB_bPb) (In_of_inclb _ _ FB_xPb)
    (la_state r_jP_0) r_t0P_0 s_inP e_srcP R_t0P LN_t0P NX_t0P ENT_inP SID_inP S_in4P S_in6P.
Definition exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv :=
  exit_stepsQ A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE phX PHX HFILLX Hini e16P vMFA e32P e48P HRIv FUEL xlP icc LN_9P NX_9P r_9P_0 cellsfP
    R_9P W_y1P D_y1P NX_y1P XX_y1P IC_y1P OB_y1P RI_y1P ND_y3P NO_y3P OB_y3P.
Definition fin_P A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq HREB HZD HPOST :=
  fin_leaf A Kc rb tp0 md0 W0 UStopLe rho HE HKc phF HREB HZD TR KIT y4P s_fP ENT_fP SID_fP rhoQ tpQ JLq HPOST.
Definition R_t0M__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S4S83A1SbA5").
Local Strategy expand [R_t0M__R].
Definition r_t0M := Eval vm_compute in ((fun ro21__ : option (list leafA) => (match ro21__ with Some l => l | None => [] end)) R_t0M__R).
Definition r_t0M_0 := Eval vm_compute in (nth 0 r_t0M (mkLeafA (la_state r_jM_0) RsCut)).
Definition ct0M := Eval vm_compute in (cT0 (la_state r_t0M_0)).
Definition R_t1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S45S70A1SbA5").
Local Strategy expand [R_t1M__R].
Definition r_t1M := Eval vm_compute in ((fun ro20__ : option (list leafA) => (match ro20__ with Some l => l | None => [] end)) R_t1M__R).
Definition r_t1M_0 := Eval vm_compute in (nth 0 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition r_t1M_1 := Eval vm_compute in (nth 1 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition s_inM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0M_0)) (ax_S ct0M)).
Definition s_bkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1M_0) nob)) (ax_S ct0M)).
Lemma SK_tM : ltac2:(tb__ "0|1|
S0SeSfSfS17S17A2S17A2M0A1Sb0S16G0S62S1cS3S70A1A1A4Sb0S16G0S62S13S16S2dS31A1SaS16Sb7SaS16Sb8SaS16S3fSaS16S43SdS16A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tM : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S70A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tMb : ltac2:(tb__ "0|0|
S0ScS61S2cS31Sb2A2S1bS3S70A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tM : ltac2:(tb__ "0|0|
S0ScS64S19S3S70A1A1S56A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1M : ltac2:(tb__ "0|0|
S0ScS1fS3S45S70A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1M : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S45S70A1SbA5S10G0SaS5S8fSaS5S97SdS5A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1M__R <: R_t1M__R = Some [r_t1M_0; r_t1M_1]). Qed.
Lemma LN_t1M : ltac2:(tb__ "0|0|
S0ScS1eS3S45S70A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bM : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S8fA1A1A1M0S13S16Sb1S16S34G0A3SaS16ScfSaS16SceSdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xM : ltac2:(tb__ "0|1|
S0SeS16A1S1cS3S4S97A1A1A1M0S13S16Sb1S16S34G0A3SaS16ScfSaS16SceSdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkM : ltac2:(tb__ "0|0|
S0ScS8S3bS4S8fA1S34A2S70S91A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkM : ltac2:(tb__ "0|0|
S0ScS66S91S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4M : ltac2:(tb__ "0|0|
S0S17S65S91S40A2S1dSa9S20S40A1S1aZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6M : ltac2:(tb__ "0|0|
S0S17S65S91S4aA2S1dSa9S20S4aA1S1aZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bMb : ltac2:(tb__ "0|0|
S0ScS61SaS18S23SaaS1dSa9S20S40A1S1aZ4A1A3Sd0A3SdS18A1A3S1bS3S4S8fA1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xMb : ltac2:(tb__ "0|0|
S0ScS61SaS18S22S23SaaS1dSa9S20S40A1S1aZ4A1A3Sd0A3A1SdS18A1A3S1bS3S4S97A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0M : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ413dcSaS2aZ413f0SdS2aA1A3A3S4S83A1SbA5S10G0SaS5S9dSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0M__R <: R_t0M__R = Some [r_t0M_0]). Qed.
Lemma LN_t0M : ltac2:(tb__ "0|0|
S0ScS1eS3S4S83A1A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0M : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S4S83A1A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inM : ltac2:(tb__ "0|0|
S0ScS8S4S9dA1S70S93A3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inM : ltac2:(tb__ "0|0|
S0ScS66S93S37A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4M : ltac2:(tb__ "0|0|
S0S17S65S93S40A2S1dSa9SbaS1aZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6M : ltac2:(tb__ "0|0|
S0S17S65S93S4aA2Sf3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlM := Eval vm_compute in (keepn (la_state r_t1M_1) nob).
Definition R_9M__R : option (list leafA) := ltac2:(tb__ "0|0|
S6S35S30SaS2aZ411c0SdS2aA1A3S95SbA5").
Local Strategy expand [R_9M__R].
Definition r_9M := Eval vm_compute in ((fun ro22__ : option (list leafA) => (match ro22__ with Some l => l | None => [] end)) R_9M__R).
Definition r_9M_0 := Eval vm_compute in (nth 0 r_9M (mkLeafA xlM RsCut)).
Definition cellsfM := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9M_0) icc))) O_ri)).
Definition y3M := Eval vm_compute in (swM (cE2 (cE1 (la_state r_9M_0) icc))).
Definition y4M := Eval vm_compute in (keepn y3M (nobj y3M - 1)).
Definition s_fM := Eval vm_compute in (infer_sub NXRC (ax_S y4M) (ax_S L_rf)).
Lemma R_9M : ltac2:(tb__ "0|1|
S0S11SeS5A1M0A1S6S35S30SaS2aZ411c0SdS2aA1A3S95SbA5S10G0SaS5S6bSdS5A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9M__R <: R_9M__R = Some [r_9M_0]). Qed.
Lemma LN_9M : ltac2:(tb__ "0|0|
S0ScS1eS3S95A1A1S14A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9M : ltac2:(tb__ "0|0|
S0ScS63S37S19S3S95A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_y1M : ltac2:(tb__ "0|0|
S0ScS1fS3S3aS4S6bA1S32A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_y1M : ltac2:(tb__ "0|5|
S0S11SfSeSfS17S17A2M0A1M1SeS18A1M2A2M3A1Sb5S3S4S6bA1M4A1S3S3aG4S32A2A1A2S10G3S12G1G2SaG0S12S17S17S58S51A4SdG0A1A3SdS18A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_y1M : ltac2:(tb__ "0|1|
S0ScS64S19S3S3aS4S6bA1M0S32A2A1A1S19S3G0A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_y1M : ltac2:(tb__ "0|1|
S0SeSfS17S17A2M0A1S9S3aS4S6bA1S32A2A1SdG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_y1M : ltac2:(tb__ "0|0|
S0S11S16A1SdcS16S1cS3S3aS4S6bA1S32A2A1A1S32A3S10S16S4eA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y1M : ltac2:(tb__ "0|2|
S0SeS16A1S1cS3S3aS4S6bA1S32A2M0A1A1M1S13S16Sb1S16Sb6S3eG0A1U2A2G1A3SaS16S3fSaS16SbeS99A1SdS16A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_y1M : ltac2:(tb__ "0|0|
S0ScS5aS99Sf0Sf4Sf1Sf2A5SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_y3M : ltac2:(tb__ "0|0|
S0ScSc2SbfS41S3aS4S6bA1S32A2A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_y3M : ltac2:(tb__ "0|0|
S0ScSdaU2S3eS41S3aS4S6bA1S32A2A1A1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Y3_eqM : ltac2:(tb__ "0|0|
S0S7SbdS41S3aS4S6bA1S32A2A1A1Sa7A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma Y4_eqM : ltac2:(tb__ "0|1|
S0S7S3bSbdS41S3aS4S6bA1S32A2A1A1M0Sb6S3eG0A1U1A2A2Sa5A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y3M : ltac2:(tb__ "0|2|
S0SeS16A1S1cS3SbdS41S3aS4S6bA1S32A2A1A1M0A1A1M1S13S16Sb1S16Sb6S3eG0A1U1A2G1A3SaS16S4eSdS16A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fM : ltac2:(tb__ "0|0|
S0ScS8Sa5Se0S9fA3SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fM : ltac2:(tb__ "0|0|
S0ScS66S9fSe1A2SbA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0M r_t1M_0 r_t1M_1 nob s_bkM
    SK_tM XX_tM (inclb_incl _ _ XF_tMb) NX_tM W_t1M R_t1M LN_t1M OB_bM OB_xM ENT_bkM SID_bkM S_bk4M S_bk6M (In_of_inclb _ _ FB_bMb) (In_of_inclb _ _ FB_xMb)
    (la_state r_jM_0) r_t0M_0 s_inM e_srcP R_t0M LN_t0M NX_t0M ENT_inM SID_inM S_in4M S_in6M.
Definition exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv :=
  exit_stepsQ A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE phX PHX HFILLX Hini e16P e24M e32P e48P HRIv FUEL xlM icc LN_9M NX_9M r_9M_0 cellsfM
    R_9M W_y1M D_y1M NX_y1M XX_y1M IC_y1M OB_y1M RI_y1M ND_y3M NO_y3M OB_y3M.
Definition fin_M A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq HREB HZD HPOST :=
  fin_leaf A Kc rb tp0 md0 W0 UStopLe rho HE HKc phF HREB HZD TR KIT y4M s_fM ENT_fM SID_fM rhoQ tpQ JLq HPOST.

Theorem refill_populate_i : ltac2:(tb__ "0|4|
S103Sb3S2aS25SeSffQ40M0A1A1M1SdfSdfOF_;F_;S101R5R1A2Sb4R6A1S0ScS104R8A1SbA3Se9S35Se3R6R5SaSfS7Se8A2M2S12S7Se8Se0Se2R9R8R7A3A4SdG2A1A3A5SdfSddS2eRbR8R7R1S31Sb2R8A7Sd5RcR9A2Sc3S2S0Sc3R1SfcA3S0Sc3R1Sf6A3A2SfeG0S27RcPcM3A2A2S2aSeaR1A1S2aSebR11R2A2S105S1S0Sc3R5Sf6A3S10dS107R1A1S10eZ4S10cS10fS15S2aS106R1A1A2A1Sc5R12RfA2A2A2A2A2S25G1SeSdeA1SddSc4R17R16R14R13RdSfbRaSc5R17R14A2S10aR7A1A3R4R3R2R1AaS102S10bR18R8A2R5R4R2A4F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;SddS25S0S2aRbSeaSfeG0S27RaG3A2A2A1A3S2eReRbRaR3S31Sb2RbA7RaS100S35Sc4RfReRcRbR4Sc6A6S4S33A1R3RbA5R6A2F_;F_;Fr';Fmd0;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;Fc0;FKc;FA;").
Proof.
  apply (refill_populate W0 UStopLe (la_state r_2_0) cp2c ru1 (la_state r_f_0) (la_state r_f_1) cfm rf1 (la_state r_h_0)
           (la_state r_jP_0) xlP y4P (la_state r_jM_0) xlM y4M head_i pieceU_i mid_i fm_i pieceF_i run_i fillP_i fillM_i).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq. exact (fin_P A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq. exact (fin_M A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq).
Qed.
End SpineMallocQpu.

(* [comment removed for export] *)
Module RefillC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "pair"; "prod"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "JLRf"; "JRf"; "L_rf"; "NXR"; "Pre_rf"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQu"; "e3u"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQ14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.RebuildQN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.RebuildQQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.RefillCQ0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Theorem refill_inited_u : ltac2:(tb__ "0|1|
S11S1S1OF_;F_;S10R2R1A2S12R3A1S13S0S0SdS7S1cQ40A1A1S1bS14R5A1SfA2S1dSbS15R6A1ScA3RaSeS5S17R7RbR6R5A4S1eR4R3A5S4S5S19R4R3S6SaS2S3A2M0S9S2S3S18S16R7RbR6A3A4S8G0A1A3A5A2F_;F_;Ftp;Frho;Fnv0;Fc0;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  intros Kc TR KIT HKc A c0 nv0 rho tp HBUD Hini.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQiu.refill_N_i A Kc c0 nv0 rho tp TR KIT HKc HBUD Hini).
  - intros md0 HE HNP r tp' tr md HJ. exact (refill_rebuild_N A Kc rho tp md0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQiu.W0 UStopLe rho HE Hini HNP r tp' tr md HJ).
  - intros md0 r' E0 HE. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.SpineMallocQpu.refill_populate_i A Kc c0 rho tp TR KIT HKc Hini (hreb_Q A Kc rho tp Hini) md0 r' E0 HE).
Qed.

Theorem refill_all : ltac2:(tb__ "0|1|
S11S1S1OF_;F_;S10R2R1A2S12R3A1S13S0S0SdS7S1cQ40A1A1S1bS14R5A1SfA2R9SeS5S17R6RaR5R4A4S1aR3R2A5S4S5S19R3R2S6SaS2S3A2M0S9S2S3S18S16R6RaR5A3A4S8G0A1A3A5A2F_;Ftp;Frho;Fnv0;Fc0;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  intros Kc TR KIT HKc A c0 nv0 rho tp HBUD. destruct (aa_cache_inited A) eqn:Hini.
  - exact (refill_inited Kc TR KIT HKc A c0 nv0 rho tp HBUD Hini).
  - apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQu.refill_uninit_i A Kc c0 nv0 rho tp TR (trd_ok Kc TR KIT) HKc HBUD Hini).
    intros rX. exact (refill_inited_u Kc TR KIT HKc (initA A) c0 nv0 rX tp HBUD eq_refl).
Qed.

Theorem refill_contract_ok : refill_contract /\ refill_contractE.
Proof.
  split.
  - intros ok A Kc c nv rho tp HKc HF HP HBUD. exact (refill_all Kc (triple segs ok) (TRokD_triple Kc ok HF HP) HKc A c nv rho tp HBUD).
  - intros A Kc c nv rho tp HKc HBUD. exact (refill_all Kc (etriple segs) (TRokD_etriple Kc) HKc A c nv rho tp HBUD).
Qed.
End RefillC.

(* [comment removed for export] *)
Module F0A_refill.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "proj2"; "not"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rw"; "sv"; "SLit"; "SVar"; "sprop"; "sv_eqb"; "SAlu"; "valuation"; "ss_next"; "ss_facts"; "obj_range"; "rm"; "sprop_below"; "ss_objs"; "cell"; "ob_cells"; "sprop_eqb"; "sv_below"; "swf"; "DUnknown"; "ob_dflt"; "odefault"; "rl"; "soff"; "agree_below"; "enc_bytes"; "eval"; "holds"; "mkSS"; "smatch"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "true"; "andb"; "list"; "cons"; "pair"; "nil"; "nat"; "app"; "option"; "orb"; "Some"; "fst"; "snd"; "false"; "length"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "leb"; "div"; "sub"; "pow"; "of_nat"; "eqb"; "opp"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "in_ranges"; "rho_absorb"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "sobj_eqb"; "ax_X"; "cell_eqb"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Stdlib.Lists.List"; "forallb"; "In"; "existsb"; "filter"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_thread"; "qbatch"; "ag_ctx"; "ag_spacebeg"; "aa_q_thread"; "ag_stack_bottom"; "ag_stack_top"; "qb_addr"; "qb_items"; "qb_size"; "topG"; "aa_live"; "ag_dtls"; "ag_fsb"; "ageom"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "nocellsF"; "S_qc"; "S_hdr"; "NRTX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "L_rf"; "Pre_rf"; "JLRf"; "JRf"; "nv_q24"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill"; "LZS"; "NRC"; "NRR"; "c107"; "rr_clsb"; "rchkb"; "spec_rzb"; "K_st2"; "Prr"; "ax_carve"; "rchkb_sound"; "rpins"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "G0"; "RTC_A"; "cells_footb"; "rtc_cells_img"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "import_okPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "vmd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "chain_pre"; "free_depth"; "F_depth"; "Wcan"; "V_DEPTH"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_in_view"; "rd_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_CLS"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "coveredb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain";
"rq_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone"; "rng_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "lastq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.F0A_limbo"; "LZ0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineBatchCount"; "kQuarantineMin"; "kSpaceSize"; "Sh"; "IMG_HI"; "IMG_LO"; "kUserMapSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue"; "spec_range"; "spec_small"; "coverb"; "spec_covered"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "vCTX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "isnil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC"; "K_i1"; "K_i2"; "K_bhf"; "room24"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill.RF.SITE.AT"; "HA0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.F0A_rzone"; "RZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "O_blkN"; "O_sh"; "O_stT2"; "iam_base"; "shb"; "vN8"; "vN8g"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_geo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_pins"; "spec_on"; "sv_on"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "GEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill.RF.SITE"; "site_factsR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_skelC"; "HRF"; "HRFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "needs_populate"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.RefillC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ax.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_pins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.F0A_limbo OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.F0A_rzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_rcore OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_skelC.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition LZS : list sobj := ltac2:(tb__ "0|0|
S33S8S72S33S8S70Sc8A1S33S8S70Sc9A1S35S8A1A3A3A3").

Definition NRC (f : bool) : list carve_spec := ltac2:(tb__ "0|1|
S37S58S73S2eS32S58A1Lf;Vf;S33S58Sc4S35S58A1M0A3G0X2ex2A3").

Definition NRR (f : bool) (RR : list sobj) : list carve_spec := ltac2:(tb__ "0|0|
S5dS58S58S5cS8S54S59R1A1A1VRR;A3Lk;S7cVf;A1A3").
Definition rr_clsb (nW : nat) (f : bool) (RR : list sobj) (o : sobj) : bool := ltac2:(tb__ "0|1|
S39S39S39S5cS8S54Vo;A1SbaS58S8S59S7dVf;VRR;A2A4A3S5cS8S54S70Vo;A1M0A1S7bA3A2S54G0S71A2A2Sa9VnW;Vo;A2A2").

Definition c107 : cell := mkCell (SLit (-16)) 4 (SVar 107).

Definition Prr (f : bool) (i : positive) : bool :=
  existsb (Pos.eqb i) (([12; 136; 151; 152; 153; 154; 155]%positive : list positive) ++ (if f then ([122; 124; 125]%positive : list positive) else [])).
Lemma NRC_on : ltac2:(tb__ "0|0|
S2eS0S2eS5aS58Sd7S83R1A1A1S7cR1A1A3S30A3Ff;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NRC_small : ltac2:(tb__ "0|0|
S2eSb9S58Sb6S7cR1A1A3Ff;").
Proof.
  intros f. unfold NRC. apply Forall_app. split; [exact NRTX_small|]. destruct f; [|constructor].
  constructor; [|constructor]. unfold K_bhf, spec_small, cells_inside. split; [lia|]. split; [lia|]. split; [lia|]. repeat constructor; cbn; lia.
Qed.
Lemma NRC_coverb : ltac2:(tb__ "0|0|
S2eS0S2eS5aS58Sb7S7cR1A1A3S30A3Ff;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition spec_rzb (k : carve_spec) : bool := ltac2:(tb__ "0|6|
S2fS2fS2fSaS6A2M0S6A2M1S32S2fS2fS6S36A2SaA2A1M2A2S2eLk;Vk;G1G2G1S2eLp;R2G0S6G0S2eLp0;R2SaS6S39S39S39S31S31SeR2SbZ0M3A1A2S43Sb3R1A2A2S43R3Sb2A2A2S31S31S31SeR2SbfA2S43G3R1A2M4A2S43R3Z1000A2M5A2S39S43R3Z120A2S43Zad0R1A2A2A2A2S31S31SeR2Sc0A2G4A2G5A2A2S31S31SeR2ScbA2S48R1Zf2608A2A2S48R3Zf2610A2A2A2Llo;Lb;X2fx1Lhi;Lp0;X2fx1Ll;Lp;X2fx1").
Lemma NRTX_rzb : ltac2:(tb__ "0|0|
S0S2eS5aS58S81S73A3S30A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition K_st2 (eFR : sv) (j1 j2 : positive) : carve_spec := ltac2:(tb__ "0|4|
S34S2fS2fSaS6A2M0S6A2S32S2fS2fS6S36A2M1SaA2M2A1S34G0S6S34SaS6SbfZae8A4Zc60A4S33G2S34G1SaS34S6S36Zb10U8M3A4SfS5eVeFR;ScVj1;A1A3A4S33G2S34G1SaS34S6S36Zb08G3A4SfS5eScVj2;A1SbZ1A1A3A4S35G2A1A3A3A4").
Definition ax_carve (A : axst) (N : list carve_spec) (nx : positive) : axst := ltac2:(tb__ "0|0|
S52VA;A1S2dS57VA;S25S2aR1A1S2bR1A1S28R1A1S27R1A1S2cR1A1S37S8S16R1A1SbaS58S8S59VN;A4A3S12R1A1Vnx;S29R1A1A9A2TS;").

Definition rpins (f : bool) (A : AA) (p n : Z) (rho1 : valuation) : Prop := ltac2:(tb__ "0|4|
S5fVA;A1S6eS1S0S4bQ40M0A1M1S9Vrho1;PcA2S4aG0Vp;A2A3S1S0G1S9Vrho1;PdA2S4aG0Vn;A2A3S1S0G1S9Vrho1;P69A2S4aG0S79Vn;A1M2A2A3S1S0G1S9Vrho1;P6aA2S4aG0S44G2Z8A2A2A3S1S0S6S42S4cG0S9Vrho1;P6bA2A2Z100A2Z3A3S1S0G1S9Vrho1;P88A2S4aG0SafA2A3S1S0G1S9Vrho1;P97A2S4aG0S60R1A1A2A3S1S0G1S9Vrho1;P98A2S4aG0S62R1A1A2A3S1S0G1S9Vrho1;P99A2S4aG0S66R1A1A2A3S1S0G1S9Vrho1;P9aA2S4aG0S65R1A1A2A3S1S0G1S9Vrho1;P9bA2S4aG0S63R1A1A2A3S0S2eVf;S30A3S1S4S0S32S61A1S64VA;A1S35S61A1A3A1S1S0S6S47S3eS2fS6S6A2S68SabVA;A1M3A1A2A1SaeA3S1S0G1S9Vrho1;P7aA2S4aG0S67G3A1A2A3S1S0G1S9Vrho1;P7cA2S4aG0Z0A2A3S0G1S9Vrho1;P7dA2S4aG0S69G3A1A2A3A2A2A2A2F_;A2A2A2A2A2A2A2A2A2A2A2TG;").

Definition rchkb (nW : nat) (f : bool) (EC T1 TR : axst) (sR : wsub) (RR : list sobj) (eFR : sv) : bool := ltac2:(tb__ "0|e|
S31Sc1S2fSaSaA2M0S55VEC;A1A2S31Sc1G0S55VTR;A1A2S31S8cS7aS11S52VEC;A1M1A1M2A2S31S5aSdS15G2A1S12G1A1M3A3S31S5aSdS15S11S52S8fVsR;S75S74VEC;VRR;A5A1A1A1G3A3S31SeS4eVsR;PaM4A2SfS5eScG4A1SbN8e0A1A3A2S31SeS4eVsR;PfM5A2SfS5eScG5A1SbZ8e0A1A3A2S31SeS4eVsR;P18M6A2ScG6A1A2S31SeS4eVsR;P97M7A2ScG7A1A2S31SeS4eVsR;P98M8A2ScG8A1A2S31SeS4eVsR;P9bM9A2ScG9A1MaA2S31SeS4eVsR;P9cA2SfS5eGaSbSb0A1A3A2S31SeS4eVsR;PcA2SbZ1f00A1A2S31SeS4eVsR;Sa5A2SbZ18A1A2S31SeS4eVsR;Sa6A2SbZ2000A1A2S31S5aS8S7fVnW;Vf;VRR;A3VRR;A3S31S5aS8SaaS7aA1VRR;A3S31S5aS8S8S5cS8S8S54S70R1A1MbR2A2Lo;VRR;A3Ls;S33S8S71S7bA3A3S31S5cS8S8S31S54GbS72A2S5cS17S56S7eA1S18R1A1A3A2Lo;VRR;A3S31S5aSdSdS5cSdS19R1A1G3A3Lg;S37SdS98S9bVnW;A1A1S9aS99A1A3A3S31S1bS52VTR;A1McA1S31S1aS11S52VT1;A1A1MdVeFR;A2S31S8cG2GdA2Sa8S12GcA1VRR;S16GcA1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Lemma rchkb_sound : ltac2:(tb__ "0|10|
S36S2eS53S53S53S51S32S8A1SaS0S2eS80R8R7R6R5R4R3R2R1A8S30A3S1S0S32S2fSaSaA2M0A1M1S55R7A1S35G0A1M2A3S1S0G1S55R5A1G2A3S1S0S2eS8cS7aS11S52R7A1M3A1M4A2S30A3S1S0S2eS5aSdS15G4A1S12G3A1M5A3S30A3S1S0S2eS5aSdS15S11S52S8fR4S75S74R7R3A5A1A1A1G5A3S30A3S1S0SaS4eR4PaM6A2SfS5eScG6A1SbN8e0A1A3A3S1S0SaS4eR4PfM7A2SfS5eScG7A1SbZ8e0A1A3A3S1S0SaS4eR4P18M8A2ScG8A1A3S1S0SaS4eR4P97M9A2ScG9A1A3S1S0SaS4eR4P98MaA2ScGaA1A3S1S0SaS4eR4P9bMbA2ScGbA1McA3S1S0SaS4eR4P9cA2SfS5eGcSbSb0A1A3A3S1S0SaS4eR4PcA2SbZ1f00A1A3S1S0SaS4eR4Sa5A2SbZ18A1A3S1S0SaS4eR4Sa6A2SbZ2000A1A3S1S0S2eS5aS8S7fR9R8R3A3R3A3S30A3S1S0S2eS5aS8SaaS7aA1R3A3S30A3S1S0S2eS5aS8S8S5cS8S8S54S70R1A1MdR2A2Lo;R4A3Ls;S33S8S71S7bA3A3S30A3S1S0S2eS5cS8S8S31S54GdS72A2S5cS17S56S7eA1S18R1A1A3A2Lo;R3A3S30A3S1S0S2eS5aSdSdS5cSdS19R1A1S12S52R8A1A1A3Lg;S37SdS98S9bR9A1A1S9aS99A1A3A3S30A3S1S0S2eS1bS52R5A1MeA1S30A3S1S0S2eS1aS11S52R6A1A1MfR2A2S30A3S1S0S2eS8cG4GfA2S30A3S0S2eSa8S12GeA1R3S16GeA1A3S30A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2F_;FeFR;FRR;FsR;FTR;FT1;FEC;Ff;FnW;").
Proof.
  intros nW f EC T1 TR sR RR eFR H. unfold rchkb in H.
  do 23 (apply andb_prop in H as [?X H]).
  repeat match goal with X : isnil _ = true |- _ => apply isnil_sound in X | X : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in X end.
  repeat split; assumption.
Qed.

Lemma RF_newo : ltac2:(tb__ "0|1|
S1S0S32S8A1Sd2S52S75A1S52S74A1A2S35S8A1A3S0S32S2fSaSaA2M0A1S55S74A1S35G0A1A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma inst_cells_rt : ltac2:(tb__ "0|0|
S6S2S1S3fZeddc0R1A2S41R1Zeddc4A2A2S1S3fZeddc8R1A2S41R1Zeddd1A2A2A2S0S2eS8aS8bS89S88A2R2A2S30A3F_;Fa;").
Proof.
  intros a [Ha|Ha].
  - apply (forall_rangeZ_ok (fun a0 => cells_footb (rtc_cells_img RTC_A RtCells.G0) a0) 0xeddc0 4); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia].
  - apply (forall_rangeZ_ok (fun a0 => cells_footb (rtc_cells_img RTC_A RtCells.G0) a0) 0xeddc8 9); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia].
Qed.
Lemma carve_rangeR : ltac2:(tb__ "0|0|
S10S58Sb6R1A1S0S2fS6S6A2S13R3S59R2A1A2Sb5R3R2A2A3F_;Fk;Frho;").
Proof. intros rho [[[b lo] hi] cs] (S1 & S2 & S3 & _). cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia. reflexivity. Qed.

Lemma civ_on : ltac2:(tb__ "0|4|
S7S2eF_;S10S10S4bQ40A1M0S38S4bQ8A1M1A1F_;S6S32S2fS2fS6S36A2M2SaA2M3A1S7S0S2eR7R1A1S30A3S0G0S9R6R2A2S9R7R2A2A3F_;Fi;S7S0S32G1A1S1fR6R1A2S1fR7R1A2A3Fl;S0S2eS5aG3G3G3S2eLc;R1G2SaG2S2eLp;R2S6S36Sd8RdR3A2Ln;Lz;X2fx1Le;Lp;X2fx1Lc;R3A3S30A3Sa3R8R6R5R4A4Sa3R8R7R6R5A4F_;F_;F_;F_;Fcs;Fb;Frdv;Fr2;Fr1;FP;").
Proof.
  intros P r1 r2 rdv b cs HW HL Hc C. unfold cells_in_view in *. apply Forall_forall. intros [[off k] v] Hin.
  pose proof (proj1 (Forall_forall _ _) C _ Hin) as X. cbn beta iota in X |- *.
  pose proof (proj1 (forallb_forall _ _) Hc _ Hin) as Hv. cbn beta iota in Hv. rewrite (eval_on P r1 r2 HW HL v Hv). exact X.
Qed.

Lemma enc_byte0 : ltac2:(tb__ "0|4|
S36S4bQ40M0A1ScfU0M1R2A2S0S4bQ8M2A1M3SbbG3G1S22R3R2A2S4aG2Z0A2A4S4aG2S4cG0R2A2A2A3F_;Fw;Fk;").
Proof. intros k w Hk. unfold enc_bytes. rewrite nth_Z_to_le_bytes by exact Hk. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity. Qed.
Lemma byte_ne2 : ltac2:(tb__ "0|1|
S6S0S6S42R1Z100A2Z3A3S4S0S4bQ8M0A1S4aG0R2A2S4aG0Z2A2A3A1F_;Fx;").
Proof.
  intros x Hx E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E.
  change (2 ^ Z.of_N 8) with 256 in E. rewrite Hx in E. discriminate E.
Qed.

Lemma add_fresh : ltac2:(tb__ "0|5|
S4bQ40M0A1M1S6S1S3fZ0R1A2S41R1S46Z2Z40A2M2A2A2S1S0G1SbeS5eR3S4aG0S42S45R2S4cG0R3A2A2G2A2A2M3A3S4aG0R2A2M4A3S0G1SbeS5eG3R3A3G4A3A2F_;Fv;Fe;").
Proof.
  intros e v Hv. pose proof (Z.mod_pos_bound (v - bv_unsigned e) (2 ^ 64) ltac:(lia)) as B.
  split; apply of_unsigned; rewrite add_val, u64_lit by exact B.
  - rewrite Zplus_mod_idemp_r. replace (bv_unsigned e + (v - bv_unsigned e)) with v by lia. apply Z.mod_small. exact Hv.
  - rewrite Zplus_mod_idemp_l. replace (v - bv_unsigned e + bv_unsigned e) with v by lia. apply Z.mod_small. exact Hv.
Qed.

Section RF.
Variable nW : nat. Variable f : bool.
Let st : ustop := UStopLe.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Variables (EC T0 T1 T2 TR : axst) (sR : wsub) (RR KEPT KEPT1 : list sobj) (XS : list axform) (eFR : sv).
Hypothesis HER : ltac2:(tb__ "0|1|
S0S38S32S8A1M0A1S92VEC;S75VsR;A3S3aG0VRR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S2eS91VEC;S75VsR;VRR;S33S53S74S35S53A1A3A5S30A3").
Hypothesis OBJS : ltac2:(tb__ "0|0|
S0S32S8A1S16S52VEC;A1A1S37S8VKEPT;VRR;A3A3").
Hypothesis HT0 : ltac2:(tb__ "0|0|
S0S53VT0;Sd3S8fVsR;S75S74VEC;VRR;A5S12S52VEC;A1A1A2A3").
Hypothesis HXS : ltac2:(tb__ "0|0|
S0S38S53A1Sd5VT0;VXS;A2S3aS53VT1;A2A3").
Hypothesis OBJS1 : ltac2:(tb__ "0|0|
S0S32S8A1S16S52VT1;A1A1S37S8VKEPT1;S33S8ScaS33S8S59Sc2A1S33S8S59Sc3A1S35S8A1A3A3A3A3A3").
Hypothesis HT2 : ltac2:(tb__ "0|0|
S0S53VT2;S57VT1;Sd0S52VT1;A1VKEPT1;A2A2A3").
Hypothesis HTR : ltac2:(tb__ "0|2|
S0S53VTR;S84VT2;S33S58S82VeFR;S11S52VT1;A1A1M0S8dG0A1M1A3S35S58A1A3S8dG1A1A3A3").
Hypothesis RCHK : ltac2:(tb__ "0|0|
S0S2eS80VnW;Vf;VEC;VT1;VTR;VsR;VRR;VeFR;A8S30A3").
Definition PARTS := rchkb_sound nW f EC T1 TR sR RR eFR RCHK.
Ltac parts := pose proof PARTS as (XXE & XTR & NXE & FBX & FBT & WG10 & WG15 & WG24 & WG151 & WG152 & WG155 & WG156 & WG12 & WGC & WGS
                                   & RROK & RRWF & RRSHP & RR107 & FCH & SWFT & EFRB & NX1 & RRcov).
Let REL : list sobj := ltac2:(tb__ "0|0|
S33S8ScaS33S8S59Sc2A1S33S8S59Sc3A1S35S8A1A3A3A3").

Section SITE.
Variables (A : AA) (Kc : KcA) (rho1 : valuation) (p n : Z) (l1 l2 : list (Z * Z)).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HLV : ltac2:(tb__ "0|1|
S0S32S2fS6S6A2M0A1S6bVA;A1S37G0Vl1;S33G0S34S6S6Vp;Vn;A4Vl2;A3A3A3").
Hypothesis HCLS : blk_cls p n.
Hypothesis Hii : aa_internal_inited A = true.
Hypothesis HC0 : cache24 A = [].
Hypothesis HPIN : ltac2:(tb__ "0|0|
S86Vf;VA;Vp;Vn;Vrho1;A5").
Hypothesis HBUD : budget_bound A <= LIMIT.
#[local] Abbreviation G := (aa_geom A).
#[local] Abbreviation T := (ag_thread (aa_geom A)).

Definition site_factsR (rhoE : valuation) : Prop := ltac2:(tb__ "0|1|
S1S21S7aVrho1;VrhoE;A3S1S1S3fS49S46Z2Z28A2A1S4dQ40S9VrhoE;S9cA2A2M0A2S3fG0S49S99A1A2A2Sb9SdS24VrhoE;A1S98VW;A1A3A2A2").
Lemma rf_facts : ltac2:(tb__ "0|0|
S10S32S4bQ40A1A1S94S9fVsegs;SadVnW;Vst;S3dVA;VKc;Vrho1;A6VEC;R3R2R1A6SdaR4A1F_;Fw;Ftp;FrhoE;").
Proof.
  intros rhoE tp w Hw. parts. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof (proj1 Hw) as (Hsm & _). unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (FIN : forall g, In g (chain_pre W ++ F_depth free_depth) -> holds rhoE g).
  { intros g Hg. pose proof (proj1 (forallb_forall _ _) FCH g Hg) as X. apply existsb_exists in X as (g' & Hg' & E). apply sprop_eqb_sound in E. subst g'.
    exact (proj1 (Forall_forall _ _) HFa g Hg'). }
  split; [exact Hag|]. split.
  - assert (D1 : holds rhoE (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply FIN; apply in_or_app; right; left; reflexivity).
    assert (D2 : holds rhoE (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply FIN; apply in_or_app; right; right; left; reflexivity).
    cbn [holds eval branch_taken] in D1, D2. unfold bv_lts in D1, D2. apply negb_true_iff in D1, D2. apply Z.ltb_ge in D1, D2.
    change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. change (bv_signed (Z_to_bv 64 (- 2 ^ 40))) with (- 2 ^ 40) in D2. lia.
  - apply Forall_forall. intros g Hg. apply FIN. apply in_or_app. left. exact Hg.
Qed.

Lemma HLin : ltac2:(tb__ "0|0|
S5bS2fS6S6A2S34S6S6Vp;Vn;A4S6bVA;A1A3").
Proof. rewrite HLV. apply in_or_app. right. left. reflexivity. Qed.

Section AT.
Variables (rhoE : valuation) (tp : list word) (tr0 : list event) (ms0 : machine_state) (md : Model).
Hypothesis SF : site_factsR rhoE.
Hypothesis Hsm0 : ltac2:(tb__ "0|0|
Sa2Vsegs;VrhoE;Vtp;VEC;S34S32S9dA1SbcVtr0;SbdVms0;Vmd;A2A4A5").
Hypothesis HJ0 : ltac2:(tb__ "0|0|
SadVnW;Vst;S3dVA;VKc;Vrho1;VrhoE;Vtp;Vtr0;Vmd;Aa").
Let rhoA : valuation := ltac2:(tb__ "0|0|
S50VrhoE;VRR;S96Vmd;Vtp;Vms0;A3A3").
Let rhoC : valuation := rho_sub rhoA sR.

Lemma HA0 : ltac2:(tb__ "0|0|
SddVsegs;VA;VrhoE;Vtp;Vmd;A5"). Proof. destruct HJ0 as [_ (H & _)]. exact H. Qed.
Lemma HG0 : geom_ok G. Proof. exact (proj1 HA0). Qed.
Definition HROOM0 : ltac2:(tb__ "0|2|
S0S2eSdfZ18M0Se1VA;G0A2M1A2S30A3S3fS40S6fG1A1Sb4A2SdeG0A1A2F_;") := ltac2:(tb__ "0|1|
Sc5VA;VrhoE;Vtp;Vmd;Z0M0Sc6G0VHC0;A8").
Lemma ERW : ltac2:(tb__ "0|0|
S7S8eR1S7aA2S0S4bQ40A1S9VrhoE;R2A2S9Vrho1;R2A2A3F_;Fi;").
Proof. intros i Hi. destruct SF as ((Hw & _) & _). symmetry. exact (Hw i Hi). Qed.
Lemma Hsm1 : ltac2:(tb__ "0|0|
S26Vsegs;VrhoE;S52VEC;A1S34S32S9dA1SbcVtr0;SbdS96Vmd;Vtp;Vms0;A3S97Vmd;A1A2A4A4").
Proof. pose proof (proj1 Hsm0) as X. unfold virt in X. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in X. exact X. Qed.
Lemma E12 : ltac2:(tb__ "0|1|
S0S4bQ40M0A1S9VrhoE;PcA2S4aG0Vp;A2A3"). Proof. rewrite ERW by (unfold GW; lia). exact (proj1 HPIN). Qed.
Lemma E105 : ltac2:(tb__ "0|1|
S0S4bQ40M0A1S9VrhoE;P69A2S4aG0S79Vn;A1A2A3"). Proof. rewrite ERW by (unfold GW; lia). exact (proj1 (proj2 (proj2 HPIN))). Qed.
Lemma E106 : ltac2:(tb__ "0|1|
S0S4bQ40M0A1S9VrhoE;P6aA2S4aG0S44S79Vn;A1Z8A2A2A3"). Proof. rewrite ERW by (unfold GW; lia). exact (proj1 (proj2 (proj2 (proj2 HPIN)))). Qed.
Lemma E107m : ltac2:(tb__ "0|0|
S0S6S42S4cQ40S9VrhoE;P6bA2A2Z100A2Z3A3"). Proof. rewrite ERW by (unfold GW; lia). exact (proj1 (proj2 (proj2 (proj2 (proj2 HPIN))))). Qed.
Lemma E136 : ltac2:(tb__ "0|1|
S0S4bQ40M0A1S9VrhoE;P88A2S4aG0SafA2A3"). Proof. rewrite ERW by (unfold GW; lia). exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HPIN)))))). Qed.
Lemma E151 : ltac2:(tb__ "0|1|
S0S4bQ40M0A1S9VrhoE;P97A2S4aG0S60S5fVA;A1A1A2A3"). Proof. rewrite ERW by (unfold GW; lia). exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPIN))))))). Qed.
Lemma E152 : ltac2:(tb__ "0|1|
S0S4bQ40M0A1S9VrhoE;P98A2S4aG0S62S5fVA;A1A1A2A3"). Proof. rewrite ERW by (unfold GW; lia). exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPIN)))))))). Qed.
Lemma E153 : ltac2:(tb__ "0|1|
S0S4bQ40M0A1S9VrhoE;P99A2S4aG0S66S5fVA;A1A1A2A3"). Proof. rewrite ERW by (unfold GW; lia). exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPIN))))))))). Qed.
Lemma E154 : ltac2:(tb__ "0|1|
S0S4bQ40M0A1S9VrhoE;P9aA2S4aG0S65S5fVA;A1A1A2A3"). Proof. rewrite ERW by (unfold GW; lia). exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPIN)))))))))). Qed.
Lemma E155 : ltac2:(tb__ "0|1|
S0S4bQ40M0A1S9VrhoE;P9bA2S4aG0S63S5fVA;A1A1A2A3"). Proof. rewrite ERW by (unfold GW; lia). exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPIN))))))))))). Qed.
Definition HPF := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPIN)))))))))).

Lemma BND : ltac2:(tb__ "0|3|
S1Sd6Vp;S79Vn;A1M0A2S1S0S6S42Vp;Z10A2Z0M1A3S1S3fZ1Vn;A2S1S41S40Vp;G0A2Z7fffff800000A2S1S3fVn;G0A2S1S3fZ8M2G0A2S1S0S6S42G0G2A2G1A3S41G0S40Vn;G2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (blkF_geom A rhoE tp md p n HA0 HLin HCLS) as (B1 & B2 & B3 & B4 & _ & _ & BN & _).
  pose proof (topG_range G) as TG. pose proof (N8_facts n B3) as (N1 & N2 & N3 & _).
  repeat split; try assumption; try lia.
Qed.
Definition GEO0 := F0A_rebuild.GEO A rhoE tp md 0 0 HA0.
Lemma TB : ltac2:(tb__ "0|2|
S1S3fZ1000M0S60S5fVA;A1A1M1A2S3fS40G1G0A2Z7fffff800000A2A2").
Proof. pose proof GEO0 as (T1' & T2' & _ & _ & _ & _ & _ & _ & _ & TG & _). clear -T1' T2' TG. lia. Qed.
Lemma E12u : ltac2:(tb__ "0|0|
S0S6S4cQ40S9VrhoE;PcA2A2Vp;A3").
Proof. pose proof BND as (B1 & _ & _ & B4 & _ & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. rewrite E12. apply u64_lit. lia. Qed.
Lemma Eshb : ltac2:(tb__ "0|0|
S0S6S4cQ40S23VrhoE;SccA2A2Sb1Vp;A1A3").
Proof.
  pose proof BND as (B1 & _ & _ & B4 & _ & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  cbn [eval shb]. rewrite E12, add_val, srl_val, !u64_lit by (unfold SHADOW_OFF; lia). change (3 mod 64) with 3.
  rewrite Z.shiftr_div_pow2 by lia. unfold Sh, SHADOW_OFF. pose proof (Z.div_lt_upper_bound p (2 ^ 3) (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos p (2 ^ 3) ltac:(lia) ltac:(lia)). rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma E105s : ltac2:(tb__ "0|0|
S0S6S20VrhoE;ScdA2S79Vn;A1A3").
Proof.
  pose proof BND as (B1 & _ & B3 & B4 & _ & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  apply soff_of_val; [cbn [eval vN8]; rewrite E105; apply u64_lit; lia | lia].
Qed.
Lemma E106s : ltac2:(tb__ "0|0|
S0S6S20VrhoE;SceA2S44S79Vn;A1Z8A2A3").
Proof.
  pose proof BND as (B1 & _ & B3 & B4 & _ & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  pose proof (Z.div_pos (N8 n) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (N8 n) 8 (N8 n) ltac:(lia) ltac:(lia)).
  apply soff_of_val; [cbn [eval vN8g]; rewrite E106; apply u64_lit; lia | lia].
Qed.
Lemma R_hdr : ltac2:(tb__ "0|0|
S0S2fS6S6A2S13VrhoE;S72A2S34S6S6S45Vp;Z10A2S45Vp;Z8A2A4A3").
Proof.
  pose proof BND as (B1 & _ & _ & B4 & _ & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  unfold S_hdr, nocellsF, O_hdr. cbn [ob_base ob_lo ob_hi ob_dflt ob_cells]. rewrite obj_range_mk by lia. cbn [eval]. rewrite E12, u64_lit by lia. f_equal; lia.
Qed.
Lemma R_blk : ltac2:(tb__ "0|0|
S0S2fS6S6A2S13VrhoE;S70Sc8A1A2S34S6S6Vp;S40Vp;S79Vn;A1A2A4A3").
Proof.
  pose proof BND as (B1 & B2 & B3 & B4 & B5 & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  unfold nocellsF, O_blkN, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval].
  rewrite E12, u64_lit, soff_lit_small, E105s by lia. f_equal; lia.
Qed.
Lemma R_sh : ltac2:(tb__ "0|1|
S0S2fS6S6A2S13VrhoE;S70Sc9A1A2S34S6S6Sb1Vp;A1M0S40G0S44S79Vn;A1Z8A2A2A4A3").
Proof.
  unfold nocellsF, O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Eshb, soff_lit_small, E106s by lia. f_equal; lia.
Qed.
Lemma R_qc : ltac2:(tb__ "0|1|
S0S2fS6S6A2S13VrhoE;S71A2S34S6S6S40S60S5fVA;A1A1M0Z50A2S40G0Z70A2A4A3").
Proof.
  pose proof TB as [TB1 TB2]. unfold S_qc. rewrite obj_range_mk by lia. cbn [eval cQ vT]. rewrite E151, add_val, !u64_lit by lia.
  rewrite Z.mod_small by lia. f_equal; lia.
Qed.

Lemma RR_class : ltac2:(tb__ "0|1|
S8S5bS8R1VRR;A3S2S5S58S58S1S5bS58R1S7dVf;VRR;A2A3S0S8R3S59R1A1A3A2Lk;A2S2S5bS8S70R2A1M0S7bA3S2S0S8G0S71A3S0S2eSa9VnW;R2A2S30A3A2A2A2F_;Fo;").
Proof.
  intros o Ho. parts. pose proof (proj1 (forallb_forall _ _) RROK o Ho) as X. unfold rr_clsb in X.
  apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]|]|].
  - left. apply existsb_exists in X as (o' & Hin & E). apply sobj_eqb_sound in E. subst o'. apply in_map_iff in Hin as (k & <- & Hk). exists k. split; [exact Hk | reflexivity].
  - right; left. apply existsb_exists in X as (s & Hin & E). apply sobj_eqb_sound in E. rewrite E. exact Hin.
  - right; right; left. apply sobj_eqb_sound in X. exact X.
  - right; right; right. exact X.
Qed.
Lemma NRR_in : ltac2:(tb__ "0|0|
S58S5bS58R1S7dVf;VRR;A2A3S1S5bS58R2S7cVf;A1A3S5bS8S59R2A1VRR;A3A2F_;Fk;").
Proof.
  intros k Hk. unfold NRR in Hk. apply filter_In in Hk as [Hk X]. split; [exact Hk|].
  apply existsb_exists in X as (o & Ho & E). apply sobj_eqb_sound in E. rewrite E. exact Ho.
Qed.
Lemma RR_shape : ltac2:(tb__ "0|0|
S8S5bS8R1S33S8S71S7bA3A3S5S8S8S1S5bS8R1VRR;A3S0S8S70R1A1R3A3A2Lo;A2F_;Fs;").
Proof. intros s Hs. parts. pose proof (proj1 (forallb_forall _ _) RRSHP s Hs) as X. apply existsb_exists in X as (o & Ho & E). apply sobj_eqb_sound in E. exists o. auto. Qed.

Lemma NKR : ltac2:(tb__ "0|4|
S58S5bS58R1S7dVf;VRR;A2A3S1S5bS8S59R2A1VRR;A3S1Sb6R2A1S1Sb8R2A1Sa3VrhoE;Sa4Vsegs;S14VrhoE;A1A2S45S3bS6S6Sb5VrhoE;R2A2A3S2fS2fS2fSaS6A2M0S6A2M1S32S2fS2fS6S36A2SaA2A1M2A2M3S6Lk;R2G1G2G1S6Lp0;R2G0S6G0S6Lp1;R2SaS6R1Llo;Ls;X2fx1Lz;Lp1;X2fx1Ll;Lp0;X2fx1A2G3G2Lk;R2G1G2G1G2Lp0;R2G0S6G0G2Lp1;R2SaS6R5Lz0;Ls;X2fx1Lz;Lp1;X2fx1Lcs;Lp0;X2fx1A4A2A2A2F_;Fk;").
Proof.
  intros k Hk0. destruct (NRR_in k Hk0) as [Hk HinR]. split; [exact HinR|]. split; [exact (proj1 (Forall_forall _ _) (NRC_small f) k Hk)|].
  split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) (NRC_coverb f) k Hk)|].
  destruct (blkF_mem A rhoE tp md p n HA0 HLin HCLS) as (t2 & T1' & T2' & HW2 & HL2 & _).
  destruct (junkF_ok A rhoE tp md HA0) as (jv2 & J1 & J2 & J3 & J4 & JM & JS & JQ).
  pose proof (carve_NRT A rhoE tp md p n HA0 HLin HCLS Hii E12u t2 (conj T1' (conj T2' (conj HW2 HL2))) jv2
                (conj J1 (conj J2 (conj J3 (conj J4 (conj JM (conj JS JQ))))))) as CN.
  set (rho2 := rhoF_of A rhoE p n t2 jv2) in CN.
  assert (EJ : j_min jv2 = kQuarantineMin).
  { pose proof HA0 as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _). destruct HQR as (_ & _ & _ & _ & _ & _ & QMIN & _).
    apply (cell8_inj (view segs (rm rhoE)) (QG + 72)); [exact JM | | clear -J1; lia | unfold kQuarantineMin; clear; lia].
    intros kk Hkk. specialize (QMIN kk Hkk). cbn [c_addr c_w c_val] in QMIN |- *. rewrite maskv_out in QMIN; [exact QMIN|].
    apply fs_footb_img; [exact HG | unfold QG; cbn in Hkk; clear -Hkk; lia]. }
  assert (CK : carve_ok rho2 k).
  { unfold NRC in Hk. apply in_app_or in Hk as [Hk|Hk]; [exact (proj1 (Forall_forall _ _) CN k (NRTX_sub k Hk))|].
    destruct (Bool.bool_dec f true) as [Ef|Ef]; [|apply not_true_is_false in Ef; rewrite Ef in Hk; destruct Hk]. destruct (HPF Ef) as (HNE & HKF & _).
    rewrite Ef in Hk. destruct Hk as [<-|[]].
    exact (carve_bhf A rhoE tp md p n HA0 HLin t2 (conj T1' (conj T2' (conj HW2 HL2))) jv2 (conj J1 (conj J2 (conj J3 (conj J4 (conj JM (conj JS JQ)))))) HNE HKF). }
  assert (HP : forall i, Prr f i = true -> rw rhoE i = rw rho2 i).
  { intros i Hi. unfold Prr in Hi. apply existsb_exists in Hi as (j & Hj & Eij). apply Pos.eqb_eq in Eij. subst j.
    apply in_app_or in Hj as [Hj|Hj].
    - destruct Hj as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; unfold rho2, rhoF_of; cbn [rho_sets rw rho_set_rw Pos.eqb];
        first [reflexivity | rewrite EJ; exact E136 | exact E151 | exact E152 | exact E153 | exact E154 | exact E155].
    - destruct (Bool.bool_dec f true) as [Ef|Ef]; [|apply not_true_is_false in Ef; rewrite Ef in Hj; destruct Hj]. destruct (HPF Ef) as (HNE & _ & P122 & P124 & P125).
      rewrite Ef in Hj.
      destruct Hj as [<-|[<-|[<-|[]]]]; rewrite ERW by (unfold GW; lia); unfold rho2, rhoF_of; cbn [rho_sets rw rho_set_rw Pos.eqb].
      + destruct (aa_q_thread A) eqn:EQ; [exfalso; exact (HNE eq_refl) | exact P122].
      + exact P124.
      + exact P125. }
  assert (CKE : carve_ok rhoE k).
  { apply (carve_ok_on (Prr f) rho2 rhoE HP); [intros l; unfold rho2, rhoF_of; rewrite rl_rho_sets; reflexivity | unfold rho2, rhoF_of; rewrite rm_rho_sets; reflexivity
      | exact (proj1 (forallb_forall _ _) (NRC_on f) k Hk) | exact CK]. }
  destruct k as [[[b lo] hi] cs]. unfold carve_ok in CKE. destruct CKE as (_ & _ & _ & _ & _ & _ & _ & CIV).
  cbn [spec_range fst]. replace (bv_unsigned (eval rhoE b) + lo - lo) with (bv_unsigned (eval rhoE b)) by lia. exact CIV.
Qed.

Lemma RR_top : ltac2:(tb__ "0|1|
S8S6S5bS8R2VRR;A3S0S2eSa9VnW;R3A2S30A3S1S3fS3bS6S6S13VrhoE;R4A2M0A3R3A2S41R3S3cS6S6G0A3A2A2S3fS6aS5fVA;A1A1R4A2F_;F_;F_;Fa;Fo;").
Proof.
  intros o a Ho Hok Ha. destruct SF as (_ & Hdep & Hch). destruct HJ0 as [_ (_ & _ & _ & _ & _ & _ & Htop)].
  exact (rq_top nW A rhoE o a Htop (proj2 Hdep) Hch Hok Ha).
Qed.
Lemma LZS_range : ltac2:(tb__ "0|1|
S8S5bS8S70R1A1S7bA3S6S1S3fS3bS6S6S13VrhoE;R3A2M0A3R1A2S41R1S3cS6S6G0A3A2A2SacVp;Vn;R2A3F_;Fa;F_;Fo;").
Proof.
  intros o Hs a Ha. rewrite <- nocells_range in Ha. unfold LZS in Hs. unfold LZ0.
  destruct Hs as [E|[E|[E|[]]]]; rewrite <- E in Ha; [rewrite R_hdr in Ha | rewrite R_blk in Ha | rewrite R_sh in Ha]; cbn [fst snd] in Ha; lia.
Qed.

Lemma VOC : ltac2:(tb__ "0|2|
S6S41R1S6aS5fVA;A1M0A1A2S4SacVp;Vn;R2A3A1S4S1S3fS40S60G0A1M1Z50A2R3A2S41R3S40G1Z70A2A2A2A1S0S38S4bQ8A1A1S87Vsegs;S14VrhoA;A1R4A3S87Vsegs;S14VrhoE;A1R4A3A3F_;F_;F_;Fz;").
Proof.
  intros z Hz HL HQ. destruct (Z_le_dec 0 z) as [Z0|NZ]; [destruct (Z_lt_dec z (2 ^ 64)) as [Z1|NZ]|].
  2,3: rewrite !view_out by (clear -NZ; lia); reflexivity.
  rewrite !view_in by (clear -Z0 Z1; lia).
  destruct (in_ranges_dec rhoE RR (Z_to_bv 64 z)) as [Hin|Hout].
  - destruct Hin as (o & Ho & Hr). rewrite u64_lit in Hr by (clear -Z0 Z1; lia).
    destruct (RR_class o Ho) as [(k & Hk & ->)|[Hs|[Hs|Hs]]].
    + rewrite (carve_rangeR rhoE k (proj1 (proj2 (NKR k Hk)))) in Hr. unfold rhoA.
      exact (absorb_specs_view rhoE _ tr0 (vms md tp ms0) (vmd md) KEPT RR (NRR f RR) (rd_of segs (rm rhoE)) Hsm1 OBJS NKR z k Hk Hr).
    + exfalso. exact (HL (LZS_range o Hs z Hr)).
    + exfalso. apply HQ. rewrite <- nocells_range, Hs, R_qc in Hr. exact Hr.
    + exfalso. pose proof (RR_top o z Ho Hs Hr) as X. clear -X Hz. lia.
  - unfold rhoA, rho_absorb, rd_of. cbn [rm]. destruct (in_ranges_dec rhoE RR (Z_to_bv 64 z)) as [Hin'|]; [exfalso; exact (Hout Hin') | reflexivity].
Qed.

Lemma AOR : ltac2:(tb__ "0|2|
S8S5bS8R1VRR;A3S0S1eS1dR2A1S1cA3S6S1S3fS3bS6S6S13VrhoE;R4A2M0A3R1A2S41R1S3cS6S6G0A3A2A2S5S4bQ8A1M1G1S0S38G1A1S87Vsegs;S14VrhoA;A1R3A3S3aG1R1A2A3Lx;A2F_;Fa;F_;F_;Fo;").
Proof.
  intros o Ho Do a Ha. destruct (absorb_obj rhoE _ tr0 (vms md tp ms0) (vmd md) KEPT RR o Hsm1 OBJS Ho) as (X1 & _ & X3 & _). cbn zeta in X1, X3.
  unfold obj_range in Ha. cbn [fst snd] in Ha.
  destruct (X3 (or_introl Do) (a - bv_unsigned (eval rhoE (ob_base o))) ltac:(clear -Ha; lia)) as [x Hx].
  exists x. unfold rhoA. rewrite view_in by (clear -Ha X1; lia).
  replace a with (bv_unsigned (eval rhoE (ob_base o)) + (a - bv_unsigned (eval rhoE (ob_base o)))) at 1 by (clear; lia). exact Hx.
Qed.
Lemma shape_dflt : ltac2:(tb__ "0|0|
S8S8S5bS8R1S33S8S71S7bA3A3S0S8S70R3A1R2A3S0S1eS1dR4A1S1cA3F_;F_;Fs;Fo;").
Proof. intros o s Hs E. assert (D : ob_dflt s = DUnknown) by (destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; reflexivity). rewrite <- E in D. destruct o; exact D. Qed.

Lemma PRESL : ltac2:(tb__ "0|1|
S6SacVp;Vn;R1A3S5S4bQ8A1M0G0S0S38G0A1S87Vsegs;S14VrhoA;A1R3A3S3aG0R1A2A3Lx;A2F_;Fz;").
Proof.
  intros z Hz.
  assert (IN : exists s, In s LZS /\ fst (obj_range rhoE s) <= z < snd (obj_range rhoE s)).
  { unfold LZ0 in Hz. destruct Hz as [Hz|[Hz|Hz]].
    - exists S_hdr. split; [left; reflexivity|]. rewrite R_hdr. exact Hz.
    - exists (nocellsF O_blkN). split; [right; left; reflexivity|]. rewrite R_blk. exact Hz.
    - exists (nocellsF O_sh). split; [right; right; left; reflexivity|]. rewrite R_sh. exact Hz. }
  destruct IN as (s & Hs & Hr). destruct (RR_shape s (or_intror Hs)) as (o & Ho & Es).
  apply (AOR o Ho (shape_dflt o s (or_intror Hs) Es) z). rewrite <- nocells_range, Es. exact Hr.
Qed.
Lemma PRESQ : ltac2:(tb__ "0|2|
S6S1S3fS40S60S5fVA;A1A1M0Z50A2R1A2S41R1S40G0Z70A2A2A2S5S4bQ8A1M1G1S0S38G1A1S87Vsegs;S14VrhoA;A1R3A3S3aG1R1A2A3Lx;A2F_;Fz;").
Proof.
  intros z Hz. destruct (RR_shape S_qc (or_introl eq_refl)) as (o & Ho & Es).
  apply (AOR o Ho (shape_dflt o S_qc (or_introl eq_refl) Es) z). rewrite <- nocells_range, Es, R_qc. exact Hz.
Qed.

Lemma HDR3 : ltac2:(tb__ "0|2|
S5S4bQ8M0A1M1G1S1S0S38G1A1S87Vsegs;S14VrhoA;A1S45Vp;Z10A2A3S3aG1R1A2A3S4S0G1R1S4aG0Z2A2A3A1A2Lx;A2").
Proof.
  parts. apply existsb_exists in RR107 as (o & Ho & E). apply andb_prop in E as [E1 E2]. apply sobj_eqb_sound in E1. apply In_of_cellb in E2.
  destruct (absorb_obj rhoE _ tr0 (vms md tp ms0) (vmd md) KEPT RR o Hsm1 OBJS Ho) as (X1 & X2 & _). cbn zeta in X1.
  destruct (X2 c107 E2) as (_ & _ & RD). specialize (RD 0%nat ltac:(cbn; lia)).
  assert (Eb : ob_base o = SVar 12) by (apply (f_equal ob_base) in E1; destruct o; exact E1). rewrite Eb in X1, RD.
  pose proof BND as (B1 & _ & _ & B4 & _ & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  cbn [c107 c_off c_width SymState.c_val eval] in RD. rewrite E12, u64_lit, soff_lit_small in RD by lia.
  replace (p + -16 + Z.of_nat 0) with (p - 16) in RD by (cbn; lia).
  eexists. split; [unfold rhoA; rewrite view_in by lia; exact RD|].
  rewrite enc_byte0 by (cbn; lia). apply byte_ne2. exact E107m.
Qed.

Lemma spec_rz : ltac2:(tb__ "0|1|
S58S0S2eS81R1A1S30A3S6S1S3fS3bS6S6Sb5VrhoE;R3A2M0A3R1A2S41R1S3cS6S6G0A3A2A2S4Sc7VA;R2A2A1F_;Fa;F_;Fk;").
Proof.
  intros [[[b lo] hi] cs] Hb a Ha. pose proof TB as [TB1 TB2].
  pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & _ & _ & _ & _ & _ & C1 & C2 & _).
  unfold spec_rzb in Hb. cbn [spec_range fst snd] in Ha.
  apply orb_prop in Hb as [Hb|Hb]; [apply orb_prop in Hb as [Hb|Hb]; [apply orb_prop in Hb as [Hb|Hb]|]|].
  - apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1]. apply sv_eqb_sound in H0. subst b. apply Z.leb_le in H1, H2.
    cbn [eval] in Ha. rewrite u64_lit in Ha by lia. apply (RZ_img A rhoE tp md HA0 HROOM0 a). clear -Ha H1 H2. lia.
  - apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1]. apply sv_eqb_sound in H0. subst b. apply Z.leb_le in H1, H2.
    cbn [eval vT] in Ha. rewrite E151, u64_lit in Ha by lia. apply (RZ_T A rhoE tp md HA0 HROOM0 a).
    apply orb_prop in H3 as [H3|H3]; apply Z.leb_le in H3; clear -Ha H1 H2 H3; lia.
  - apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1]. apply sv_eqb_sound in H0. subst b. apply Z.leb_le in H1, H2.
    cbn [eval vCTX] in Ha. rewrite E152, u64_lit in Ha by (clear -C1 C2 TG; lia). apply (RZ_ctx A rhoE tp md HA0 HROOM0 a). clear -Ha H1 H2. lia.
  - apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1]. apply sv_eqb_sound in H0. subst b. apply Z.eqb_eq in H1, H2. subst lo hi.
    pose proof BND as (B1 & _ & _ & B4 & _ & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
    unfold iam_base in Ha. cbn [eval] in Ha. rewrite sll_val, srl_val, E12, u64_lit in Ha by lia. change (32 mod 64) with 32 in Ha. change (3 mod 64) with 3 in Ha.
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 in Ha by lia.
    pose proof (Z.div_lt_upper_bound p (2 ^ 32) (2 ^ 15) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos p (2 ^ 32) ltac:(lia) ltac:(lia)).
    rewrite Z.mod_small in Ha by lia. apply (RZ_img A rhoE tp md HA0 HROOM0 a). unfold IMG_LO, IMG_HI. lia.
Qed.
Lemma RR_rz : ltac2:(tb__ "0|1|
S4bQ40M0A1S4fVrhoE;VRR;R1A3S4Sc7VA;S4cG0R2A2A2A1F_;Fa;").
Proof.
  intros a (o & Ho & Hr). destruct (RR_class o Ho) as [(k & Hk & ->)|[Hs|[Hs|Hs]]].
  - destruct (NRR_in k Hk) as [Hk' _]. rewrite (carve_rangeR rhoE k (proj1 (Forall_forall _ _) (NRC_small f) k Hk')) in Hr.
    unfold NRC in Hk'. apply in_app_or in Hk' as [Hk'|Hk'].
    + exact (spec_rz k (proj1 (forallb_forall _ _) NRTX_rzb k Hk') _ Hr).
    + destruct (Bool.bool_dec f true) as [Ef|Ef]; [|apply not_true_is_false in Ef; rewrite Ef in Hk'; destruct Hk']. destruct (HPF Ef) as (HNE & _ & P122 & _).
      rewrite Ef in Hk'. destruct Hk' as [<-|[]].
      apply (RZ_qfoot A rhoE tp md HA0 HROOM0). unfold q_foot. apply Exists_exists. exists (lastq A). split.
      * apply in_or_app. left. unfold lastq. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel.In_last. exact HNE.
      * left. cbn [K_bhf spec_range fst snd eval vQB] in Hr. rewrite ERW, P122 in Hr by (unfold GW; lia).
        pose proof (qF A rhoE tp md p n HA0 HLin) as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL). specialize (QL HNE).
        change (last (aa_q_thread A) qb_dflt) with (lastq A) in QL. destruct QL as (_ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _).
        pose proof GEO0 as (_ & _ & SB1 & SB2 & _ & _ & _ & _ & _ & TG & _). rewrite kSpaceSize_val in S2. unfold kQuarantineBatchSize in *.
        rewrite u64_lit in Hr by (clear -S1 S2 SB1 SB2 TG; lia). clear -Hr. lia.
  - apply (RZ_CZ A rhoE tp md HA0 HROOM0 p n l1 l2 HLV HCLS). pose proof (LZS_range o Hs _ Hr) as HZ.
    unfold F0A_rebuild.CZ. destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.F0A_limbo.LZ_cases A rhoE tp md p n l1 l2 HA0 HLV HCLS _ HZ) as [K|K]; [left | right]; exact K.
  - rewrite <- nocells_range, Hs, R_qc in Hr. cbn [fst snd] in Hr. apply (RZ_T A rhoE tp md HA0 HROOM0). left. clear -Hr. lia.
  - apply (RZ_top A rhoE tp md HA0 HROOM0). exact (RR_top o _ Ho Hs Hr).
Qed.

Lemma rf_entry : ltac2:(tb__ "0|0|
S77VA;VKc;Z18S78VrhoC;Vtp;Vtr0;Vmd;A8").
Proof.
  parts. pose proof HJ0 as [_ (HA & _ & _ & HK & Htp & _ & Htop)]. pose proof SF as (_ & Hdep & _). unfold free_depth in Hdep.
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range G) as TG.
  split.
  - split.
    + apply (refill_fwd A rhoE rhoC tp md p n l1 l2 HA HLV HCLS).
      * intros z Hz HL HQ. change (rm rhoC) with (rm rhoA). exact (VOC z Hz HL HQ).
      * intros z Hz. change (rm rhoC) with (rm rhoA). exact (PRESQ z Hz).
      * intros z Hz. change (rm rhoC) with (rm rhoA). exact (PRESL z Hz).
      * change (rm rhoC) with (rm rhoA). exact HDR3.
    + split; [exact HK|]. split; [|split].
      * unfold tp_ok in *. unfold rhoC. cbn [rw rho_sub]. rewrite WG24. unfold rhoA. cbn [eval rho_absorb rw]. exact Htp.
      * unfold top_high in *. unfold V_DEPTH in *. unfold rhoC. cbn [rw rho_sub]. rewrite WG10, WG15. unfold rhoA. rewrite !eval_absorb.
        assert (Em : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2272)))) = bv_unsigned (rw rhoE 10%positive) - 2272).
        { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2272))) with (2 ^ 64 - 2272) by reflexivity.
          rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
        rewrite Em. rewrite signed_add_lit by (cbn [eval]; lia). cbn [eval]. lia.
      * unfold rigidQ, rhoC. cbn [rw rho_sub]. rewrite WG151, WG152, WG155, WG156. unfold rhoA. cbn [eval rho_absorb rw].
        rewrite E151, E152, E155. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply add_lit.
  - destruct cls_of_q24 as [Q1 Q2]. unfold rfacts. cbn zeta. split; [exact Q1|]. split; [exact Q2|].
    unfold rhoC. cbn [rw rho_sub]. rewrite WG12, WGC, WGS. cbn [eval].
    split; [reflexivity|]. split; [reflexivity|]. split; [rewrite (proj1 c24_nums); reflexivity|].
    split; [exact HC0 | exact HROOM0].
Qed.

Lemma rf_exit_ok : ltac2:(tb__ "0|0|
S10S32S4bQ40A1A1S32S9dA1S9eS76VA;VKc;Z18VrhoC;Vtp;R4R3R2R1A9S93VrhoE;S96Vmd;Vtp;Vms0;A3VRR;VsR;S75S74VEC;R5A8F_;Fmd';Ftr';FtpL;FrhoL;").
Proof.
  intros rhoL tpL tr' md' (_ & HRM & _). parts. destruct RF_newo as [NEWO XPost].
  split; [split|split].
  - intros a Hin. apply HRM. exact (RR_rz a Hin).
  - intros o' oR Ho' HoR. rewrite NEWO in Ho'. destruct Ho'.
  - intros r a j oR Hr. rewrite XPost in Hr. destruct Hr.
  - intros r a j Hr. rewrite XXE in Hr. destruct Hr.
Qed.

Lemma rf_exit_core : ltac2:(tb__ "0|1|
S10S32S4bQ40A1A1S10S94Sd1VrhoE;S96Vmd;Vtp;Vms0;A3VRR;VsR;S52S75A1S52VEC;A1S52S74A1R2R4A9S9fVsegs;S90S76VA;VKc;Z18M0A3VrhoC;Vtp;R5R4A5S8fVsR;S75S74VEC;VRR;A5R3R4R2A6S5S10S10S5S10S10S1Se2Sa7VCST;VXGL;VA;A3Vrho1;R2A3S9fVsegs;SadVnW;Vst;S3dSe0VA;G0A2VKc;R2A6VTR;R1R7R5A6A2LrhoX;A2Lrho1'';A2F_;F_;Fw';Frho';FtpL;FrhoL;").
Proof.
  intros rhoL tpL rho' w' HLK [Hsm' HJ']. parts.
  pose proof SF as (Hag0 & Hdep & Hch). pose proof Hag0 as (Hagw & Hagl & Hagm).
  pose proof HJ0 as [_ (HA & HU0 & HL0 & HK0 & Htp0 & _ & Htop0)].
  destruct (entails_frA_sound segs EC Pre_rf sR RR rhoE tp tr0 ms0 md HER Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'. destruct HJ' as ((HQL & HKc2 & _) & HRM2 & HBD2 & _).
  pose proof HLK as (Hag' & Hrm' & _).
  pose proof TB as [TB1 TB2]. pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & TBAND & TI & _).
  set (JP := J_ofPA (JLRf A Kc 24) rhoC tp rhoL tpL) in *.
  assert (NXlt : forall i, (i < GW)%positive -> (i < ss_next (ax_S EC))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. apply Pos.leb_le. exact NXE. }
  assert (LT1 : forall i, (i < ss_next (ax_S EC))%positive -> (i < ss_next (ax_S T1))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. apply Pos.leb_le. exact NX1. }
  assert (AG' : forall i, (i < ss_next (ax_S EC))%positive -> rw rho' i = rw rhoE i) by (intros i Hi; symmetry; exact (proj1 Hag' i Hi)).
  assert (E151' : rw rho' 151%positive = Z_to_bv 64 T) by (rewrite AG' by (apply NXlt; unfold GW; lia); exact E151).

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S EC))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros g Hg.
    exact (proj1 (holds_agree_vals _ rhoE rho' g Hag' (proj1 (forallb_forall _ _) FBX g Hg)) (proj1 (Forall_forall _ _) Hfacts4 g Hg)). }
  assert (H0 : SPA segs JP T0 rho' tpL (tr2, mkCfg ms2 md2)).
  { rewrite HT0. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact FBT | intros _; exact HF4]. }

  pose proof (SPA_axforms segs JP XS rho' T0 T1 tpL _ HXS H0) as H1.
  pose proof (proj1 (proj1 H1)) as Hsm1v. unfold virt in Hsm1v. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm1v.
  pose proof (SPA_unobj segs JP rho' T1 KEPT1 REL tpL tr2 ms2 md2 OBJS1 H1 (fun k => k)) as H2. rewrite <- HT2 in H2.
  set (rho3 := rho_absorb rho' REL (vms md2 tpL ms2)) in *.
  assert (RM3 : forall a, rm rho3 a = if in_ranges_dec rho' REL a then ms_mem (vms md2 tpL ms2) a else rm rhoL a).
  { intros a. unfold rho3, rho_absorb. cbn [rm]. rewrite Hrm'. reflexivity. }
  assert (RREL : forall a : word, in_ranges rho' REL a ->
            (T + 2792 <= bv_unsigned a < T + 3168) \/ (0xeddc0 <= bv_unsigned a < 0xeddc4 \/ 0xeddc8 <= bv_unsigned a < 0xeddd1)).
  { intros a (o & Ho & Hr). destruct Ho as [<-|[<-|[<-|[]]]].
    - left. unfold O_stT2 in Hr. rewrite obj_range_mk in Hr by lia. cbn [eval vT fst snd] in Hr. rewrite E151', u64_lit in Hr by lia. exact Hr.
    - right; left. unfold K_i1, carve_obj, carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [eval fst snd] in Hr. rewrite u64_lit in Hr by lia. lia.
    - right; right. unfold K_i2, carve_obj, carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [eval fst snd] in Hr. rewrite u64_lit in Hr by lia. lia. }
  assert (PST : forall z, T + 2792 <= z < T + 3168 -> exists x, rd_of segs (rm rho3) (Z_to_bv 64 z) = Some x).
  { intros z Hz. destruct (absorb_obj rho' _ tr2 (vms md2 tpL ms2) (vmd md2) KEPT1 REL O_stT2 Hsm1v OBJS1 (or_introl eq_refl)) as (_ & _ & X3 & _). cbn zeta in X3.
    unfold O_stT2, obj_lo_of, obj_hi_of in X3. cbn [ob_base ob_dflt ob_lo ob_hi eval vT] in X3. rewrite !soff_lit_small in X3 by lia. rewrite E151', u64_lit in X3 by lia.
    destruct (X3 (or_introl eq_refl) (z - T) ltac:(lia)) as [x Hx]. exists x. replace (T + (z - T)) with z in Hx by lia. exact Hx. }

  assert (ICV : forall z, (0xeddc0 <= z < 0xeddc4 \/ 0xeddc8 <= z < 0xeddd1) -> rd_of segs (rm rho3) (Z_to_bv 64 z) = rd_of segs (rm rhoE) (Z_to_bv 64 z)).
  { destruct (blkF_mem A rhoE tp md p n HA0 HLin HCLS) as (t2 & T1' & T2' & HW2 & HL2 & _).
    destruct (junkF_ok A rhoE tp md HA0) as (jv2 & JV).
    pose proof (carve_inst A rhoE tp md p n HA0 t2 (conj T1' (conj T2' (conj HW2 HL2))) jv2) as CI. set (rho2 := rhoF_of A rhoE p n t2 jv2) in CI.
    assert (HW155 : forall i, Pos.eqb i 155 = true -> rw rho' i = rw rho2 i).
    { intros i Hi. apply Pos.eqb_eq in Hi. subst i. rewrite AG' by (apply NXlt; unfold GW; lia). unfold rho2, rhoF_of. cbn [rho_sets rw rho_set_rw Pos.eqb]. exact E155. }
    assert (HL' : forall l, rl rho' l = rl rho2 l) by (intros l; unfold rho2, rhoF_of; rewrite rl_rho_sets; symmetry; exact (proj2 Hag' l)).
    assert (NKI : forall k, In k [K_i1; K_i2] -> In (carve_obj k) REL /\ spec_small k /\ spec_covered k
              /\ cells_in_view rho' (rd_of segs (rm rhoE)) (fst (spec_range rho' k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs)).
    { intros k Hk. assert (CK : carve_ok rho2 k) by (destruct Hk as [<-|[<-|[]]]; [exact (proj1 CI) | exact (proj2 CI)]).
      assert (INR : In (carve_obj k) REL) by (destruct Hk as [<-|[<-|[]]]; [right; left; reflexivity | right; right; left; reflexivity]).
      assert (SM : spec_small k) by (destruct Hk as [<-|[<-|[]]]; unfold K_i1, K_i2, spec_small, cells_inside; (split; [lia|]; split; [lia|]; split; [lia|]; repeat constructor; cbn; lia)).
      assert (CV : spec_covered k) by (apply coverb_sound; destruct Hk as [<-|[<-|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      assert (ON : let '(_, _, _, cs) := k in forallb (fun c : Z * nat * sv => let '(_, _, e) := c in sv_on (fun i => Pos.eqb i 155) e) cs = true)
        by (destruct Hk as [<-|[<-|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      assert (EB : let '(b, _, _, _) := k in eval rho' b = eval rho2 b) by (destruct Hk as [<-|[<-|[]]]; reflexivity).
      split; [exact INR|]. split; [exact SM|]. split; [exact CV|].
      destruct k as [[[b lo] hi] cs]. unfold carve_ok in CK. destruct CK as (_ & _ & _ & _ & _ & _ & _ & CIV).
      cbn [spec_range fst]. replace (bv_unsigned (eval rho' b) + lo - lo) with (bv_unsigned (eval rho' b)) by lia. rewrite EB.
      unfold rho2, rhoF_of in CIV. rewrite rm_rho_sets in CIV. fold (rhoF_of A rhoE p n t2 jv2) in CIV. fold rho2 in CIV.
      exact (civ_on (fun i => Pos.eqb i 155) rho2 rho' _ _ cs HW155 HL' ON CIV). }
    intros z Hz. destruct Hz as [Hz|Hz].
    - apply (absorb_specs_view rho' _ tr2 (vms md2 tpL ms2) (vmd md2) KEPT1 REL [K_i1; K_i2] (rd_of segs (rm rhoE)) Hsm1v OBJS1 NKI z K_i1 (or_introl eq_refl)).
      cbn [K_i1 spec_range fst snd eval]. rewrite u64_lit by lia. lia.
    - apply (absorb_specs_view rho' _ tr2 (vms md2 tpL ms2) (vmd md2) KEPT1 REL [K_i1; K_i2] (rd_of segs (rm rhoE)) Hsm1v OBJS1 NKI z K_i2 (or_intror (or_introl eq_refl))).
      cbn [K_i2 spec_range fst snd eval]. rewrite u64_lit by lia. lia. }

  assert (P1 : present (view segs (rm rho3)) (T + 2832) (T + 2832 + 8)) by (intros z Hz; rewrite view_in by lia; apply PST; lia).
  assert (P2 : present (view segs (rm rho3)) (T + 2824) (T + 2824 + 8)) by (intros z Hz; rewrite view_in by lia; apply PST; lia).
  destruct (present_cell8F _ _ P1) as (v1 & R1 & C1). destruct (present_cell8F _ _ P2) as (v2 & R2 & C2).
  set (j1 := ss_next (ax_S T1)). set (j2 := Pos.succ j1).
  set (x1 := Z_to_bv 64 ((v1 - bv_unsigned (eval rho3 eFR)) mod 2 ^ 64)).
  set (x2 := Z_to_bv 64 ((v2 - bv_unsigned (Z_to_bv 64 1)) mod 2 ^ 64)).
  set (rho4 := rho_sets rho3 [(j1, x1); (j2, x2)]).
  assert (NX2 : ss_next (ax_S T2) = j1) by (rewrite HT2; reflexivity).
  assert (AG34 : agree_below j1 rho3 rho4).
  { apply agree_below_rho_sets. intros j v [E|[E|[]]]; apply (f_equal fst) in E; cbn [fst] in E; subst j; unfold j2; lia. }
  assert (H3 : SPA segs JP T2 rho4 tpL (tr2, mkCfg ms2 md2)).
  { apply (SPA_agree segs JP rho3 rho4 tpL T2 _); [rewrite NX2; exact AG34 | exact (fun k => k) | exact H2]. }
  assert (ND : List.NoDup (map fst [(j1, x1); (j2, x2)])).
  { cbn [map fst]. constructor; [intros [E|[]]; unfold j2 in E; lia | constructor; [intros [] | constructor]]. }
  assert (EV1 : eval rho4 (SAlu ALU_ADD eFR (SVar j1)) = Z_to_bv 64 v1).
  { cbn [eval]. rewrite <- (eval_agree j1 rho3 rho4 eFR AG34 EFRB). unfold rho4. rewrite (rw_rho_sets_in rho3 _ j1 x1 ND (or_introl eq_refl)).
    exact (proj1 (add_fresh _ v1 R1)). }
  assert (EV2 : eval rho4 (SAlu ALU_ADD (SVar j2) (SLit 1)) = Z_to_bv 64 v2).
  { cbn [eval]. unfold rho4. rewrite (rw_rho_sets_in rho3 _ j2 x2 ND (or_intror (or_introl eq_refl))). exact (proj2 (add_fresh _ v2 R2)). }
  assert (AV4 : agree_vals j1 rho' rho4).
  { split; [intros i Hi; rewrite <- (proj1 AG34 i Hi); reflexivity | intros l; rewrite <- (proj1 (proj2 AG34) l); reflexivity]. }
  assert (E151_4 : bv_unsigned (eval rho4 vT) = T).
  { cbn [eval vT]. rewrite <- (proj1 AV4 151%positive) by (apply LT1, NXlt; unfold GW; lia). rewrite E151'. apply u64_lit. lia. }

  assert (XT2 : ax_X T2 = []) by (rewrite HTR in XTR; exact XTR).
  assert (PD1 : SymState.pairwise_disjoint rho' (KEPT1 ++ REL)).
  { destruct Hsm1v as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _). rewrite OBJS1 in Hpd. exact Hpd. }
  destruct (SymFrame.pairwise_disjoint_app_inv rho' KEPT1 REL PD1) as (_ & _ & PDX).
  assert (H4 : SPA segs JP TR rho4 tpL (tr2, mkCfg ms2 md2)).
  { rewrite HTR. fold j1. fold j2. apply (SPA_carve_list segs JP rho4 T2 tpL _ [K_st2 eFR j1 j2] (Pos.succ j2) H3).
    - rewrite HTR in SWFT. exact SWFT.
    - rewrite NX2. unfold j2. lia.
    - constructor; [|constructor]. unfold K_st2. cbn beta iota zeta. rewrite E151_4.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; constructor; [cbn; lia | constructor; [cbn; lia | constructor]]|].
      split; [|split].
      + intros off Hoff. unfold rho4. rewrite rm_rho_sets. destruct (PST (T + off) ltac:(lia)) as [x Hx].
        exact (wok_rd_off_image2 _ (T + off) x ltac:(lia) ltac:(clear -TI Hoff; lia) Hx).
      + unfold cells_in_view. constructor; [|constructor; [|constructor]].
        * intros j Hj. rewrite EV1. unfold rho4. rewrite rm_rho_sets. specialize (C1 j Hj). cbn [c_addr c_w c_val] in C1. rewrite view_in in C1 by lia. exact C1.
        * intros j Hj. rewrite EV2. unfold rho4. rewrite rm_rho_sets. specialize (C2 j Hj). cbn [c_addr c_w c_val] in C2. rewrite view_in in C2 by lia. exact C2.
      + intros rr y j Hin. rewrite XT2 in Hin. destruct Hin.
    - constructor; [|constructor]. apply Forall_forall. intros o' Ho'.
      assert (Ho1 : In o' KEPT1) by (rewrite HT2 in Ho'; exact Ho').
      assert (WF' : obj_wf j1 o' = true).
      { pose proof (swf_objs _ (proj1 Hsm1v)) as X. rewrite OBJS1, forallb_app in X. apply andb_prop in X as [X _]. exact (proj1 (forallb_forall _ _) X o' Ho1). }
      rewrite (obj_range_agree_vals j1 rho' rho4 o' AV4 WF').
      replace (obj_range rho4 (carve_obj (K_st2 eFR j1 j2))) with (obj_range rho' O_stT2).
      { exact (PDX o' O_stT2 Ho1 (or_introl eq_refl)). }
      unfold K_st2, carve_obj, carved, O_stT2. rewrite !obj_range_mk by lia. rewrite E151_4. cbn [eval vT]. rewrite E151', u64_lit by lia. reflexivity.
    - cbn. split; [constructor | exact I]. }

  set (rho5 := rho_absorb rho4 RR (ms_with_mem ms2 (rm rhoE))).
  set (rho1'' := mkVal (rw rho1) (rl rho1) (rm rho5)).
  assert (AVE4 : agree_vals (ss_next (ax_S EC)) rhoE rho4).
  { split; [intros i Hi; rewrite <- (proj1 AV4 i (LT1 i Hi)); exact (proj1 Hag' i Hi) | intros l; rewrite <- (proj2 AV4 l); exact (proj2 Hag' l)]. }
  assert (RNG : forall o, In o RR -> obj_range rho4 o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S EC))); [exact AVE4 | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  assert (IRE : forall a, in_ranges rho4 RR a <-> in_ranges rhoE RR a).
  { intros a. split; intros (o & Ho & Hoa); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hoa). }
  assert (RM5 : forall a, rm rho5 a = if in_ranges_dec rho4 RR a then rm rhoE a else rm rho3 a).
  { intros a. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. unfold rho4. rewrite rm_rho_sets. reflexivity. }
  set (xzb := fun z => (T + 2792 <=? z) && (z <? T + 3168)).
  assert (XZB : forall z, xzb z = true <-> T + 2792 <= z < T + 3168) by (intros z; unfold xzb; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; tauto).
  assert (RCE : forall a : word, ~ in_ranges rhoE RR a -> ~ RZ A (bv_unsigned a) -> rm rhoL a = rm rhoE a).
  { intros a Hn Hrz. rewrite (HRM2 a Hrz). apply rm_absorb_out. exact Hn. }

  assert (RD5 : forall z, 0 <= z < 2 ^ 64 -> ~ RZ A z -> xzb z = false -> rd_of segs (rm rho5) (Z_to_bv 64 z) = rd_of segs (rm rhoE) (Z_to_bv 64 z)).
  { intros z Bz Hrz Hx. unfold rd_of at 1. rewrite RM5. destruct (in_ranges_dec rho4 RR (Z_to_bv 64 z)) as [Hi|Hn]; [reflexivity|].
    change (rd_of segs (rm rho3) (Z_to_bv 64 z) = rd_of segs (rm rhoE) (Z_to_bv 64 z)).
    destruct (in_ranges_dec rho' REL (Z_to_bv 64 z)) as [Hr|Hnr].
    - destruct (RREL _ Hr) as [K|K]; rewrite u64_lit in K by lia; [exfalso; rewrite (proj2 (XZB z) K) in Hx; discriminate Hx | exact (ICV z K)].
    - unfold rd_of. rewrite RM3. destruct (in_ranges_dec rho' REL (Z_to_bv 64 z)) as [Hr'|_]; [exfalso; exact (Hnr Hr')|].
      rewrite (RCE (Z_to_bv 64 z) (fun Hi => Hn (proj2 (IRE _) Hi)) ltac:(rewrite u64_lit by lia; exact Hrz)). reflexivity. }
  assert (V1 : forall z, ~ RZ A z -> xzb z = false -> view segs (rm rho5) z = view segs (rm rhoE) z).
  { intros z Hrz Hx. destruct (Z_le_dec 0 z) as [Z0|NZ]; [destruct (Z_lt_dec z (2 ^ 64)) as [Z1|NZ]|].
    2,3: rewrite !view_out by (clear -NZ; lia); reflexivity.
    rewrite !view_in by (clear -Z0 Z1; lia). exact (RD5 z (conj Z0 Z1) Hrz Hx). }
  assert (VL : forall z, z < topG G -> ~ LZ0 p n z -> xzb z = false -> ~ (T + 80 <= z < T + 112) -> view segs (rm rho5) z = view segs (rm rhoL) z).
  { intros z Hz HL Hx HQ. destruct (Z_le_dec 0 z) as [Z0|NZ]; [destruct (Z_lt_dec z (2 ^ 64)) as [Z1|NZ]|].
    2,3: rewrite !view_out by (clear -NZ; lia); reflexivity.
    rewrite !view_in by (clear -Z0 Z1; lia).
    assert (CHAIN : ~ RZ A z -> rd_of segs (rm rhoE) (Z_to_bv 64 z) = rd_of segs (rm rhoL) (Z_to_bv 64 z)).
    { intros Hrz. pose proof (VOC z Hz HL HQ) as X. rewrite !view_in in X by (clear -Z0 Z1; lia). rewrite <- X. unfold rd_of.
      rewrite (HRM2 (Z_to_bv 64 z) ltac:(rewrite u64_lit by (clear -Z0 Z1; lia); exact Hrz)). reflexivity. }
    destruct (in_ranges_dec rho4 RR (Z_to_bv 64 z)) as [Hi|Hn].
    - assert (Hrz : ~ RZ A z) by (pose proof (RR_rz _ (proj1 (IRE _) Hi)) as X; rewrite u64_lit in X by (clear -Z0 Z1; lia); exact X).
      rewrite (RD5 z (conj Z0 Z1) Hrz Hx). exact (CHAIN Hrz).
    - destruct (in_ranges_dec rho' REL (Z_to_bv 64 z)) as [Hr|Hnr].
      + destruct (RREL _ Hr) as [K|K]; rewrite u64_lit in K by (clear -Z0 Z1; lia); [exfalso; rewrite (proj2 (XZB z) K) in Hx; discriminate Hx|].
        assert (Hrz : ~ RZ A z) by (apply (RZ_img A rhoE tp md HA0 HROOM0 z); unfold IMG_LO, IMG_HI; clear -K; lia).
        rewrite (RD5 z (conj Z0 Z1) Hrz Hx). exact (CHAIN Hrz).
      + unfold rd_of. rewrite RM5. destruct (in_ranges_dec rho4 RR (Z_to_bv 64 z)) as [Hi'|_]; [exfalso; exact (Hn Hi')|].
        rewrite RM3. destruct (in_ranges_dec rho' REL (Z_to_bv 64 z)) as [Hr'|_]; [exfalso; exact (Hnr Hr') | reflexivity]. }
  assert (V3 : forall z, xzb z = true -> exists b, view segs (rm rho5) z = Some b).
  { intros z Hx. apply XZB in Hx. rewrite view_in by lia.
    destruct (in_ranges_dec rho4 RR (Z_to_bv 64 z)) as [Hi|Hn].
    - pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & _ & HTH & _). destruct HTH as [_ HTS].
      destruct (HTS z ltac:(lia)) as [b Hb]. rewrite (MV_T A rhoE tp md HA z ltac:(lia)) in Hb. rewrite view_in in Hb by lia.
      exists b. unfold rd_of. rewrite RM5. destruct (in_ranges_dec rho4 RR (Z_to_bv 64 z)) as [_|Hn']; [exact Hb | exfalso; exact (Hn' Hi)].
    - destruct (PST z Hx) as [x Hx']. exists x. unfold rd_of. rewrite RM5. destruct (in_ranges_dec rho4 RR (Z_to_bv 64 z)) as [Hi'|_]; [exfalso; exact (Hn Hi') | exact Hx']. }
  assert (HA5 : AInvA segs (refillA A 24) rho5 tpL md2).
  { apply (refill_back A rhoE rhoL rho5 tp tpL md md2 p n l1 l2 HA HLV HCLS HROOM0 HQL xzb); [|exact V1 | exact VL | exact V3].
    intros z Hx. exact (proj1 (XZB z) Hx). }
  assert (RW5 : forall i, (i < GW)%positive -> rw rho5 i = rw rhoE i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. rewrite <- (proj1 AVE4 i (NXlt i Hi)). reflexivity. }
  assert (HJF5 : JF nW st false (refillA A 24) Kc rho1'' rho5 tpL tr2 md2).
  { split.
    - split; [|split].
      + intros i Hi. unfold rho1''. cbn [rw]. rewrite (Hagw i Hi). symmetry. exact (RW5 i Hi).
      + intros l. unfold rho1'', rho5. cbn [rl rho_absorb]. rewrite (Hagl l). exact (proj2 AVE4 l).
      + intros a. reflexivity.
    - split; [exact HA5|]. split; [exact (stopJ_le _ _)|].
      split; [rewrite (RW5 12%positive), (RW5 13%positive) by (unfold GW; lia); exact HL0|]. split; [exact HKc2|].
      split; [unfold tp_ok in Htp0 |- *; rewrite (RW5 24%positive) by (unfold GW; lia); exact Htp0|].
      split; [exact I|].
      unfold top_high. rewrite (RW5 10%positive), (RW5 V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop0. }
  assert (H5 : SPA segs (JF nW st false (refillA A 24) Kc rho1'') TR rho5 tpL (tr2, mkCfg ms2 md2)).
  { pose proof (proj1 (proj1 H4)) as HsmT. pose proof (smatch_facts_hold _ _ _ _ HsmT) as HfT.
    unfold rho5. apply (SPA_absorb_any segs JP); [exact XTR | | exact H4 | exact HJF5].
    intros o a Ho Ha. exact (coveredb_sound _ _ _ rho4 o a HfT RRcov Ho Ha). }
  exists rho1'', rho5. split; [|exact H5].

  pose proof HA as (HG & _ & HF & (Hsep & _) & _).
  assert (NREL : forall a : word, ~ rt_zone G (bv_unsigned a) -> ~ in_ranges rho' REL a).
  { intros a NRT Hr. apply NRT. unfold rt_zone. destruct (RREL _ Hr) as [K|K]; [right; left; clear -K; lia|].
    left. split; [unfold IMG_HI; clear -K; lia | exact (inst_cells_rt _ K)]. }
  split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
  - intros a Hk. unfold rho1''. cbn [rm]. rewrite (Hagm a). rewrite RM5. destruct (in_ranges_dec rho4 RR a) as [Hi|Hn]; [reflexivity|].
    assert (NRT : ~ rt_zone G (bv_unsigned a)).
    { destruct Hk as [Hc|Hs]; [exact (client_not_rt CST HCST A _ _ HG HF Hsep Hc)|].
      pose proof (client_shadow_bounds CST XGL HCST HXGL A _ _ HG HF Hsep Hs) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
      intros R. apply (shadow_not_rt2 A (bv_unsigned a) HG ltac:(clear -B; lia)). left. exact R. }
    rewrite RM3. destruct (in_ranges_dec rho' REL a) as [Hr|_]; [exfalso; exact (NREL a NRT Hr)|].
    exact (RCE a (fun Hi => Hn (proj2 (IRE _) Hi)) (RZ_keep CST XGL HCST HXGL A rhoE tp md HA HROOM0 _ Hk)).
  - intros a HBa Hdef. unfold rho1''. cbn [rm]. rewrite RM5. destruct (in_ranges_dec rho4 RR a) as [Hi|Hn]; [rewrite <- (Hagm a); exact Hdef|].
    rewrite RM3. destruct (in_ranges_dec rho' REL a) as [Hr|_].
    + exfalso. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HBa. destruct (RREL _ Hr) as [K|K]; clear -K HBa TBAND; lia.
    + apply (HBD2 a HBa). assert (X : rm rhoC a = rm rhoE a) by (apply rm_absorb_out; intros Hi; exact (Hn (proj2 (IRE _) Hi))).
      rewrite X, <- (Hagm a). exact Hdef.
Qed.
End AT.

Theorem refill_call_HRF : ltac2:(tb__ "0|1|
S94OF_;S95Sa1Vsegs;R2Sa0VKc;A1M0A3Sd4Vsegs;R3G0A3SdbVnW;Vst;Sa7VCST;VXGL;VA;A3R4VA;VKc;Vrho1;VEC;VTR;R3AaF_;F_;FQ;Fok;").
Proof.
  intros ok Q Hokl Hokpl rhoE tp Hcont k HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (rf_facts rhoE tp _ Hw) as SF.
  apply (call_soundPA segs ok (JF nW st false A Kc rho1) (JRf A Kc 24 nv_q24) EC Pre_rf sR RR [(L_rf, JLRf A Kc 24)] Q rhoE tp HER).
  - change (map fst [(L_rf, JLRf A Kc 24)]) with [L_rf]. exact Hchk.
  - intros rhoP tp1. exact (proj1 refill_contract_ok ok A Kc 24 nv_q24 rhoP tp1 HKc Hokl Hokpl HBUD).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (rf_entry rhoE tp tr0 ms0 md1 SF Hsm0 HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    split; [exact (rf_exit_ok rhoE tp tr0 ms0 md1 SF HJ0 rhoL tpL tr' md' HJL)|].
    intros rho' HLK n' Hg' w' Hw'.
    destruct (rf_exit_core rhoE tp tr0 ms0 md1 SF Hsm0 HJ0 rhoL tpL rho' w' HLK Hw') as (rho1'' & rhoX & Hl & HC5).
    exact (Hcont rho1'' rhoX tpL Hl n' Hg' w' HC5).
  - exact HgQ.
  - exact Hw.
Qed.

Theorem refill_call_HRFE : ltac2:(tb__ "0|0|
S94OF_;SdcVnW;Vst;Sa7VCST;VXGL;VA;A3VA;VKc;Vrho1;VEC;VTR;R1A9FQ;").
Proof.
  intros Q rhoE tp Hcont w Hw. destruct w as [tr [ms md]].
  pose proof (rf_facts rhoE tp _ Hw) as SF.
  apply (call_completePA segs (JF nW st false A Kc rho1) (JRf A Kc 24 nv_q24) EC Pre_rf sR RR [(L_rf, JLRf A Kc 24)] Q rhoE tp HER).
  - change (map fst [(L_rf, JLRf A Kc 24)]) with [L_rf]. exact Hchk.
  - intros rhoP tp1. exact (proj2 refill_contract_ok A Kc 24 nv_q24 rhoP tp1 HKc HBUD).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (rf_entry rhoE tp tr0 ms0 md1 SF Hsm0 HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    split; [exact (rf_exit_ok rhoE tp tr0 ms0 md1 SF HJ0 rhoL tpL tr' md' HJL)|].
    intros rho' HLK w' Hw'.
    destruct (rf_exit_core rhoE tp tr0 ms0 md1 SF Hsm0 HJ0 rhoL tpL rho' w' HLK Hw') as (rho1'' & rhoX & Hl & HC5).
    exact (Hcont rho1'' rhoX tpL Hl w' HC5).
  - exact Hw.
Qed.
End SITE.
End RF.
End F0A_refill.

