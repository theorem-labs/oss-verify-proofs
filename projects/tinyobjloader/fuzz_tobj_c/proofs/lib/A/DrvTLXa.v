(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "list"; "nat"; "option"; "Some"; "app"; "None"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "acell"; "mkACell"; "in_rangesZ"; "view"; "cells_ok"; "RTC_A"; "c_addr"; "c_w"; "rtc_cells_img"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "of_nat"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "FdChannel"; "VmState"; "fd_lookup"; "m_fds"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "rm"; "rw"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa.TLX"; "BX0"; "P0T"; "KcT"; "JT"; "SH0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "KV_T"; "CST_drv"; "KVpp"; "KVrtc"; "PPF"; "KP_T"; "KVsh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "JAi"; "ndesc"; "JA"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0"; "ch1"; "EVS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "mkBX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "K_HIGH_MEM_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "band_free"; "Kc_ok"; "errno_addrA"; "with_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "P0f_T"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof"; "clsZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tnz"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CST_drv : list (Z * Z) := ltac2:(tb__ "0|5|
S2S5S0S0A2M0S3S0S0Z14d40Z80M1A4S2G0S3S0S0Z160c0Z40A4S2G0S3S0S0Z1a7c0G1A4S2G0S3S0S0Z21440G1A4S2G0S3S0S0Z22b80Zf00A4S2G0S3S0S0Z613a50Z10000A4S2G0S3S0S0Ze47f8Z10M2A4S2G0S3S0S0Ze7b30Z8M3A4S2G0S3S0S0Ze9978G3A4S2G0S3S0S0Ze99b8G3A4S2G0S3S0S0Ze99c0G3A4S2G0S3S0S0Ze99a8G3A4S2G0S3S0S0Ze99d8G2A4S2G0S3S0S0Ze9a98G3A4S2G0S3S0S0Zec260Z300A4S2G0S3S0S0Zec540Z1800A4S2G0S3S0S0Zedd40G3A4S2G0S3S0S0Zedd90Z1M4A4S2G0S3S0S0Zeebf8Z2cA4S2G0S3S0S0Zeec30Z1dA4S2G0S3S0S0Zeec4eZ72A4S2G0S3S0S0Zf20daZ2A4S2G0S3S0S0Z182f78G3A4S2G0S3S0S0Z183020G3A4S2G0S3S0S0Z1832a0G4A4S2G0S3S0S0Z623a50Z14A4S2G0S3S0S0Z624510G3A4S2G0S3S0S0Z6445f8G3A4S2G0S3S0S0Z644608Z220A4S2G0S3S0S0Z644828Z4A4S2G0S3S0S0Z64484bG4A4S2G0S3S0S0Z644ca8Z450A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma errno_in_CST_drv : ltac2:(tb__ "0|0|
S0S4cR1A1S10S39R2A2F_;Fa;").
Proof. intros a Ha. unfold errno_addrA, ERRNO_A in Ha. exists 0x624510, 8. split; [cbn; tauto | lia]. Qed.

Definition KVrtc : list acell := ltac2:(tb__ "0|4|
S2SeSfZe9ae8U8M0Zddf74A3S2SeSfZe9af0G0Zde378A3S2SeSfZf20d8U1M1Z1M2A3S2SeSfZf20d9G1G2A3S2SeSfZf20e0G0S48A3S2SeSfZf20e8G0Z0M3A3S2SeSfZf20f0G0G3A3S2SeSfZ182fa0G0ZffffffffffffffffA3S2SeSfZf0c5cG1G2A3S4SeA1A3A3A3A3A3A3A3A3A3").
Definition KVsh : list acell := ltac2:(tb__ "0|2|
S2SeSfZ800c0998U8M0Z0M1A3S2SeSfZ800c09a0G0G1A3S4SeA1A3A3").

Definition PPF : Z := 0xeec4d.
Definition KVpp : list acell := [mkACell PPF 1 1].
Definition KV_T : list acell := ltac2:(tb__ "0|0|
SaSeS3bSaSeS3eS3aA3A3").

Definition law_pp_stmt (AInv : AA -> valuation -> list word -> Model -> Prop) (CST : list (Z * Z)) : Prop := ltac2:(tb__ "0|2|
S17S2aS2cS6S27Q40A1A1S20VAInv;R4R3R2R1A4S18S8S27Q8M0A1M1A1S11S37S2eR4A1S3cA3S9G1S28G0Z1A2A2A3F_;Fmd;Ftp;Frho;FA;S19S10VCST;S3cA2A1A2").

Definition KP_T : list (Z * Z) := ltac2:(tb__ "0|1|
S2S5S0S0A2M0S3S0S0Z7fffc570Z7fffc750A4S2G0S3S0S0Z800158a8Z80015ba8A4S4G0A1A3A3").

Lemma KVrtc_in : ltac2:(tb__ "0|0|
S2bSeS30SeR1S3bA3S30SeR2S16S13R3A2A3F_;Fc;FG;").
Proof.
  intros G c Hc. unfold KVrtc in Hc. unfold rtc_cells_img. cbn [rt_musl_memcpy rt_musl_memset RTC_A].
  cbn in Hc. intuition (subst; cbn; tauto).
Qed.

Section TLX.
Variable AInv : ltac2:(tb__ "0|0|
S2aS2cS6S27Q40A1A1S20OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S10VCST;R1A2S17S1bZ0R2A2S1cR2S47A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S10VXGL;R1A2S17S1bZ0R2A2S1cR2S47A2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S0S10S39R1A2S10VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.

Variable rhoT : valuation.
Variable F : list byte.
Variable T0 : list event.
Variable MD : Model -> Prop.
Hypothesis HMDvm : ltac2:(tb__ "0|0|
S20S24VMD;R2A1VMD;S4dR2R3A2A1F_;Fv;Fmd;").
Hypothesis HMDfd1 : ltac2:(tb__ "0|0|
S20VMD;R1A1S18S8S22A1S25S26R2A1S43A2S9S22S23S43A1A2A3F_;Fmd;").

Definition KcT (k : nat) : KcA := ltac2:(tb__ "0|1|
S6S21A1M0S20S17VMD;R1A1S18G0R2SaS21VT0;S7G0Lk;Vk;S4S21A1S7S44U2A1Ln;X7x2A3A3A2Lmd;Ltr;").

Definition SH0 (r : valuation) : Prop := ltac2:(tb__ "0|4|
S17S0S17S1bZ800c0998R1A2S1cR1Z800c09a8A2A2S18S8S27Q8M0A1M1A1M2S2eVr;S28Q40R2A2A2M3S9G1S28G0Z0A2A2A3F_;Fa;S0S1aS17S1bZ7fffc570R1A2S1cR1Z7fffc750A2A2S17S1bZ800158a8R1A2S1cR1Z80015ba8A2A2A2S19S18G2G3SbG1A1A3A1F_;Fa;A2").
Definition P0T (r : valuation) : Prop := ltac2:(tb__ "0|0|
S17S4eVF;Vr;A2S35Vr;A1A2").

Definition BX0 : bxt := ltac2:(tb__ "0|1|
S46S3S0S0Z0M0G0A4G0G0A3").

Definition JT (PA : AA -> Prop) (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|1|
S41VAInv;VCST;VXGL;S36S33Vk;A1VrhoT;S32S4S5S0S0A2M0A1S4S5G0S0A2A1S31VPA;Vnd;Ac").
Definition JTi (PA : AA -> Prop) (k : nat) (nd : ndesc) (Ai : AA) (kc : Z) : jpredA := ltac2:(tb__ "0|1|
S3fVAInv;VCST;VXGL;S36S33Vk;A1VrhoT;S32S4S5S0S0A2M0A1S4S5G0S0A2A1S31VPA;Vnd;VAi;Vkc;Ae").

Lemma Kc_okT : ltac2:(tb__ "0|0|
S7S4bS33R1A1A1Fk;").
Proof. intros k tr md v [H1 H2]. split; [apply HMDvm; exact H1 | exact H2]. Qed.

Lemma KVpp_ok : ltac2:(tb__ "0|0|
S2aS2cS6S27Q40A1A1S20VAInv;R4R3R2R1A4S12S11S37S2eR4A1A2S3aA2F_;Fmd;Ftp;Frho;FAi;").
Proof.
  intros Ai rho tp md HM. unfold KVpp. constructor; [|constructor]. intros j Hj. cbn [c_addr c_w c_val] in *.
  destruct j as [|j]; [|lia]. rewrite Z.add_0_r. rewrite (proj1 HLPP Ai rho tp md HM). reflexivity.
Qed.

Lemma HKV_T : ltac2:(tb__ "0|1|
S2aOF_;S49S40S2aS0S2cS6S27Q40A1A1S6S21A1S20S3fVAInv;VCST;VXGL;S36R8VrhoT;S32S4S5S0S0A2M0A1S4S5G0S0A2A1S31R9R7R6R5R4R3R2R1A12S12S11S37S2eR5A1A2S38A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc;FPA;").
Proof.
  intros PA Kc nd Ai kc rho tp tr md (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _).
  unfold KV_T. apply Forall_app. split; [|apply Forall_app; split].
  - pose proof (law_rtc _ _ _ ALA Ai rho tp md HM) as HR.
    apply Forall_forall. intros c Hc. exact (proj1 (Forall_forall _ _) HR c (KVrtc_in _ c Hc)).
  -
    destruct HP0 as [_ [HZ _]]. destruct HK0 as [K1 _].
    assert (BY : forall a, 0x800c0998 <= a < 0x800c09a8 -> view segs (rm rho) a = Some (Z_to_bv 8 0)).
    { intros a Ha. rewrite view_in by lia. rewrite DrvJ.rd_of_high by lia.
      rewrite (K1 a ltac:(lia)).
      - exact (HZ a Ha).
      - right. split; [|rewrite (HZ a Ha); discriminate]. exists (8 * (a - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
        + left. right. left. split; [apply HCSTdrv; exists 0x644ca8, 0x450; split; [cbn; tauto | unfold SHADOW_OFF; lia] | unfold errno_addrA, ERRNO_A, SHADOW_OFF; lia].
        + unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    unfold KVsh. repeat constructor; intros j Hj; cbn [c_addr c_w c_val] in *;
      rewrite BY by lia; f_equal;
      do 8 (destruct j as [|j]; [reflexivity|]); lia.
  -   exact (KVpp_ok Ai rho tp md HM).
Qed.

Lemma HKP_T : ltac2:(tb__ "0|3|
S2aOF_;S49S40S2aS0S2cS6S27Q40M0A1A1S6S21A1S20S0S0S0S3fVAInv;VCST;VXGL;S36RbVrhoT;S32S4S5S0S0A2M1A1S4S5G1S0A2A1S31RcRaR9R8R7R6R5R4A12S30G1S3S0S0R4R3A4S3dA3S17S1bR5R3A2S1cR3R4A2A2S17S17S1bZ646000R4A2S1cR4S1fZ2Z40A2A2A2S19S18S8S27Q8A1M2A1S2eRaS28G0R4A2A2SbG2A1A3A1A2F_;F_;F_;Fz;Fhi;Flo;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc;FPA;").
Proof.
  intros PA Kc nd Ai kc rho tp tr md lo hi z (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _) Hin Hz.
  destruct HP0 as [_ [_ HP]]. destruct HK0 as [K1 _].
  unfold KP_T in Hin. cbn in Hin.
  assert (RNG : 0x7fffc570 <= z < 0x7fffc750 \/ 0x800158a8 <= z < 0x80015ba8).
  { destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
  split; [lia|]. rewrite (K1 z ltac:(lia)); [exact (HP z RNG)|].
  right. split; [|exact (HP z RNG)]. exists (8 * (z - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
  - left. right. left. split; [apply HCSTdrv; destruct RNG as [R|R]; [exists 0x22b80, 0xf00 | exists 0xec540, 0x1800]; (split; [cbn; tauto | unfold SHADOW_OFF; lia])
                             | unfold errno_addrA, ERRNO_A, SHADOW_OFF; destruct RNG; lia].
  - unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma HKVrng_T : ltac2:(tb__ "0|3|
SeS30SeR1S38A3S1aS17S1bZe4000S14R2A1M0A2S1bS1dG0S1eS15R2A1A1A2M1Z646000M2A2A2S17S1bG2G0A2S1bG1S1fZ2Z3eA2A2A2A2F_;Fc;").
Proof. intros c Hc. unfold KV_T, KVrtc, KVsh, KVpp, PPF in Hc. cbn in Hc. intuition (subst; cbn; lia). Qed.

Lemma JT_tv_band_free : ltac2:(tb__ "0|1|
S2aOF_;S7S40S2cS6S27Q40A1A1S6S21A1S20S5S2dS2dA2M0S34R8R7R6R5R4R3R2A7S30G0R2S42R7A1A3S50R7R3A2S4aS45R8ScS2dS2dR4A3A2S45R8SdS2dS2dR4A3A2A2F_;F_;F_;Ft;Fmd;Ftr;Ftp;Frho;Fnd;Fk;FPA;").
Proof.
  intros PA k nd rho tp tr md t (Ai & kc & HJ) Hin Hnz.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & _).
  destruct (proj1 (Forall_forall _ _) HN t Hin Hnz) as (Hpos & Hlive & _).
  unfold tvv in Hpos, Hlive. cbn [fst snd] in Hpos, Hlive |- *. unfold uval in *.
  apply band_free_of_points; [lia|]. intros a Ha.
  pose proof (law_client_app _ _ _ ALA Ai rho tp md a HM) as X. pose proof (topG_range (aa_geom Ai)) as TG.
  assert (HC : client_addrA CST Ai a).
  { left. right. left. exists (uval rho (fst t)), (uval rho (snd t)). split; [exact Hlive | exact Ha]. }
  specialize (X HC). unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.
Lemma band_free_clsZ : ltac2:(tb__ "0|1|
S2cS1S1S4aS29Q40M0S2fR3R2A2A2S29G0S2fR3R1A2A2A2S4fR4R3R2A3F_;Fil;Fib;Frho;").
Proof.
  intros rho ib il H. unfold band_free, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ in *.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.HSE, SHB in *. lia.
Qed.

Lemma HCSTKV_T : ltac2:(tb__ "0|0|
S0S7S0S0S30SeSfR4R3R2A3S38A3S1bS1dR5S1eR4A1A2Z646000A2S17S1bR6R3A2S1cR3S1dR6S1eR5A1A2A2A2S19S10VCST;R4A2A1F_;F_;F_;Fz;Fv;Fk;Fa;").
Proof.
  intros a k v z Hc Hhi Hz Hin. destruct (HCSTok z Hin) as [_ Hf].
  assert (FT : forall G, cells_footb (rtc_cells_img RTC_A G) z = true).
  { intros G. unfold KV_T in Hc. apply in_app_or in Hc as [Hc|Hc].
    - pose proof (KVrtc_in G _ Hc) as Hin'. unfold cells_footb. apply existsb_exists. exists (mkACell a k v). split; [exact Hin'|].
      unfold in_cellb. cbn [c_addr c_w]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
    - apply in_app_or in Hc as [Hc|Hc]; exfalso.
      + unfold KVsh in Hc. cbn in Hc. destruct Hc as [E|[E|[]]]; injection E; intros; subst; lia.
      +   unfold KVpp in Hc. cbn in Hc. destruct Hc as [E|[]]. injection E; intros; subst. cbn in Hz.
        assert (z = PPF) by lia. subst z. exact (proj2 HLPP Hin). }
  rewrite (FT G0) in Hf. discriminate.
Qed.

End TLX.
