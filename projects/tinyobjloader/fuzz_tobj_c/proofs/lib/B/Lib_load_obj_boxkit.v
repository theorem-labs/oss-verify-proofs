(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "cons"; "true"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "JA"; "NDA"; "amode"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bxK"; "bxV"; "bxt"; "bitem"; "bxN"; "bxS"; "BIc"; "bd_nn"; "bd_wpos"; "bsumK"; "bsumV"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Init.Logic"; "and"; "eq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Box.
Variable AInv : ltac2:(tb__ "0|0|
S22S9S2S1cQ40A1A1S21OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S3S3SaSaA2SaA2A1").
Variable PA : AA -> Prop.

Lemma SPA_rebox : ltac2:(tb__ "0|2|
S13S13S2S3S8S8A2A1S2S3S3S8SaA2S8A2A1S2S14A1M0G0SfS1eS9S2S1cQ40A1A1S1dS0S16RbA1S16RaA1A2S0S15RcA1S15RbA1A2S0Z0M1S12RcA1A2S0G1S11RdA1A2S20S4S19RaA1S6A3S20S4S19RcA1S6A3S18RdR9A2S1fS18RdRaA2S1fS0S1S1bRdRaA2S12R11A1A2S1S1bReRaA2S12R12A1A2A2S0S1S1aRdRaA2S11R11A1A2S1S1aReRaA2S11R12A1A2A2A2A2F_;F_;ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R11VPA;SeRfReRdRbA4AcRaR9R8R7A6ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R11VPA;SeR10RfRdRcA4AcRbRaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd';Fbd;Ffr;Ftv;FBX';FBX;").
Proof.
  intros BX BX' tv fr bd bd' am A rho tp w HS HN HV0 HK0 Hw' HI [Hsm (Ai & kc & HJ)].
  split; [exact Hsm|]. exists Ai, kc.
  apply (JAi_rebx AInv CST XGL NP Kc rho0 P0f FB FF BX BX' PA (NDA tv fr bd am) bd' Ai kc rho tp _ _); [|exact HN|exact HJ].
  cbn [nd_bd nd_am]. intros HBU HCK Hkc. pose proof HBU as (A1 & A2 & A3 & A4 & A5 & Hw & Hnn & B1 & B2).
  destruct (HI Hw Hnn) as (Hnn' & LV & LK).
  pose proof (apot_range am rho) as [[R1 _] [R2 _]].
  unfold bxa, bxV, bxK, capK in *. cbn [fst snd] in *. split; [|lia].
  unfold BUD. cbn [fst snd]. split; [lia|]. split; [lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact Hw'|]. split; [exact Hnn'|]. lia.
Qed.

Lemma SPA_box_out : ltac2:(tb__ "0|4|
S13S13SaSaS2S3S8S8A2A1S2S3S3S8SaA2S8A2A1S2S14A1M0G0SfS1eS9S2S1cQ40A1A1S1dS0S16RcA1S16RdA1A2S0S15RdA1S15ReA1A2S0Z0M1S12RfA1A2S0G1S11R10A1A2S0S1S12R11A1RfA2S12R10A1A2S0S1S11R12A1RfA2S11R11A1A2S0G1R11A2M2G2ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R14VPA;SeR11R10S7S14RfReA3RdA4AcRcRbRaR9A6ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R16VPA;SeR12R11S5S14S17Z1M3G1R14A3S5S14S17G1G3R13A3RfA3A3ReA4AcRdRcRbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FA;Fam;Frest;Fpre;Ffr;Ftv;Fk;Fc;FBXL;FBX;").
Proof.
  intros BX BXL c k tv fr pre rest am A rho tp w HS HN HV0 HK0 HV HK Hc Hk HW.
  assert (Hwp : bd_wpos (pre ++ rest) = true).
  { destruct HW as [_ (Ai & kc & HJ)]. destruct (JAi_proj_BUD AInv CST XGL NP Kc rho0 P0f FB FF BXL PA _ Ai kc rho tp _ _ HJ) as ((_ & _ & _ & _ & _ & Hw & _) & _). exact Hw. }
  assert (Hwr : bd_wpos pre = true /\ bd_wpos rest = true) by (unfold bd_wpos in *; rewrite forallb_app in Hwp; apply andb_prop in Hwp; exact Hwp).
  apply (SPA_rebox BXL BX tv fr (pre ++ rest) (BIc 1 0 c :: BIc 0 1 k :: rest) am A rho tp w HS HN HV0 HK0); [| |exact HW].
  - unfold bd_wpos in *. unfold BIc. cbn [forallb bi_v bi_k]. rewrite (proj2 Hwr). reflexivity.
  - intros _ Hnn. unfold bd_nn in Hnn. apply Forall_app in Hnn as [Hn1 Hn2].
    destruct (bsum_nonneg pre rho (proj1 Hwr) Hn1) as [S1 S2].
    rewrite bsumV_app, bsumK_app. unfold BIc. cbn [bsumV bsumK bi_v bi_k]. unfold bival at 1 2 3 4. cbn [bi_f bi_c lfval].
    split; [|lia]. unfold bd_nn. constructor; [unfold bival; cbn [bi_f bi_c lfval]; lia|]. constructor; [unfold bival; cbn [bi_f bi_c lfval]; lia | exact Hn2].
Qed.

Lemma SPA_JA_P0_get : ltac2:(tb__ "0|0|
S13S10S1eS9S2S1cQ40A1A1S1dScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R6VPA;R5AcR4R3R2R1A6VP0f;Vrho0;A1F_;Fw;Ftp;Frho;FA;Fnd;FBX;").
Proof.
  intros BX nd A rho tp w [_ (Ai & kc & HJ)]. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). exact HP0.
Qed.
Lemma SPA_JA_P0_set : ltac2:(tb__ "0|0|
S9OF_;S13S10S1eS9S2S1cQ40A1A1S1dR7Vrho0;A1ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;R7VPA;R6AcR5R4R3R2A6ScSbSdVAInv;VCST;VXGL;VNP;VKc;Vrho0;R9VFB;VFF;R8VPA;R7AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fnd;FBX;FP0f';").
Proof.
  intros P0f' BX nd A rho tp w HP' [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & HN3 & HFR & HK & HP0 & HXA & HBU & HPA & HCK & HCN).
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HN3|]. split; [exact HFR|]. split; [exact HK|]. split; [exact HP'|]. split; [exact HXA|]. split; [exact HBU|]. split; [exact HPA|]. split; [exact HCK | exact HCN].
Qed.
End Box.
