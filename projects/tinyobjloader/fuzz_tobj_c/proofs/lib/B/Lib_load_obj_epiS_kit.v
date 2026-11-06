(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "BUD"; "BXnn"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "app"; "nil"; "false"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "AHead"; "AK0"; "AV0"; "NDA"; "JA"; "JAi"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "and"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PotIn.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S1cSeS5S17Q40A1A1S19OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP' : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S5S6S6S0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.

Lemma BUD_pot_in : ltac2:(tb__ "0|3|
S5S1A1S0S0S0S0S0S0S0S0SeS3S8S1RaS7S1S2Z1M0Z0M1S13A3S7S1S2G1G0S12A3S9S1A1A3A3A3SbS0S0SfR9G1A2SfSfR8G1A2R7A2A4R4R3R2R1A6S10G1RaA2M2G2G2S18G2S10RaS13A2A2S18G2S10RaS12A2A2S3R10SbS0S0SfRfRcA2SfSfReRbA2RdA2A4RaR9R8R7A6F_;F_;F_;F_;F_;F_;Frho;FKf;FKm;FV;Fpk;Fpv;Fkc;Fx2;Fx1;Fb;").
Proof.
  intros b x1 x2 kc pv pk V Km Kf rho H H1 H2 Hkc Hpv Hpk.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  rewrite bsumV_app in B1. rewrite bsumK_app in B2. rewrite bd_wpos_app in Hw. apply andb_prop in Hw as [Hw _].
  unfold BIc in B1, B2. cbn [bsumV bsumK bi_v bi_k] in B1, B2. unfold bival in B1, B2. cbn [lfval bi_f bi_c] in B1, B2.
  apply bd_nn_app in Hn as [Hn _].
  unfold BUD. cbn [fst snd]. repeat (split; [first [assumption | lia]|]). lia.
Qed.

Lemma JAi_pot_in : ltac2:(tb__ "0|2|
S5S6SdSdA2A1S5S6S6SdS0A2SdA2A1S5S1A1SdS1cS0SeS5S17Q40A1A1S5S1aA1S19S4VBX;A1S16VAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S14RbRaS8S1R9S7S1S2Z1M0Z0M1S13A3S7S1S2G1G0S12A3S9S1A1A3A3A3S11R8SaA2A4R7R6R5R4R3R2A12S16VAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S14RcRbRaS11R9ScA2A4R8R7R6R5R4R3A12F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fhd;Fbd;Ffr;Ftv;").
Proof.
  intros tv fr bd hd Ai kc rho tp tr md [HX1 HX2] HJ.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCK & HCN).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [exact HXA|].
  split; [|split; [exact HPA | split; [exact HCK | exact HCN]]].
  pose proof (apot_range (AHead hd true) rho) as [R1 R2].
  unfold apot in HBU. cbn [am_eval apotz] in HBU. unfold bxa in HBU |- *. cbn [fst snd] in HBU |- *.
  apply (BUD_pot_in bd (fst (bx2 BX)) (snd (bx2 BX)) kc _ _ _ _ _ rho HBU HX1 HX2 (XA_kc_nonneg _ _ _ _ _ _ HXA) R1 R2).
Qed.

Lemma SPA_JA_pot_in : ltac2:(tb__ "0|2|
S5S6SdSdA2A1S5S6S6SdS0A2SdA2A1S5S1A1SdS1eSeS5S17Q40A1A1S1dS4VBX;A1S1bVsegs;S15VAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S14R9R8S8S1R7S7S1S2Z1M0Z0M1S13A3S7S1S2G1G0S12A3S9S1A1A3A3A3S11R6SaA2A4AcR5R4R3R2A6S1bVsegs;S15VAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S14RaR9R8S11R7ScA2A4AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fhd;Fbd;Ffr;Ftv;").
Proof.
  intros tv fr bd hd A rho tp [tr [ms md]] HX [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc. exact (JAi_pot_in tv fr bd hd Ai kc rho tp tr md HX HJ).
Qed.
End PotIn.
