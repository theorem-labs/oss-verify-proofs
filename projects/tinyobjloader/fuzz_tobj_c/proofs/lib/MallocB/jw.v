(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz jh DrainTR.

(* [comment removed for export] *)
Module SpineMallocSecE4P.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_geom"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "None"; "length"; "nil"; "option"; "@Corelib.Init.Logic"; "eq"; "not"; "and"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "ulink"; "UStopLeOrPc"; "ustop"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "clsP"; "JGs"; "JGsC"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSecOK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocSecE4.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OKEP.
Variable nW : nat. Variable st : ustop. Variable nx : positive. Variable hi : bool.
Let W : list ulink := Wcan nW.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
SbS37VCST;R1A2S37S3eR2A2S1aF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SbS37VCST;R1A2S18S31R2A1A1F_;Fa;").
Let JGs : ltac2:(tb__ "0|0|
S5S5F_;S5S1fS0SeQ40A1S1eFa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S3aVnW;Vst;Vnx;A3").
Let JGsC : ltac2:(tb__ "0|0|
S5S5F_;S5S1fS0SeQ40A1S1eFa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S3bVnW;Vst;Vnx;A3").
Variable Posts : ltac2:(tb__ "0|0|
S5S1fS10S11S3dS35A2A1F_;F_;").
Variables (E1 D2 T4a T4b C5a C5b : axst).

Hypothesis EG12 : ltac2:(tb__ "0|5|
S5S1fS0SeQ40M0A1M1S10G1A1M2S1cOF_;S26VW;Vst;A2S20R6A1S39Vhi;SdG0R5A2S25SdG0S1R6PcM3A2A2A1A3S0S0G2S3cSdG0R9A2S25SdG0S1RaG3A2A2A1RaR3A4S1bS4S1dS4VJGs;S5R1LX;M4RdRcR4RaA5VD2;R3R2A5R8A3F_;FtpY;FrhoY;Frho';S0S1bS4S1dS4VJGsC;G4RbRaR9R8A5VE1;R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Hypothesis EG3 : ltac2:(tb__ "0|7|
S5S1fS0SeQ40M0A1M1S1cOF_;S26VW;Vst;A2S20R5A1S29S28S2bS14S8S7R7A1A2A1Z1A2S2cZ2Z14A2A2SbS19S27S36SdG0R6A2A1M2R1A2S29R1S28G2S2aS25SdG0S1R7PcM3A2A2A1Z8A2A2A2A2S18S17S16SeQ8A1M4A1S2R8SfG0R2A2A2S13G4A1A3A1F_;Fz;S0S0S10G1A1M5S3fSaRcA1SdG0R9A2S25SdG0S1RaG3A2A2A1RaR3A5S1bS4S1dS4VJGs;S5S38R1A1LX;RdRcR4RaA5VT4a;R3R2A5R9A3F_;FtY;FrY;Frho'';S0G5S1bS4S1dS4VJGs;S5R1LX;M6RcRbRaR9A5VT4b;R2R1A5R8A3FtY;FrY;S0G5S1bS4S1dS4VJGs;G6RdRcRbRaA5VD2;R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Hypothesis EG41a : ltac2:(tb__ "0|5|
S5S1fS0SeQ40M0A1M1S1cOF_;S17S23Vst;S22A3S17S10S21A1VW;S15S21A1A3F_;S26VW;Vst;A2S20R6A1S6S0S0S10G1A1M2S11SbSbA2M3S32G3R1S30R5A1A3S2fR2S12SbSbSdG0RbA2S25SdG0S1RcPcA2A2A1A4A2F_;Fbn;S2eR5RbR4A3S1bS4S1dS4VJGs;S2dS5S38R1A1LX;M4R6A2ReRdR5RbA5VC5a;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S0G2S1bS4S1dS4VJGs;G4RbRaR9R8A5VT4a;R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Hypothesis EG41b : ltac2:(tb__ "0|5|
S5S1fS0SeQ40M0A1M1S1cOF_;S17S23Vst;S22A3S17S10S21A1VW;S15S21A1A3F_;S26VW;Vst;A2S20R6A1S6S0S0S10G1A1M2S11SbSbA2M3S32G3R1S30R5A1A3S2fR2S12SbSbSdG0RbA2S25SdG0S1RcPcA2A2A1A4A2F_;Fbn;S2eR5RbR4A3S1bS4S1dS4VJGs;S2dS5R1LX;M4R6A2ReRdR5RbA5VC5b;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S0G2S1bS4S1dS4VJGs;G4RbRaR9R8A5VT4b;R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Hypothesis ETLa : ltac2:(tb__ "0|8|
S5S1fS0S0SeQ40M0A1M1S10G1A1M2S6S26VW;Vst;A2S20R7A1ScS17G1S1R7R1A2S1R8R1A2A3Fi;ScS17S10SeQ8A1M3A1S3R8R1A2S3R9R1A2A3Fl;S24VCST;VXGL;RbRbS2R9A1S2R8A1A6S27S2bS14S8S7RcA1A2A1S9RcA1A2S11SbSbA2M4S32G4R1S30R8A1A3S2fR2S12SbSbSdG0RbA2M5S25SdG0S1RcPcA2A2A1M6A4A2F_;Fbn;SbS19S27S36G5A1M7R1A2S29R1S28G7S2aG6Z8A2A2A2A2S18S17S16G3A1S2RdSfG0R2A2A2S13G3A1A3A1F_;Fz;S0G2S1bS4S1dS4VJGs;S2dS5S38R1A1LX;RbA2R11R10ReRdA5VC5a;R2R1A5S34S4S33RfRcVPosts;R11R10A2A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Hypothesis ETLb : ltac2:(tb__ "0|8|
S5S1fS0S0SeQ40M0A1M1S10G1A1M2S6S26VW;Vst;A2S20R7A1ScS17G1S1R7R1A2S1R8R1A2A3Fi;ScS17S10SeQ8A1M3A1S3R8R1A2S3R9R1A2A3Fl;S24VCST;VXGL;RbRbS2R9A1S2R8A1A6S27S2bS14S8S7RcA1A2A1S9RcA1A2S11SbSbA2M4S32G4R1S30R8A1A3S2fR2S12SbSbSdG0RbA2M5S25SdG0S1RcPcA2A2A1M6A4A2F_;Fbn;SbS19S27S36G5A1M7R1A2S29R1S28G7S2aG6Z8A2A2A2A2S18S17S16G3A1S2RdSfG0R2A2A2S13G3A1A3A1F_;Fz;S0G2S1bS4S1dS4VJGs;S2dS5R1LX;RbA2R11R10ReRdA5VC5b;R2R1A5S34S4S33RfRcVPosts;R11R10A2A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").

Theorem esec_ok_chain_P : ltac2:(tb__ "0|2|
S5S1fS0SeQ40M0A1M1S10G1A1S17S23Vst;S22A3S17S10S21A1VW;S15S21A1A3F_;S26VW;Vst;A2S20R6A1S39Vhi;SdG0R5A2S25SdG0S1R6PcA2A2A1A3S0S1bS4S1dS4VJGsC;S5R1LX;RaR9R8R7A5VE1;R1R6A5S34S4S33R8R6VPosts;RaR9A2A5A3FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HW HUS HKc HC rhoX.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  apply (EG12 A Kc rho a tp _ HUS HKc HC). intros rho1 rhoY tpY SL1.
  apply (etriple_pre_pure segsA _ _ (Z.of_nat (length (aa_sec A)) + 1 < 2 ^ 20 /\ Z.of_nat (length (aa_sec A)) <= aa_Km A)).
  { intros [tr [ms md]] Hw. exact (d2_pure nW st nx A Kc rho1 a rhoY tpY tr md (proj2 Hw)). }
  intros [HRM HL9].
  assert (E1r : rw rho1 12%positive = rw rho 12%positive) by (destruct SL1 as (W1 & _); apply W1).
  assert (RD1 : forall z, Sh ua <= z < Sh ua + L / 8 -> rm rho1 (Z_to_bv 64 z) <> None) by (destruct SL1 as (_ & _ & _ & D1); exact D1).
  apply (EG3 A Kc rho1 a _ HUS HKc HRM); [rewrite E1r; exact RD1 | |].
  - rewrite E1r. fold ua L. intros rho2 rY tY SL4.
    assert (E2r : rw rho2 12%positive = rw rho 12%positive) by (destruct SL4 as (W2 & _); rewrite W2; exact E1r).
    apply (EG41a A Kc rho2 a _ HW HUS HKc). rewrite E2r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (etriple_pre_pure segsA _ _ _ (fun w Hw => c5_pure nW st nx CST XGL HCST HXGL HCSTS HCSTD (fun X : AA => bumpP X) G2 A Kc rho rho1 rho2 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 SL4 DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (ETLa A Kc rho rho3 a tp G2 HUS HKc HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
  - intros rY tY.
    apply (EG41b A Kc rho1 a _ HW HUS HKc). rewrite E1r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (etriple_pre_pure segsA _ _ _ (fun w Hw => c5_pure nW st nx CST XGL HCST HXGL HCSTS HCSTD (fun X : AA => X) G2 A Kc rho rho1 rho1 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 (slink4_refl (aa_geom A) ua L rho1 RD1) DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (ETLb A Kc rho rho3 a tp G2 HUS HKc HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
Qed.
End OKEP.
End SpineMallocSecE4P.

(* [comment removed for export] *)
Module SpineMallocR15.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sv"; "eval"; "sprop"; "SAlu"; "SLit"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "phase"; "entryR"; "gh_new"; "ph0"; "frozen"; "ghosts"; "mlink"; "FAb"; "committed"; "ph_f"; "ph_u"; "releasedp"; "rlink"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "iff"; "@Corelib.Init.Datatypes"; "list"; "bool"; "length"; "true"; "nil"; "prod"; "option"; "pair"; "None"; "Some"; "cons"; "nat"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "of_nat"; "le"; "lt"; "ge"; "ltb"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "cs_free_array"; "cs_mapped_free_array"; "class_state"; "aa_cache_inited"; "aa_geom"; "ag_spacebeg"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cst_of"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7"; "popfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP"; "ph_quiet"; "pbase"; "ph_set"; "PF"; "PU"; "ph_get"; "pord"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocR13"; "phL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocR14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6"; "backT"; "exitT"; "popT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vMFA"; "beg1"; "beg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocR15.ASMP"; "pieceT"; "fillT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocR15"; "phFin"; "phUF3"; "phU3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineMallocR12"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3"; "phK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4"; "ph_setcnt"; "ph_setri"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv InvLaws PrimCredit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineMallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocR14.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Section FAMAP.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
SfVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let cs : class_state := ltac2:(tb__ "0|0|
S47VA;S3eQ40S1Vrb;PcA2A2A2").
Variable LFm : axst.
Let CFM : axst := cFm LFm.
Hypothesis W_fm : ltac2:(tb__ "0|0|
S1bS21S8S4bVCFM;A1A1S23A3").
Hypothesis D_fm : ltac2:(tb__ "0|4|
S1bS26S25S20S25S3S3A2M0A1M1S20S5A1M2A2M3A1S6cS4bVLFm;A1S4bVCFM;A1A2S29G3S27G1G2S2aG0S27S3S3S70S6S6bS5fS7Z40000A1A3A4S24G0A1A3S24S5A1A4A2A3").

Lemma famap_restate : ltac2:(tb__ "0|0|
SeS0S20S3dQ40A1A1SaS30S38Vcs;A1S2dZ4S2cS2eS22SbS37Vcs;A1A2A1S10VA;Vrb;A2A2A2A2VTR;ScS9SdVA;VKc;Vrb;Vtp0;Vmd0;R5A6VCFM;R4R3A5R2A2VTR;ScS9SdVA;VKc;Vrb;Vtp0;Vmd0;R6A6VLFm;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;Fph;").
Proof.
  intros ph r tp Q HLT HT. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_restate A Kc rb tp0 md0 TR KIT LFm (ax_S CFM) _ _ ph r tp Q W_fm D_fm ltac:(apply Pos.eqb_refl)); [|exact HT].
  intros tr md (HFz & HGh & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  exact (rup_val A rb r CF PF HGh HLT).
Qed.
End FAMAP.

Definition phU3 : phase := ph_set PU 3 ph0.
Definition phUF3 : phase := ph_set PF 3 phU3.
Definition phFin (ph : phase) (new k : Z) : phase := ltac2:(tb__ "0|0|
S73S72S71S56Vph;Vnew;A2Vk;A2A1A1").

Section ASMP.
Variables CST XGL : list (Z * Z).
Variable PFam : ltac2:(tb__ "0|0|
S36S40S20S25S4aS4eA2A1F_;F_;").
Variables (W : list ulink) (st : ustop).

Variables (LP CP2C RU LF0 LFm CFM RF LF1 : axst) (LJP XLP LZP LJM XLM LZM E3P : axst).
Notation AInvS := (AInvA segs).
Hypothesis HWs : ltac2:(tb__ "0|0|
S1bS45Vst;S44A3S1bS20S43A1VW;S24S43A1A3F_;").

Definition headT : Prop := ltac2:(tb__ "0|1|
S36S40S0S20S3dQ40A1A1M0S34SaSaOF_;F_;S46R5R1A2S41R6A1S0S0G0SaSfRcRaR9R8VW;Vst;R4A7S49RdRbA2S0RaScS9SdRfReRdRcRbS11A6VCP2C;R1R5A5R4A2Fr';F_;R9ScS9SdReRdRcRbRaS11A6VLP;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition pieceT (p : piece) (eb : sv) (C0 RX : axst) : Prop := ltac2:(tb__ "0|6|
S36S40S0S20S3dQ40M0A1A1M1S34SaSaOF_;F_;S46R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7SeS1bS2bS54Vp;R1A2U0A3S55Vp;R2A2S4fR3A1S0S12RdR1A2S13R10ReR2A3S1bSbS3eG0S4R3Veb;A2A2S50R11RfVp;A3A3F_;F_;Fr;S1cS2fS2cS3cS3bRfA1A1M2Z100000000A2S50RfRdVp;A3M3A2S1cS2fS2cG3Z40000M4A2S2cG2Z2000000000A2A2S1bSbS33G3Z10000A2Z0A3A2A2G1S34S14R12R10RfReR8R2R1A7S31S6dR2R3A2M5G4A2F_;Fmd;Ftp;G1S34S14R13R11R10RfS51Vp;U1R9A3R2R1A7S31G5Z8000A2F_;Fmd;Ftp;S0G1SaS0G1R12ScS9SdR17R16R15R14R13S51Vp;U3RdA3A6VRX;R2R1A5R3A2Ftp';Fr';R11ScS9SdR16R15R14R13R12RcA6VC0;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;F_;Fph;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition midT : Prop := ltac2:(tb__ "0|4|
S36S40S0S20S3dQ40M0A1A1M1S34SaSaOF_;F_;S46R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S49RaR8A2SeS0G1SaS47RfS3eG0S1RdPcA2A2A2S39S1dS30S38R1A1S2dZ4M2S2cS2eS22SbS37R1A1A2A1S10R10ReA2A2A2A2A1S0RdScS9SdR12R11R10RfReR7A6M3VLF0;R1R5A5R4A2Fr';F_;S30S38R2A1S2dG2S2cS2eS22SbS37R2A1A2A1S10R11RfA2A2A2A2S0ReScS9SdR13R12R11R10RfR8A6VLFm;R1R6A5R5A2Fr';F_;RdScS9G3VRU;R6R5A5R4A2F_;F_;Tcs;FQ;Ftp;Fr;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition fmT : Prop := ltac2:(tb__ "0|2|
S36S40S0S20S3dQ40M0A1A1M1S34SaSaOF_;F_;S46R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S49RaR8A2SeS0G1SaS47RfS3eG0S1RdPcA2A2A2S39S30S38R1A1S2dZ4S2cS2eS22SbS37R1A1A2A1S10R10ReA2A2A2A2RcScS9SdR11R10RfReRdR6A6VCFM;R5R4A5R3A2RdScS9SdR12R11R10RfReR7A6VLFm;R6R5A5R4A2F_;F_;Tcs;FQ;Ftp;Fr;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition runT (C L : axst) : Prop := ltac2:(tb__ "0|2|
S36S40S0S20S3dQ40A1A1M0S34SaSaOF_;F_;S46R5R1A2S41R6A1SeS0G0SaS0R8ScS9SdRdRcRbRaR9R5A6M1VL;R1R3A5R2A2Fr';R8ScS9G1VC;R4R3A5R2A2F_;FQ;Ftp;Fr;Fph;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition fillT (LH LJ : axst) : Prop := ltac2:(tb__ "0|7|
S36S40S0S20S3dQ40M0A1A1M1S34SaSaOF_;F_;S46R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S49RaR8A2SeS4fR1A1SbS6eS1cS2fZ0R2A2S2fR2S10RfRdA2A2A2S1aR10ReS56R5R3A2S6fS9S2ReA1A2R2A5SbS1cS2fS2cS15R12R10A2M2S2dZ4M3S2eS22SbS37S47R12S3eG0S1R10PcA2A2A2A1A2A1M4A2A2R1A2S30R1S2cG2S2dG3S2cG4S10R12R10A2M5A2A2A2A2A2S1dS1bS26S3dQ8A1M6A1R5R2A1S28G6A1A3A1F_;Fz;F_;F_;Fm;Fi;S0G1SaS0RdScS9SdR12R11R10RfReS56R7G5A2A6VLJ;R1R3A5R2A2Fr';RdScS9SdR12R11R10RfReR7A6VLH;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").

Hypothesis H_head : headT.
Hypothesis H_pu : ltac2:(tb__ "0|0|
S65S53S60VCP2C;VRU;A4").
Hypothesis H_mid : midT.
Hypothesis H_fm : fmT.
Hypothesis H_pf : ltac2:(tb__ "0|0|
S65S52S61VCFM;VRF;A4").
Hypothesis H_run : runT RF LF1.
Hypothesis H_fillP : fillT LF0 LJP.
Hypothesis H_fillM : fillT LF1 LJM.
Hypothesis H_popP : ltac2:(tb__ "0|0|
S5eVW;Vst;VLJP;VXLP;S5aA5").
Hypothesis H_popM : ltac2:(tb__ "0|0|
S5eVW;Vst;VLJM;VXLM;S5aA5").
Hypothesis H_exitP : ltac2:(tb__ "0|0|
S5dVW;Vst;VXLP;VLZP;S57S5fS58S59A8").
Hypothesis H_exitM : ltac2:(tb__ "0|0|
S5dVW;Vst;VXLM;VLZM;S57S5bS58S59A8").
Hypothesis H_backP : ltac2:(tb__ "0|0|
S5cVCST;VXGL;VPFam;VW;Vst;VE3P;VLZP;A7").
Hypothesis H_backM : ltac2:(tb__ "0|0|
S5cVCST;VXGL;VPFam;VW;Vst;VE3P;VLZM;A7").

Lemma pop_tail : ltac2:(tb__ "0|5|
S4aS4aS4aS4aS3S66R5R4A2S5eVW;Vst;R5R4S5aA5S5dVW;Vst;R5R4S57R3S58S59A8S5cVCST;VXGL;VPFam;VW;Vst;VE3P;R5A7S36S40S0S20S3dQ40M0A1M1A1M2S34SaSaOF_;F_;S46R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S49RaR8A2SeS1bS21S3aRcA1S23A3S4fR2A1S1bS21S16S18R3A1A1S23A3S3eG0S1RdPcA2A2SbS48R1A1SbS47R11R2A2S39S2eS22SbS37R1A1A2A1SbS10R13R11A2SbS38R3A1SbS1eS1bS21S19S17RaA1A1S23A3S2fS2dZ4M3S2cR3R2A2A2R1A2A2S0S12R15R1A2S13R18R16R2A3S1bG1S4R3R1eA2S3fG0S21SbL_;S32R5S2dG3S2cR7R6A2A2A2S2cR5Z40000A2R5X21x2A2A3F_;F_;Fr;S0G2S20S35A1S34SdR1bR1aR19R18R17S67R10R8S63RbA1A3R4R3R2R1AaS1cS62S9S64R1cRcA2M4R5R4R2A5S42VCST;VXGL;R1cG4S2R1aA1S2R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;S36S0G2S0R17ScS9S6aVW;Vst;R4R1bR3A5VE3P;R1R2A5S4dS9S4cR3R2VPFam;R4R1bA2A5A2FrX;Ftp';Frho';FA';S0G2R16ScS9SdR1bR1aR19R18R17R10A6R24R2R1A5S4dS9S4cR13R18VPFam;R1bR1aA2A5A2Ftp;Fr;F_;F_;F_;F_;Tmfa;Tnew;Tnf;Tcs;Tc;Tnv;F_;F_;F_;FphX;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;F_;F_;F_;F_;Fe24;FLZ;FXL;FLJ;FLH;").
Proof.
  intros LH LJ XL LZ e24 HFI HPO HEX HBA A Kc rb tp0 md0 TR KIT HKc rho HE PF phX Hini PQ PCU nv c cs nf new mfa HARM HE24 HREB HPOP r tp.
  pose proof (P_csR A rb tp0 md0 W st rho HE PF) as (X1 & X2 & X3 & X5 & X6 & X7 & LP' & HIDS). cbn zeta in X1, X2, X3, X5, X6, X7, LP', HIDS. fold nv c cs nf new in X1, X2, X3, X5, X6, X7, LP', HIDS.
  destruct (pop_geo A rb tp0 md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & _). fold nv c cs nf new mfa in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0.
  set (k := kchunks c) in *. set (fP := faP c cs) in *.

  apply (HFI A Kc rb tp0 md0 TR KIT HKc rho HE PF phX PQ).
  { intros i m Hi HR z Hz. apply (P_HDEF A rb tp0 md0 W st rho HE PF (phL phX i) m); [exact HARM | exact HR | exact Hz]. }
  intros r1.

  apply (HPO A Kc rb tp0 md0 TR KIT HKc rho HE (phL phX new) (conj eq_refl (conj eq_refl eq_refl)) fP).
  - intros i m Hi HR idx Hidx. apply (P_HSRC A rb tp0 md0 W st rho HE PF (phK (phL phX new) i) m); [reflexivity | cbn [ph_pop phK]; fold nv c k in Hi; clear -Hi K1; lia | exact HR | exact Hidx].
  - fold nv c k. rewrite LP'. clear -KN NF0. lia.
  - rewrite LP'. clear -MF1 MF2 N4. lia.
  - intros _. unfold gh_nf. fold nv c cs nf new. rewrite LP'. cbn [ph_fill phL]. clear -NF0 N4. lia.
  - exact HIDS.
  - fold nv c cs k. rewrite LP'. exact X1.
  - fold nv c k. exact (P_HSRCP A rb tp0 md0 W st rho HE PF).
  - intros r2.

    apply (HEX A Kc rb tp0 md0 TR KIT HKc rho HE (phK (phL phX new) k) (conj eq_refl (conj eq_refl eq_refl))).
    + intros _. unfold gh_nf. fold nv c cs nf new. cbn [ph_fill phK phL]. clear -NF0 N4 MF1 MF2. lia.
    + exact Hini.
    + intros r' HFz HGh. exact (P_HRIv A rb tp0 md0 W st rho HE PF e24 r' HFz HGh (HE24 r' HFz HGh)).
    + fold nv c cs k. exact X2.
    + fold nv c cs. intros x Hx. rewrite X1 in Hx. apply HIDS. rewrite <- (firstn_skipn (Z.to_nat (nf + new - k)) fP). apply in_or_app. right. exact Hx.
    + intros r3.

      apply (HBA A Kc rb tp0 md0 TR KIT rho HE (phFin phX new k)).
      * intros r' t tr md HJ. exact (proj1 (HREB r' t tr md HJ)).
      * intros r' t tr md HJ. exact (proj2 (HREB r' t tr md HJ)).
      * fold nv c cs k. exact X2.
      * exact (HPOP (refillA A c)).
Qed.

Theorem refill_populate : ltac2:(tb__ "0|3|
S36S40S0S20S3dQ40M0A1A1M1SaSaOF_;F_;S46R4R1A2S41R5A1S1bS21S3aR7A1S23A3S4dS9S4cR6R5VPFam;R8R7A2A5SaS0S34SfRbR2R8R1VW;Vst;R9A7S49RcR3A2SeS1eS1bSeR1S69A3S1bSeR1S68A3A2S3eG0S1R6PcA2A2SbS48R1A1SbS47R11R2A2S39S1fS1bSeR5S68A3S30S38R1A1S2dZ4S2cS2eS22SbS37R1A1A2A1S10R12R9A2A2A2A2A2S0G1S20S35A1S34SdR17R16ReR14RdS67RaS10R17ReA2S63R7A1A3R4R3R2R1AaS1cS62S9S64R18R8A2M2R5R4R2A5S42VCST;VXGL;R18G2S2RfA1S2R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;S36S0G1S0RaScS9S6aVW;Vst;R4RdR3A5VE3P;R1R2A5S4dS9S4cR3R2VPFam;R4RdA2A5A2FrX;Ftp';Frho';FA';S0S34S0SfReR3RbR2VW;Vst;RcA7RbScS9SdRfReR4RcR3S11A6VLP;R2RcA5R7A2F_;Fr';Fmd0;Frb;F_;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp TR KIT HKc Hini Q HREB HPOP rb md0 r0 HE.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (H_head A Kc rb tp md0 TR KIT HKc rho r0 tp Q HE). intros PF r1.
  set (nv := bv_unsigned (rw rb 12%positive)) in *. set (c := cls_of nv) in *. set (cs := cst_of A nv) in *.
  destruct (pop_geo A rb tp md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  fold nv c cs in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0, FAr.
  destruct (pop_credit A rb tp md0 W st rho HE PF) as (CR & _). fold nv c cs in CR.
  assert (G12 : ag_spacebeg (aa_geom A) mod 65536 = 0) by (unfold cfacts in CF; cbn zeta in CF; destruct CF as (_ & _ & _ & _ & _ & (X & _) & _); exact X).
  assert (MU18 : cs_mapped_user cs mod 262144 = 0) by (unfold cfacts in CF; cbn zeta in CF; fold nv c cs in CF; destruct CF as (_ & _ & (X & _) & _); exact X).

  apply (H_pu A Kc rb tp md0 TR KIT HKc rho HE ph0 eq_refl eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
  - intros r HFz HGh. exact (beg1_val A rb r CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh).
  - cbn [pbase]. unfold U0, region_beg, kRegionSize. fold nv c cs. split; [clear -C1 AU0; lia|]. split; [clear -C1 MU1; lia|].
    rewrite Z.add_mod, (Z.add_mod (ag_spacebeg (aa_geom A))), G12 by (clear; lia).
    destruct (proj1 (Z.mod_divide (cs_mapped_user cs) 262144 ltac:(clear; lia)) MU18) as [q Hq]. rewrite Hq.
    replace (c * 2 ^ 32) with (c * 65536 * 65536) by (clear; lia). replace (q * 262144) with (q * 4 * 65536) by (clear; lia). rewrite !Z_mod_mult. reflexivity.
  - intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF ph0 t md HM) as X. cbn [ph0 ph_u ph_f committed revealedp Nat.leb] in X.
    destruct (cs_mapped_free_array cs <? _); clear -X CR; lia.
  - intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF (ph_set PU 1 ph0) t md HM) as X. cbn [ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
    destruct (cs_mapped_free_array cs <? _); clear -X CR; lia.
  - intros r2 tp2. fold phU3.
    apply (H_mid A Kc rb tp md0 TR KIT HKc rho HE PF phU3 r2 tp2 Q); cbn zeta; fold nv c cs.
    +
      intros NLT r3.
      apply (pop_tail LF0 LJP XLP LZP vMFA H_fillP H_popP H_exitP H_backP A Kc rb tp md0 TR KIT HKc rho HE PF phU3 Hini (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) eq_refl).
      * right. fold nv c cs. clear -NLT. lia.
      * intros r HFz HGh. fold nv c cs. replace (cs_mapped_free_array cs <? _) with false by (symmetry; apply Z.ltb_ge; clear -NLT; lia).
        destruct HGh as (_ & _ & Q222 & _). fold nv c cs in Q222. exact Q222.
      * fold nv c. apply (HREB rb md0 HE PF phU3 (or_introl eq_refl)). cbn zeta. fold nv c cs. split; [intros X; discriminate X | intros X; contradiction].
      * exact HPOP.
    +
      intros LT r3.
      apply (H_fm A Kc rb tp md0 TR KIT HKc rho HE PF phU3 r3 tp2 Q LT).
      pose proof (P_newZ A rb) as ENZ. fold nv c cs in ENZ.
      destruct (RefillModelP.P_famap c cs _ C1 (proj1 (entry_pure A rb tp md0 W st rho HE PF)) (proj2 (proj2 (proj2 (entry_pure A rb tp md0 W st rho HE PF))))
                  ltac:(rewrite ENZ; exact LT)) as (_ & FCM).
      pose proof (facap_room c C1) as FRM.
      apply (H_pf A Kc rb tp md0 TR KIT HKc rho HE phU3 eq_refl I (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
      * intros r HFz HGh. exact (beg2_val A rb r CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh).
      * cbn [pbase]. unfold F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c cs.
        split; [clear -C1 NF0 MF1; lia|]. split; [clear -C1 FCM FRM; lia|].
        rewrite Z.add_mod, (Z.add_mod (ag_spacebeg (aa_geom A) + c * 2 ^ 32)), (Z.add_mod (ag_spacebeg (aa_geom A))), G12 by (clear; lia).
        destruct (proj1 (Z.mod_divide (cs_mapped_free_array cs) 262144 ltac:(clear; lia)) MF0) as [q Hq]. rewrite Hq.
        replace (c * 2 ^ 32) with (c * 65536 * 65536) by (clear; lia). replace (q * 262144) with (q * 4 * 65536) by (clear; lia). rewrite !Z_mod_mult. reflexivity.
      * intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF phU3 t md HM) as X. cbn [phU3 ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
        fold nv c cs in CR. replace (cs_mapped_free_array cs <? _) with true in CR by (symmetry; apply Z.ltb_lt; exact LT). clear -X CR. lia.
      * intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF (ph_set OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP.PF 1 phU3) t md HM) as X. cbn [phU3 ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
        fold nv c cs in CR. replace (cs_mapped_free_array cs <? _) with true in CR by (symmetry; apply Z.ltb_lt; exact LT). clear -X CR. lia.
      * intros r4 tp4. fold phUF3.
        apply (H_run A Kc rb tp md0 TR KIT HKc phUF3 r4 tp4 Q). intros r5.
        apply (pop_tail LF1 LJM XLM LZM e24M H_fillM H_popM H_exitM H_backM A Kc rb tp md0 TR KIT HKc rho HE PF phUF3 Hini (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) eq_refl).
        -- left. reflexivity.
        -- intros r HFz HGh. fold nv c cs. replace (cs_mapped_free_array cs <? _) with true by (symmetry; apply Z.ltb_lt; exact LT).
           destruct HGh as (_ & _ & Q222 & _). fold nv c cs in Q222. unfold e24M, vMFA. cbn [eval]. rewrite Q222. apply bv_eq.
           rewrite add_val, !u64_lit by (clear -NF0 MF1 MF2; lia). rewrite Z.mod_small by (clear -NF0 MF1 MF2; lia). reflexivity.
        -- fold nv c. apply (HREB rb md0 HE PF phUF3 (or_intror eq_refl)). cbn zeta. fold nv c cs. split; [intros _; exact LT | intros _; reflexivity].
        -- exact HPOP.
Qed.
End ASMP.
End SpineMallocR15.

(* [comment removed for export] *)
Module SpineMallocU1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "nat"; "list"; "prod"; "cons"; "pair"; "nil"; "bool"; "true"; "andb"; "false"; "app"; "Some"; "option"; "None"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "valuation"; "cell"; "rm"; "mkCell"; "rw"; "ss_objs"; "eval"; "smatch"; "sstate"; "sv_eqb"; "DUnknown"; "c_off"; "c_val"; "c_width"; "mkObj"; "sprop"; "ss_facts"; "swf"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "eqb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocU1"; "JU"; "cell_inb"; "O_arrF"; "O_pcmZ"; "arr_okb"; "cU0"; "NU2"; "O_arr0"; "cU2"; "cnt_spec"; "idx1"; "idx2"; "kU1"; "kU2"; "perm_okb"; "sU1"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_cache_inited"; "ag_thread"; "topG"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "pc_base"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "nobj"; "addobjs"; "nxt"; "keepn"; "selobjs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "KcA"; "UStopLeOrPc"; "mem_keptA"; "ustop"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.RebuildI"; "initA"; "ZI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5"; "rho_after"; "posts_conv"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "w_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "CLS30"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "PCE"; "entryR"; "frozen"; "mlink"; "ph0"; "rmlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "rhoM_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "cfacts"; "rigids"; "BASEF"; "BASEO";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocU1.UJ"; "JU"; "umem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "JK"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.RebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.RebuildI.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition NU0 : list carve_spec := ltac2:(tb__ "0|7|
S5S4S4S4S16S0A2M0S0A2M1S3S4S4S0S2A2M2S16A2M3A1M4A2M5S6G1G4S6G0S0S6S16S0S52Z4M6A4Z8A4S5G3S6G2S16S6S0S2G6U4A4S17Z0A1A4S7G3A1A3A4S7G5A1A3").
Definition O_pcmZ : sobj := ltac2:(tb__ "0|3|
S8dS52Z4M0Z8S5S4S4S0S2A2M1S16A2M2S6G1S16S6S0S2G0U4A4S17Z0A1A4S7G2A1A3A4").
Definition cnt_spec : list (Z * nat * sv) := ltac2:(tb__ "0|1|
S4fS0S4S4S0S2A2M0S16A2S0S6G0S16S6S0S2S2aZd0S2cZ50R1A2A2U4A4S17Z0A1A4Lc;S7cA4").
Definition NU1 : list carve_spec := ltac2:(tb__ "0|4|
S5S4S4S4S16S0A2M0S0A2M1S3S4S4S0S2A2S16A2A1M2A2M3S6G1G2S6G0S0S6S16S0S63Z120A4Zad0A4S3fA4S7G3A1A3").
Definition O_arr0 : sobj := carved vT 288 2768 cnt_spec.
Definition O_arrF (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S26S63S17Z120A1S17Zad0A1Vcells;S22A5").
Definition NU2 : list carve_spec := ltac2:(tb__ "0|7|
S5S4S4S4S16S0A2M0S0A2M1S3S4S4S0S2A2M2S16A2M3A1M4A2M5S6G1G4S6G0S0S6S16S0S52Z0M6A4Z4A4S5G3S6G2S16S6S0S2G6U4A4S17G6A1A4S7G3A1A3A4S7G5A1A3").
Lemma NU2_objs : ltac2:(tb__ "0|0|
S11S3S15A1S4fS8fS15S8eS3cA4S5S15S51S7S15A1A3A3"). Proof. reflexivity. Qed.

Definition cU0 (E : axst) : axst := ltac2:(tb__ "0|0|
S55VE;S5S15S39S7S15A1A3S56VE;A1A3").

Definition idx1 (E : axst) : list nat := ltac2:(tb__ "0|2|
ScS2S50U0S35S54VE;A1M0U3A2M1A2S5S2S35G0U2A2S5S2G1S5S2S35G0U1A2S7S2A1A3A3A3A3").
Definition sU1 (E : axst) : axst := ltac2:(tb__ "0|0|
S58VE;S40VE;A1A2").
Definition kU1 (E : axst) : axst := ltac2:(tb__ "0|0|
S57S45VE;A1S35S54VE;A1U2A2A2").
Definition cU1 (E : axst) : axst := ltac2:(tb__ "0|0|
S55S42VE;A1S5S15S3dS7S15A1A3S56VE;A1A3").
Definition kU2 (E : axst) : axst := ltac2:(tb__ "0|0|
S57VE;S35S54VE;A1U1A2A2").
Definition cU2 (E : axst) : axst := ltac2:(tb__ "0|0|
S55S43VE;A1S5S15S51S7S15A1A3S56VE;A1A3").

Definition idx2 (E : axst) : list nat := ltac2:(tb__ "0|2|
ScS2S50U0S35S54VE;A1M0U2A2M1A2S5S2S35G0U1A2S5S2G1S7S2A1A3A3A3").
Definition eU (E : axst) : axst := ltac2:(tb__ "0|1|
S58S3eVE;A1M0S41G0A1A2").

Definition perm_okb (n : nat) (idxs : list nat) : bool := ltac2:(tb__ "0|0|
SaSaS74Vidxs;A1S47S2S2S92R1Vn;A2Li;Vidxs;A3A2S47S2S2S48S2S91R1A1Vidxs;A3Li;S50U0Vn;A2A3A2").
Lemma perm_okb_sound : ltac2:(tb__ "0|0|
S2S3S2A1S11S8S44R2R1A2S9A3S10S11S8S74R2A1S9A3S10S2S46S2R1R3A3S6cR2R5A2F_;Fi;S2S6cR1R4A2S46S2R2R4A3F_;Fi;A2A2F_;Fidxs;Fn;").
Proof.
  intros n idxs H. unfold perm_okb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [exact H1|]. split.
  - intros i Hi. apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) H2 i Hi).
  - intros i Hi. pose proof (proj1 (forallb_forall _ _) H3 i ltac:(apply in_seq; lia)) as X.
    apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj.
Qed.

Definition cell_inb (off w v : Z) (cells : list cell) : bool := ltac2:(tb__ "0|0|
S48S19S19SaSaS21S23R1A1S17Voff;A1A2S2eS25R1A1Vw;A2A2S21S24R1A1S17Vv;A1A2A2Lcl;Vcells;A3").
Definition arr_okb (cells : list cell) : bool := ltac2:(tb__ "0|2|
S47S0S0SaSaS37S2aZd0S2cZ50R1A2M0A2Z4M1Z0Vcells;A4S37S2aZd4G0A2G1S65R1A1Vcells;A4A2S37S2aZd8G0A2Z8S64R1A1Vcells;A4A2Lc;S7cA3").
Lemma cell_inb_In : ltac2:(tb__ "0|0|
S0S0S0S3S19A1S11S8S37R4R3R2R1A4S9A3S46S19S1bS17R5A1R4S17R3A1A3R2A3F_;Fcells;Fv;Fw;Foff;").
Proof.
  intros off w v cells H. unfold cell_inb in H. apply existsb_exists in H as ([o w' v'] & Hin & E). cbn [c_off c_width SymState.c_val] in E.
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply sv_eqb_sound in E1. apply sv_eqb_sound in E3. apply Z.eqb_eq in E2.
  subst o w' v'. exact Hin.
Qed.
Lemma arr_okb_In : ltac2:(tb__ "0|2|
S3S19A1S0S11S8S3aR2A1S9A3S10S2bZ1R2A2S2bR2Z1eA2A2S10S46S19S1bS17S2aZd0S2cZ50R3A2M0A2A1Z4M1S17Z0A1A3R4A3S10S46S19S1bS17S2aZd4G0A2A1G1S17S65R3A1A1A3R4A3S46S19S1bS17S2aZd8G0A2A1Z8S17S64R3A1A1A3R4A3A2A2F_;F_;Fc;Fcells;").
Proof.
  intros cells c H Hc. unfold arr_okb in H. pose proof (proj1 (forallb_forall _ _) H c (proj2 (In_CLS30 c) Hc)) as X. cbv beta in X.
  apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
  split; [exact (cell_inb_In _ _ _ _ X1)|]. split; [exact (cell_inb_In _ _ _ _ X2) | exact (cell_inb_In _ _ _ _ X3)].
Qed.

Lemma uninit_frame : ltac2:(tb__ "0|5|
S4aS18S3S2fQ40A1A1S33S7aS7bR4R3R2R1A5S11S8S4cR5A1SbA3S4dS4bR6A1A1S0S68S7bS1aR6A1A2S69S10S0S0S10S2bZ1R2A2S2bR2Z1eA2A2S10S2bS2aS2aR5Zd0A2S2cZ50M0R3A2A2M1R2A2S2dR2S2aG1G0A2A2A2S11SeS2fQ8M2A1M3A1M4R5R3A1SdG3S31G2Z0A2A2A3F_;F_;Fz;Fc;S0S10S2bS2aR3Za80A2R1A2S2dR1S2aR3Zc60A2A2A2S13G3G3S11G4R4R3A1SdG3R1A2A3Lb;A2F_;Fz;A2Tm0;TT;F_;F_;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 HA Hini T m0. pose proof HA as (HG & _ & _ & HRest & _).
  destruct HRest as (_ & _ & Hprim & _ & _ & _ & _ & HTH & _). destruct Hprim as (_ & _ & _ & PC).
  assert (MT : forall z, T <= z < T + 0x1000 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  split.
  - intros c z Hc Hz. pose proof (PC c Hc) as P4. unfold class_repr in P4.
    destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CN & _).
    destruct (CN Hini) as [_ FL]. fold T in FL. rewrite <- MT by (clear -Hz Hc; lia). exact (FL z Hz).
  - intros z Hz. destruct HTH as [_ TH2]. fold T in TH2. destruct (TH2 z Hz) as [b Hb]. exists b. rewrite <- MT by (clear -Hz; lia). exact Hb.
Qed.

Section UJ.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Let T : Z := ag_thread (aa_geom A).

Definition umem (s : bool) (m0 m : bview) : Prop := ltac2:(tb__ "0|6|
S8OLs;Vs;S10S0S12S60VT;R1A2M0A1S11SeS2fQ8A1M1A1M2Vm;R2A1M3Vm0;R2A1A3F_;Fz;S10S0G0S12S11G2G3SfG1A1A3A1F_;Fz;S0S10S2bZ1R1A2S2bR1Z1eA2A2S10S66Vm;S67S2aS2aVT;Zd0A2S2cZ50R2A2A2M4U4M5Z0A3A2S10S66Vm;S67S2aG4Z4A2G5S65R2A1A3A2S66Vm;S67S2aG4Z8A2U8S64R2A1A3A2A2A2F_;Fc;A2A2S0S11G2Vm;R1A1Vm0;R1A1A3Fz;X8x2").
Definition JU (s : bool) : jpredA := ltac2:(tb__ "0|2|
S18S3S2fQ40A1A1S3S34A1S33S10S7fVrb;R4A2S10VKc;R2R1A2S10S80VA;Vrb;Vtp0;Vmd0;S81R3R1A7S10S8cVs;S68S32S1aVrb;A1M0A2S68S32S1aR4A1M1A2A3S82G0G1A2A2A2A2A2Lmd;Ltr;Ltp;Lr;").

Lemma JU_K : ltac2:(tb__ "0|0|
S8S90VKc;S8bR1A1A2Fs;").
Proof. intros s r t tr md (_ & HK & _). exact HK. Qed.

Lemma JU_stable : ltac2:(tb__ "0|0|
S8S1S5eVKc;A1S93PdcR2A2S77S32R3S8bR4A1A3F_;F_;Fn;Fs;").
Proof.
  intros s n HKc Hn r r' tp tr md md' Hag Hme (HF & HK & HM & HR & HRM).
  destruct Hag as (Hw & Hl & Hm).
  assert (Erm : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  assert (Hlt : forall i, (i < 220)%positive -> rw r' i = rw r i) by (intros i Hi; symmetry; apply Hw; lia).
  destruct Hme as ((mat' & ->) & Hpaid & _).
  split; [|split; [|split; [|split]]].
  - destruct HF as [F1 F2]. split; [intros i Hi; rewrite (Hlt i Hi); exact (F1 i Hi) | intros l; rewrite <- (Hl l); exact (F2 l)].
  - rewrite with_vm_backing_with_vm. apply HKc. exact HK.
  - unfold mlink in *. cbn zeta in *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|].
    exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. rewrite Hpaid. exact M10.
  - rewrite Erm. exact HR.
  - rewrite Erm. exact HRM.
Qed.
End UJ.

Lemma pc_base_val : ltac2:(tb__ "0|0|
S4aS18S18S85R3R2A2S86R4R3R2A3S11S0S30Q40S1eR3S52A2A2S7dR5R4A2A3F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & _) & _).
  destruct RG as (_ & _ & E151 & _ & _ & _ & _ & E158).
  unfold pc_base, vT, V_CLS, PCE. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
  rewrite (Z.mod_small (_ * 80)) by lia. rewrite (Z.mod_small (_ + 208)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma vT_val : ltac2:(tb__ "0|0|
S4aS18S18S85R3R2A2S86R4R3R2A3S11S0S30Q40S1eR3S63A2A2S4dS4bR5A1A1A3F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & _) & _).
  destruct RG as (_ & _ & E151 & _). unfold vT. cbn [eval]. rewrite E151. apply u64_lit. lia.
Qed.

Section UENTRY.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.
Variable E3 : axst.
Hypothesis SK3 : ltac2:(tb__ "0|1|
S11S3S4S4S16S16A2S16A2M0A1S4fS15G0S8aS1dS61VE3;A1A1A4S4fS15G0S8aScS15S88VW;A1S5S15S51S5S15S53S7S15A1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S49S27S87VW;Vst;A2S28S61VE3;A1A1A3").
Hypothesis WU0 : ltac2:(tb__ "0|0|
S11S8S29S61S3bVE3;A1A1A1S9A3").

Lemma uninit_entry : ltac2:(tb__ "0|2|
S4aS5aS18S18S3S2fQ40M0A1A1S71S11S5dVst;S5bA3S11S3S59A1VW;S7S59A1A3F_;S11S8S4cR7A1SbA3S11S0S84R8S30G0S1cR6PcA2A2A2Z0A3S76S32S89VW;Vst;R9R8R7A5VE3;R6R5R4A6S10S7eRaR7R6S70S72R5A1A1M1VW;Vst;R8A7S76S32S36RaR9R7R6G1SbA6S3bVE3;A1R7R6R5A6A2F_;F_;F_;F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w HW Hini Hcnt H.
  pose proof H as [HsmA [Hag HJ]]. pose proof Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN, HB.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite <- E12 in Hcnt. set (nv := bv_unsigned (rw rhoE 12%positive)) in *.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (Hnv : nv <= 64512).
  { pose proof (proj1 (Forall_forall _ _) HFa (SPUle (SVar 12) (SLit 64512)) (XF3 (SPUle (SVar 12) (SLit 64512)) ltac:(unfold BASEF; apply in_or_app; right; unfold F_gen; cbn; tauto))) as F.
    cbn [holds eval] in F. rewrite u64_lit in F by lia. exact F. }
  assert (HE : entryR A rhoE tp (cfg_model (w_cfg w)) W st rho).
  { unfold entryR. split; [exact Hag|]. split; [exact HA|]. split; [exact Htp|]. split; [exact HU|]. split; [exact HB|]. split; [lia|]. split; [exact Htop|]. split; [exact Hcnt|].
    exact (MI_ivs_wf segs _ _ (proj1 (proj2 HsmA))). }
  split; [exact HE|].
  assert (HFz : frozen rhoE rhoE) by (split; intros; reflexivity).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (pc_base_val A rhoE rhoE CF RG) as EB. pose proof (vT_val A rhoE rhoE CF RG) as ET.
  unfold cfacts in CF. cbn zeta in CF. fold nv in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  set (c := cls_of nv) in *. set (T := ag_thread (aa_geom A)) in *.
  assert (PCr : PCE A rhoE = T + 208 + 80 * c) by (unfold PCE; fold nv c T; clear; lia).
  destruct (uninit_frame A rhoE tp _ HA Hini) as (FZ & _). fold T in FZ.

  assert (Ha : SPA segs (JU A Kc rhoE tp (cfg_model (w_cfg w)) false) E3 rhoE tp w).
  { split; [exact HsmA|]. unfold JU. split; [exact HFz|]. split; [exact HK|]. split; [|split; [intros z; reflexivity | intros a _; reflexivity]].
    unfold mlink, ph0, committed, revealedp, subU, subF. cbn [ph_u ph_f Nat.leb].
    repeat (split; [reflexivity|]). exists []. cbn [app length Z.of_nat]. split; [reflexivity|]. split; [intros p []|]. split; [lia | lia]. }

  destruct (arm_base_disj A rhoE tp _ W st rho (ax_S E3) [O_pcc0; O_st] rhoE _ HW HE HFz Hsm SK3 XF3) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNc : obj_range rhoE oc = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { rewrite (obj_range_skel rhoE oc O_pcc0 SKc). unfold O_pcc0. rewrite obj_range_mk by (clear; lia). rewrite EB, PCr. f_equal; clear; lia. }
  assert (RNs : obj_range rhoE os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel rhoE os O_st SKs). unfold O_st. rewrite obj_range_mk by (clear; lia). rewrite ET. reflexivity. }
  apply (SPA_carve_list segs _ rhoE E3 tp w NU0 (nxt E3) Ha WU0).
  - apply Pos.le_refl.
  - unfold NU0. apply Forall_cons; [|apply Forall_nil].
    rewrite EB, PCr. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 T1; lia|]. split; [clear -C1 T1 T2 TG; lia|].
    split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
    assert (BY : forall off, 4 <= off < 8 -> rd_of segs (rm rhoE) (Z_to_bv 64 (T + 208 + 80 * c + off)) = Some (Z_to_bv 8 0)).
    { intros off Hoff. pose proof (FZ c (T + 208 + 80 * c + off) C1 ltac:(clear -Hoff; lia)) as Hb. rewrite view_in in Hb by (clear -Hoff C1 T1 T2 TG; lia). exact Hb. }
    split.
    { intros off Hoff. eapply wok_rd_off_image2; [| |exact (BY off Hoff)]; [clear -Hoff C1 T1 T2 TG; lia | clear -Hoff C1 TI; lia]. }
    split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
    apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval].
    rewrite (enc_bytes_zero_nth 4 (Z_to_bv 64 0) j ltac:(apply u64_lit; clear; lia) Hj).
    replace (T + 208 + 80 * c + 4 + Z.of_nat j) with (T + 208 + 80 * c + (4 + Z.of_nat j)) by (clear; lia). apply BY. clear -Hj. lia.
  - cbn [map carve_obj NU0]. unfold carved. apply Forall_cons; [|apply Forall_nil]. rewrite obj_range_mk by (clear; lia). rewrite EB, PCr.
    rewrite EO. apply Forall_app. split.
    + apply BZ. left. fold T. clear -C1. lia.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1; lia.
  - cbn [map carve_obj NU0 pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.
End UENTRY.

Section USTEPS.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variables (W : list Iface.ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S11S5dVst;S5bA3S11S3S59A1VW;S7S59A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S7eVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis Hini : aa_cache_inited A = false.
Notation JUp := (JU A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let T : Z := ag_thread (aa_geom A).

Lemma u_nums : ltac2:(tb__ "0|3|
S10S10S2bZ1Vc;A2S2bVc;Z1eA2A2S10S2bZ1000M0VT;A2S10S2bS2aVT;G0A2M1S4eS4bVA;A1A1M2A2S10S2bG2Z7fffff800000A2S10S14S2bG1Z10000A2S2bZ643000VT;A2A2S11S0S7dVA;Vrb;A2S2aS2aVT;Zd0A2S2cZ50Vc;A2A2A3A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c T in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  split; [exact C1|]. split; [exact T1|]. split; [exact T2|]. split; [exact TG|]. split; [exact TI|]. unfold PCE. fold nv c T. lia.
Qed.

Lemma u_release1 : ltac2:(tb__ "0|3|
S20S3S15A1M0S18S3S2fQ40A1A1S3S34A1M1S6dS33S33S11G0S1dR8A1ScS15R7S5S15S51S5S15S39S7S15A1A3A3M2A3A3S1fS32R7R9S6G1S6eR5S6fR4R3A2A4A4S36VA;VKc;Vrb;Vtp0;Vmd0;SbR8R7R6R3AaS36VA;VKc;Vrb;Vtp0;Vmd0;SbS75R9G2R6A3R8R7R4AaF_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;FK;FS;").
Proof.
  intros S K r tp tr ms md mdJ HO Hsm (HFz & HK & HM & HR & HRM).
  destruct u_nums as (C1 & T1 & T2 & TG & TI & PCr).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (pc_base_val A rb r CF RG) as EB. rewrite PCr in EB.
  destruct HE as (_ & HA & _). destruct (uninit_frame A rb tp0 md0 HA Hini) as (FZ & _). fold T in FZ.
  set (r3 := rho_absorb r [O_pcc0; O_pcmZ] ms).
  assert (RC : obj_range r O_pcc0 = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { unfold O_pcc0. rewrite obj_range_mk by lia. rewrite EB. f_equal; lia. }
  assert (RM : obj_range r O_pcmZ = (T + 208 + 80 * c + 4, T + 208 + 80 * c + 8)).
  { unfold O_pcmZ, carved. rewrite obj_range_mk by lia. rewrite EB. reflexivity. }

  assert (EZ : forall k j, (j < k)%nat -> nth j (enc_bytes k (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0) by (intros k j Hj; apply enc_bytes_zero_nth; [apply u64_lit; lia | exact Hj]).
  assert (M3 : forall z, T + 208 + 80 * c <= z < T + 208 + 80 * c + 8 -> view segs (rm r3) z = Some (Z_to_bv 8 0)).
  { intros z Hz. destruct (Z_lt_dec z (T + 208 + 80 * c + 4)) as [LT|GE].
    - destruct (absorb_obj r S tr ms md K [O_pcc0; O_pcmZ] O_pcc0 Hsm HO (or_introl eq_refl)) as (_ & AS & _).
      destruct (AS (mkCell (SLit 0) 4 (SLit 0)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb (Z.to_nat (z - (T + 208 + 80 * c))) ltac:(cbn [c_width]; lia)).
      cbn [ob_base O_pcc0 eval c_off SymState.c_val c_width] in ASb. rewrite soff_lit_small in ASb by lia. fold (eval r pc_base) in ASb. rewrite EB in ASb.
      rewrite EZ in ASb by lia.
      unfold r3. rewrite view_in by lia. replace z with (T + 208 + 80 * c + 0 + Z.of_nat (Z.to_nat (z - (T + 208 + 80 * c)))) at 1 by lia. exact ASb.
    - destruct (absorb_obj r S tr ms md K [O_pcc0; O_pcmZ] O_pcmZ Hsm HO (or_intror (or_introl eq_refl))) as (_ & AS & _).
      destruct (AS (mkCell (SLit 4) 4 (SLit 0)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb (Z.to_nat (z - (T + 208 + 80 * c + 4))) ltac:(cbn [c_width]; lia)).
      cbn [ob_base O_pcmZ carved eval c_off SymState.c_val c_width] in ASb. rewrite soff_lit_small in ASb by lia. fold (eval r pc_base) in ASb. rewrite EB in ASb.
      rewrite EZ in ASb by lia.
      unfold r3. rewrite view_in by lia. replace z with (T + 208 + 80 * c + 4 + Z.of_nat (Z.to_nat (z - (T + 208 + 80 * c + 4)))) at 1 by lia. exact ASb. }
  unfold JU. split; [exact HFz|]. split; [exact HK|]. split; [exact HM|]. split.
  - cbn [umem] in HR |- *. intros z. destruct (Z_le_dec (T + 208 + 80 * c) z) as [H1|H1]; [destruct (Z_lt_dec z (T + 208 + 80 * c + 8)) as [H2|H2]|].
    + rewrite (M3 z (conj H1 H2)). symmetry. apply (FZ c z C1). lia.
    + unfold r3. rewrite view_absorb_out; [exact (HR z)|]. intros o [<-|[<-|[]]]; [rewrite RC | rewrite RM]; cbn [fst snd]; lia.
    + unfold r3. rewrite view_absorb_out; [exact (HR z)|]. intros o [<-|[<-|[]]]; [rewrite RC | rewrite RM]; cbn [fst snd]; lia.
  - apply (rmlink_absorb _ r [O_pcc0; O_pcmZ] ms HRM). intros o [<-|[<-|[]]]; [rewrite RC | rewrite RM]; cbn [fst snd]; unfold IMG_LO, IMG_HI; lia.
Qed.

Lemma u_release2 : ltac2:(tb__ "0|3|
S20S3S15A1M0S3S19A1S18S3S2fQ40A1A1S3S34A1M1S6dS33S33S11G0S1dR9A1ScS15R8S5S15S38R7A1S7S15A1M2A3A3A3S11S8S3aR8A1S9A3S1fS32R8RbS6G1S6eR6S6fR5R4A2A4A4S36VA;VKc;Vrb;Vtp0;Vmd0;SbR9R8R7R4AaS36VA;VKc;Vrb;Vtp0;Vmd0;S9S75RaS5S15S38RbA1G2A3R7A3R9R8R5AaF_;F_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;Fcells;FK;FS;").
Proof.
  intros S K cells r tp tr ms md mdJ HO HOK Hsm (HFz & HK & HM & HR & HRM).
  destruct u_nums as (C1 & T1 & T2 & TG & TI & PCr).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (vT_val A rb r CF RG) as ET. fold T in ET.
  set (r3 := rho_absorb r [O_arrF cells] ms).
  assert (RA : obj_range r (O_arrF cells) = (T + 288, T + 2768)).
  { unfold O_arrF. rewrite obj_range_mk by lia. rewrite ET. reflexivity. }
  destruct (absorb_obj r S tr ms md K [O_arrF cells] (O_arrF cells) Hsm HO (or_introl eq_refl)) as (_ & AS & AP & _).
  cbn [ob_base O_arrF ob_cells ob_dflt] in AS, AP. rewrite ET in AS, AP.
  assert (CELL : forall off w v, In (mkCell (SLit off) (Z.of_nat w) (SLit v)) cells -> 0 <= off < 4096 -> cell_ok (view segs (rm r3)) (mkACell (T + off) w v)).
  { intros off w v Hin Hoff j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (AS _ Hin) as (B1 & B2 & ASb). cbn [c_off c_width SymState.c_val] in B1, B2, ASb. rewrite soff_lit_small in B1, B2, ASb by lia.
    unfold obj_lo_of, obj_hi_of in B1, B2. cbn [ob_lo ob_hi O_arrF] in B1, B2. rewrite !soff_lit_small in B1, B2 by lia.
    specialize (ASb j ltac:(rewrite Nat2Z.id; exact Hj)). rewrite Nat2Z.id in ASb. cbn [eval] in ASb.
    unfold r3. rewrite view_in by lia. exact ASb. }
  unfold JU. split; [exact HFz|]. split; [exact HK|]. split; [exact HM|]. split.
  - cbn [umem] in HR |- *. fold T. split; [|split].
    + intros z Hz. unfold r3. rewrite view_absorb_out; [exact (HR z)|]. intros o [<-|[]]. rewrite RA. cbn [fst snd]. exact Hz.
    + intros z Hz. unfold ZI in Hz. destruct (AP (or_introl eq_refl) (z - T)) as [x Hx].
      { unfold obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi O_arrF]. rewrite !soff_lit_small by lia. lia. }
      replace (T + (z - T)) with z in Hx by lia. unfold r3. rewrite view_in by lia. rewrite Hx. discriminate.
    + intros c' Hc'. destruct (arr_okb_In cells c' HOK Hc') as (I1 & I2 & I3).
      split; [|split].
      * replace (T + 208 + 80 * c') with (T + (208 + 80 * c')) by lia. apply (CELL _ 4%nat); [exact I1 | lia].
      * replace (T + 208 + 80 * c' + 4) with (T + (212 + 80 * c')) by lia. apply (CELL _ 4%nat); [exact I2 | lia].
      * replace (T + 208 + 80 * c' + 8) with (T + (216 + 80 * c')) by lia. apply (CELL _ 8%nat); [exact I3 | lia].
  - apply (rmlink_absorb _ r [O_arrF cells] ms HRM). intros o [<-|[]]. rewrite RA. cbn [fst snd]. unfold IMG_LO, IMG_HI. lia.
Qed.

Lemma u_rebuild : ltac2:(tb__ "0|1|
S18S3S2fQ40A1A1S3S34A1S33S36VA;VKc;Vrb;Vtp0;Vmd0;S9R4R3R2R1AaS10S7aS32S5fVA;A1M0R5R4R2A5S5cVCST;VXGL;VA;G0S1aVrb;A1S1aR5A1A6A2F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md (HFz & HK & HM & HR & HRM).
  pose proof HE as (_ & HA & _). pose proof HA as (_ & _ & _ & _ & HM0 & _ & HB0).
  unfold mlink in HM. cbn zeta in HM. unfold ph0, committed, revealedp, subU, subF in HM. cbn [ph_u ph_f Nat.leb] in HM.
  destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & _ & M10).
  assert (Etp1 : tp1 = []).
  { destruct tp1 as [|p tp1']; [reflexivity|]. exfalso. destruct (M8 p (or_introl eq_refl)) as [_ [[X _]|[X _]]]; discriminate X. }
  subst tp1. cbn [app length Z.of_nat] in M7, M10. subst tp.
  cbn [umem] in HR. fold T in HR. destruct HR as (L1 & L2 & L3).
  apply (init_rebuild CST XGL HCST HXGL A rb r tp0 tp0 md0 md HA Hini).
  - exact L1.
  - intros z Hz. pose proof (L2 z Hz) as D. change (exists b, view segs (rm r) z = Some b). destruct (view segs (rm r) z) as [b|]; [exists b; reflexivity | contradiction].
  - exact HRM.
  - exact L3.
  - apply (model_inv_fields A (initA A) tp0 md0 md); try reflexivity; try assumption. clear -M10. lia.
  - eapply bandtp_mono; [|exact HB0]. intros z _ Hd. change (view segs (rm r) z <> None). change (view segs (rm rb) z <> None) in Hd.
    assert (D : ZI T z \/ ~ ZI T z) by (unfold ZI; clear; lia).
    destruct D as [D|D]; [exact (L2 z D) | rewrite (L1 z D); exact Hd].
Qed.

Lemma rhoM_init : ltac2:(tb__ "0|0|
S18S18S1S11S2fQ40A1S1cS83S5fVA;A1S6aR3R2A2A2R1A2S1cS83VA;R3A2R1A2A3Fi;Fr;Frho0;").
Proof. intros rho0 r i. reflexivity. Qed.

Lemma JG_init : ltac2:(tb__ "0|0|
S18S3S2fQ40A1A1S3S34A1S33S36VA;VKc;Vrb;Vtp0;Vmd0;S9R4R3R2R1AaS89VW;Vst;S5fVA;A1VKc;S6aVrho;R5A2R5R4R3R2A9F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HJ. pose proof HJ as (HFz & HK' & _).
  pose proof HE as (Hag & HA & Htp & HU & HB & Hnv & Htop & Hcnt & _). destruct Hag as (Hagw & Hagl & Hagm). destruct HFz as [Fw Fl].
  assert (RWid : forall i, (i < GW)%positive -> rw r i = rw (rhoM_of A rho) i).
  { intros i Hi. rewrite <- (Fw i) by (unfold GW in Hi; lia). symmetry. apply Hagw. exact Hi. }
  split.
  - split; [|split].
    + intros i Hi. rewrite rhoM_init. symmetry. exact (RWid i Hi).
    + intros l. unfold rhoM_of. rewrite rl_rho_sets. cbn [rho_after rl]. rewrite <- Fl. rewrite <- Hagl. unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
    + intros a. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
  - assert (R12 : rw r 12%positive = rw rb 12%positive) by (rewrite (RWid 12%positive) by (unfold GW; lia); apply Hagw; unfold GW; lia).
    split; [|split; [exact HK'|split; [|split; [|split; [|split]]]]].
    + exact (proj1 (u_rebuild r tp tr md HJ)).
    + unfold tp_ok in *. rewrite (RWid 24%positive) by (unfold GW; lia). rewrite (Hagw 24%positive) by (unfold GW; lia). exact Htp.
    + unfold unwind_stopJ. destruct W as [|l W']; [exact I|]. destruct st; [exact I|]. discriminate (HW eq_refl).
    + cbn [eval]. rewrite R12. fold nv. exact HB.
    + cbn [eval]. rewrite R12. fold nv. lia.
    + unfold top_high in *. rewrite (RWid 10%positive) by (unfold GW; lia). rewrite (RWid V_DEPTH) by (unfold GW, V_DEPTH; lia).
      rewrite (Hagw 10%positive) by (unfold GW; lia). rewrite (Hagw V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop.
Qed.

Lemma posts_init : ltac2:(tb__ "0|1|
S4aS5aS3S4S62S79A2A1F_;F_;S6bVCST;VXGL;R1A3S18S3S2fQ40A1A1S71S5cVCST;VXGL;VA;S5fVA;A1M0S1aVrho;A1S1aR3A1A6S78S32S73S6aVrho;R4A2R3R6G0VKc;A2R2A6S78S32S73Vrho;R4R7VA;VKc;A2R3A6F_;F_;Fw;Ftp;Fr;F_;FPFam;").
Proof.
  intros PFam HPF r tp w HM0 H.
  apply (HPF A (initA A) Kc rho r tp tp w); [repeat split; reflexivity | exact HM0 | | exact H].
  intros A' HCK c' Hc' Hn Hf. exact (HCK c' Hc' Hn Hf).
Qed.
End USTEPS.
End SpineMallocU1.

(* [comment removed for export] *)
Module SpineCallocR13.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "sub"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "SAlu"; "SLit"; "sprop"; "SVar"; "ss_next"; "ss_objs"; "rw"; "ss_facts"; "ss_lenient"; "cell"; "swf"; "SPBranch"; "SPNot"; "eval"; "mkCell"; "rm"; "smatch"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "list"; "bool"; "true"; "nil"; "false"; "option"; "Some"; "app"; "prod"; "pair"; "None"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineCallocR13.FILL"; "JRfill"; "phL"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "FAb"; "zoneR"; "entryR"; "frozen"; "ghosts"; "mkPh"; "ph_f"; "ph_u"; "rlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "LV0"; "LV2"; "GR"; "LV3"; "keepn"; "LNX"; "HINT_au"; "HINT_k"; "O_cell"; "O_pcm"; "O_ri"; "vAU"; "vNEW"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "ALU_XOR"; "BC_LTU"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineCallocR13"; "O_fcell"; "faend_e"; "F_lt"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineCallocR12.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition faend_e : sv := SAlu ALU_ADD fa_e2 need_e.
Definition O_fcell : sobj := ltac2:(tb__ "0|1|
S52S4dS23S18S1dS10Z0A1Z4M0SfS59S12S4bA1S10G0A1A3A3S27S18A1A3A2").
Definition F_lt : sprop := ltac2:(tb__ "0|0|
S1aS5bS12S4aA1S56A3").

Section FILL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S43VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let S : Z := Size c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).
Let au : Z := cs_allocated_user cs.
Let new : Z := gh_new A rb.

Variable ph : phase.
Hypothesis PQ : ph_quiet ph.
Definition phL (i : Z) : phase := ltac2:(tb__ "0|0|
S46S48Vph;A1S47Vph;A1Vi;Z0S28S28A6").
Lemma phL0 : phL 0 = ph.
Proof.
  destruct PQ as (Q1 & Q2 & Q3 & Q4).
  transitivity (mkPh (ph_u ph) (ph_f ph) (ph_fill ph) (ph_pop ph) (ph_cnt ph) (ph_ri ph)); [unfold phL; rewrite Q1, Q2, Q3, Q4; reflexivity | symmetry; apply ph_eta].
Qed.

Hypothesis HDEF : ltac2:(tb__ "0|3|
S21S74S1S6Z0R2A2S6R2Vnew;A2A2S49VA;Vrb;S39R3A1S75S35S1eVrb;A1A2R2A5S21S1S6S5S41VA;Vrb;A2M0S7Z4M1Vnf;A2A2R1A2S8R1S5G0S7G1S5Vnf;Vnew;A2A2A2A2A2S3S0S29S3aQ8A1M2A1R5R2A1S2eG2A1A3A1F_;Fz;F_;F_;Fm;Fi;").

Lemma fill_nums : ltac2:(tb__ "0|7|
S1S1S6Z20VS;A2S6VS;Z10000A2A2S1S6Z0M0Vau;A2S1S6S5Vau;S7Vnew;VS;A2A2Ze0000000M1A2S1S1S6Z4M2Vnew;A2S6Vnew;Z2001A2A2S1S6G0Vnf;A2S1S6S7G2S5Vnf;Vnew;A2A2S5Z20000000M3Z8004M4A2A2S1S6G0S41VA;Vrb;A2M5A2S1S8S5S5S5G5G3A2G4A2Z8A2SbZ2Z3eA2A2S1S0S21G5S5S5S72S71VA;A1A1M6S7Vc;Z100000000A2A2G1A2A3S1S1S6Z1Vc;A2S6Vc;Z1eA2A2S1S6Z100080000000G6A2S6S5S5G6Z2000000000A2Z1000A2Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  destruct (new_nums A rb CF PF) as (N1 & N2 & N3 & N4 & _ & N6 & _ & N8 & N9 & N10 & _). cbn zeta in N1, N2, N3, N4, N6, N8, N9, N10. fold nv c cs in N1, N2, N3, N4, N6, N8, N9, N10. fold S nf au new in N1, N2, N3, N4, N6, N8, N9, N10.
  unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. clear; lia. }
  split; [exact N1|]. split; [clear -N2; lia|]. split; [clear -N3 N6; lia|]. split; [exact N4|]. split; [exact N8|]. split; [clear -N4 N9 N10; lia|].
  split; [rewrite FAr; clear -C1 G13; lia|]. split; [rewrite FAr; clear -C1 G13 G14 TG; lia|]. split; [exact FAr|]. split; [exact C1|]. split; [exact G13|]. clear -G14 TG; lia.
Qed.

Definition JRfill (i : Z) : jpredA := ltac2:(tb__ "0|3|
SeS24S3aQ40M0A1M1A1S24S5dA1S5cS1S40VA;VKc;Vrb;Vtp0;Vmd0;S39Vi;A1R4R3R2R1AaS1S0G1S15R4S4aA2S3bG0S5Vi;Z1M2A2A2A3S1S0G1S15R4S4bA2S3bG0S5Vau;S7Vi;VS;A2A2A2A3S0G1S15R4S4dA2S3bG0S5S41VA;Vrb;A2S7Z4S9S9S5Vnf;Vnew;A2G2A2Vi;A2A2A2A2A3A2A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JRfill_K : ltac2:(tb__ "0|0|
S21S73VKc;S38R1A1A2Fi;").
Proof. intros i r t tr md [H _]. exact (JR_K A Kc rb tp0 md0 _ r t tr md H). Qed.
Lemma JRfill_stable : ltac2:(tb__ "0|0|
S21S22S0S25S63S4fR1A2S26A3S37S35R2S38R3A1A3F_;Fn;Fi;").
Proof.
  intros i n Hn r r' tp tr md md' Hag Hme (HJ & H0 & H2 & H3). apply Pos.leb_le in Hn. unfold LNX in Hn.
  split; [|split; [|split]].
  - eapply (JR_stable A Kc rb tp0 md0 (phL i) n HKc); [unfold GR; lia | exact Hag | exact Hme | exact HJ].
  - destruct Hag as (Hw & _). rewrite <- (Hw LV0) by (unfold LV0; lia). exact H0.
  - destruct Hag as (Hw & _). rewrite <- (Hw LV2) by (unfold LV2; lia). exact H2.
  - destruct Hag as (Hw & _). rewrite <- (Hw LV3) by (unfold LV3; lia). exact H3.
Qed.

Lemma zone_fill : ltac2:(tb__ "0|3|
S21S21S6Z0R2A2S2S42VA;Vrb;S39S5R3Z1M0A2A1R2A4S4S42VA;Vrb;S39R3A1R2A4S1S6S5S41VA;Vrb;A2S7Z4M1S9S9S5Vnf;Vnew;A2G0A2R3A2A2A2M2R2A2S8R2S5G2G1A2A2A2A2A2F_;Fz;Fi;").
Proof.
  intros i z Hi. unfold zoneR, phL. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. unfold gh_nf. fold nv c cs nf new.
  split.
  - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; try (left; tauto).
    + destruct (Z.eq_dec i 0) as [->|NZ]; [right; clear -H; lia|].
      destruct (Z_lt_dec z (FAb A rb + 4 * (nf + new - 1 - i) + 4)) as [L|G]; [right; clear -H L; lia | left; right; right; right; right; left; clear -H G NZ Hi; lia].
  - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H]; try tauto.
    + right; right; right; right; left. clear -H Hi. lia.
    + right; right; right; right; left. clear -H Hi. lia.
Qed.

Lemma fill_release : ltac2:(tb__ "0|3|
S20S24ScA1M0SeS24S3aQ40A1A1S24S5dA1M1S6aS5cS5cS21S1S6Z0R1A2S8R1Vnew;A2A2S0G0S14RaA1S2bScR9S23ScS60S27ScA1A3M2A3A3S1fS35R9RbS2dG1S6bR7S6cR6R5A2A4A4S38R4RaR9R8R5A5S40VA;VKc;Vrb;Vtp0;Vmd0;S39S5R5Z1A2A1S3fRbG2R8A3RaR9R6AaF_;F_;F_;F_;Fi;FmdJ;Fmd;Fms;Ftr;Ftp;Fr2;FK;FSt;").
Proof.
  intros St K r2 tp tr ms md mdJ i Hi HO Hsm ((HFz & HGh & HKc' & HM & HR & HRM) & H0 & H2 & H3).
  destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  set (r3 := rho_absorb r2 [O_fcell] ms). set (Ci := FAb A rb + 4 * (nf + new - 1 - i)) in *.
  assert (CiR : FAb A rb + 4 * nf <= Ci /\ Ci + 4 <= FAb A rb + 4 * (nf + new)) by (unfold Ci; clear -Hi; lia).
  assert (RC : obj_range r2 O_fcell = (Ci, Ci + 4)).
  { unfold O_fcell, O_cell. rewrite obj_range_mk by (clear; lia). cbn [eval]. rewrite H3, u64_lit by (clear -CiR N5 N6 N7 N8; lia). f_equal; clear; lia. }
  set (m2 := view segs (rm r2)) in *. set (m3 := view segs (rm r3)).
  assert (AIS : 0 <= au + i * S /\ au + i * S <= 3758096384) by (clear -Hi N1 N2 N3; nia).
  assert (M3C : cell_ok m3 (mkACell Ci 4 ((au + i * S) / 16))).
  { intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (absorb_obj r2 St tr ms md K [O_fcell] O_fcell Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SAlu ALU_SRL (SVar LV2) (SLit 4))) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_fcell O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H3, soff_lit_small, u64_lit in ASb by (clear -CiR N5 N6 N7 N8; lia).
    assert (EV : alu64 ALU_SRL (rw r2 LV2) (Z_to_bv 64 4) = Z_to_bv 64 ((au + i * S) / 16)).
    { apply bv_eq. rewrite srl_val, H2, !u64_lit.
      - change (4 mod 64) with 4. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity.
      - pose proof (Z.div_pos (au + i * S) 16 ltac:(clear -AIS; lia) ltac:(clear; lia)). pose proof (Z.div_le_upper_bound (au + i * S) 16 (2 ^ 30) ltac:(clear; lia) ltac:(clear -AIS; lia)). clear -H H1. lia.
      - clear -AIS. lia. }
    rewrite EV in ASb. unfold m3. rewrite view_in by (clear -CiR N5 N6 N7 N8 Hj; lia). fold Ci in ASb. replace (Ci + 0 + Z.of_nat j) with (Ci + Z.of_nat j) in ASb by (clear; lia). exact ASb. }
  assert (AGR : forall z, ~ (Ci <= z < Ci + 4) -> m3 z = m2 z).
  { intros z Hz. unfold m3, r3. apply view_absorb_out. intros o [<-|[]]. rewrite RC. cbn [fst snd]. exact Hz. }
  pose proof (zone_fill i) as ZI. fold Ci in ZI.
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HKc'|].
  split; [unfold mlink, phL in HM |- *; cbn [ph_u ph_f] in HM |- *; exact HM|].
  split.
  - fold m3. unfold rlink in HR |- *. fold m2 in HR. destruct HR as (L1 & L2 & L3 & _).
    split; [intros z Hz; rewrite AGR by (intros X; apply Hz; apply (ZI z ltac:(clear -Hi; lia)); right; exact X); apply L1; intros X; apply Hz; apply (ZI z ltac:(clear -Hi; lia)); left; exact X|].
    split.
    { intros z Hz. apply (ZI z ltac:(clear -Hi; lia)) in Hz.
      assert (D : Ci <= z < Ci + 4 \/ ~ (Ci <= z < Ci + 4)) by (clear; lia).
      destruct D as [D|D].
      - pose proof (M3C (Z.to_nat (z - Ci)) ltac:(cbn [c_w]; clear -D; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X.
        replace (Ci + Z.of_nat (Z.to_nat (z - Ci))) with z in X by (clear -D; lia). rewrite X. discriminate.
      - rewrite (AGR z D). destruct Hz as [Hz|Hz]; [exact (L2 z Hz) | contradiction]. }
    split.
    { intros j Hj. cbn [ph_fill phL] in Hj |- *. unfold gh_nf. fold nv c cs nf new au S.
      destruct (Z.eq_dec j i) as [->|NE]; [exact M3C|].
      eapply cell_ok_agree_range; [|apply (L3 j); cbn [ph_fill phL]; clear -Hj NE; lia].
      cbn [c_addr c_w]. unfold gh_nf. fold nv c cs nf new. intros z Hz. apply AGR. change (Z.of_nat 4) with 4 in Hz. unfold Ci. clear -Hz Hj NE. lia. }
    cbn [ph_pop ph_cnt ph_ri phL]. split; [intros x Hx; exfalso; clear -Hx; lia|]. split; intros X; discriminate X.
  - apply (rmlink_absorb _ r2 [O_fcell] ms HRM). intros o [<-|[]]. rewrite RC. cbn [fst snd]. right. unfold IMG_HI. clear -CiR N5 FAr C1 G13. lia.
Qed.

Variable F : nat.
Variables (CL0 : axst) (LB LX : leafA) (nobF : nat) (s_bk : wsub).
Let CL1 : axst := cL1 CL0.
Hypothesis SK_l : ltac2:(tb__ "0|1|
S0S24S2cS2cSdSdA2SdA2M0A1S66ScG0S67S14S30VCL0;A1A1A4S66ScG0S67S2bScS77VW;A1S23ScS6eS23ScS6fS23ScS53S23ScS54S27ScA1A3A3A3A3A3A4A3").
Hypothesis XX_l : ax_X CL0 = [].
Hypothesis XF_l : ltac2:(tb__ "0|0|
S69S11S76VW;Vst;A2S16S30VCL0;A1A1A3").
Hypothesis NX_l : ltac2:(tb__ "0|0|
S0S25S64S13S30VCL0;A1A1S4fA2S26A3").
Hypothesis W_l1 : ltac2:(tb__ "0|0|
S0S25S19S30VCL1;A1A1S26A3").
Hypothesis R_l1 : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z418d4S23S21Z418e0S27S21A1A3A3VCL1;S26A5S2aG0S23S32VLB;S23S32VLX;S27S32A1A3A3A2A3").
Hypothesis LN_l1 : ltac2:(tb__ "0|0|
S0S25S17S30VCL1;A1A1S28A3").
Hypothesis OB_b : ltac2:(tb__ "0|1|
S0S24ScA1S14S30S31VLB;A1A1A1M0S2bScS65ScVnobF;G0A3S23ScS60S27ScA1A3A3A3").
Hypothesis OB_x : ltac2:(tb__ "0|1|
S0S24ScA1S14S30S31VLX;A1A1A1M0S2bScS65ScVnobF;G0A3S23ScS60S27ScA1A3A3A3").
Hypothesis ENT_bk : ltac2:(tb__ "0|0|
S0S25S34S4eS31VLB;A1VnobF;A2VCL0;Vs_bk;A3S26A3").
Hypothesis SID_bk : ltac2:(tb__ "0|0|
S0S25S3eVs_bk;S4cA2S26A3").
Hypothesis S_bk0 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S4aA2SfS57S12S4aA1S10Z1A1A3A3").
Hypothesis S_bk2 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S4bA2SfS57S12S4bA1S12S70A1A3A3").
Hypothesis S_bk3 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S4dA2SfS57S61SfS58SfS5aS12S4aA1S10ZffffffffffffffffA1A3S10Z2A1A3A3A3").
Hypothesis FB_b : ltac2:(tb__ "0|0|
S68S11S62S16S30S31VLB;A1A1A1A3").
Hypothesis FB_x : ltac2:(tb__ "0|0|
S68S11S1bS62A1S16S30S31VLX;A1A1A1A3").

Lemma faend_val : ltac2:(tb__ "0|0|
SeS44Vrb;R1A2S45VA;Vrb;R2A3S0S21S3cQ40S1cR3S61A2A2S5S41VA;Vrb;A2S7Z4S5Vnf;Vnew;A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (need_val A rb r CF PF HGh) as NV. fold nv c cs nf new in NV.
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). fold nv c in E158.
  unfold faend_e. cbn [eval]. rewrite add_val. fold (eval r need_e). rewrite NV.
  unfold fa_e2, rb_e, vSB, V_CLS. cbn [eval]. rewrite !add_val, sll_val, E155, E158, !u64_lit by (clear -C1 G13 G14; lia).
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ * 2 ^ 32)) by (clear -C1; lia).
  rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by (clear -C1 G13 G14; lia). rewrite (Z.mod_small (_ + _ * 2 ^ 32 + 3758096384)) by (clear -C1 G13 G14; lia).
  rewrite Z.mod_small by (clear -C1 G13 G14 N4 N5 N6; lia). rewrite FAr. clear; lia.
Qed.

Lemma fill_carve : ltac2:(tb__ "0|0|
S21SeS24S3aQ40A1A1S5fS1S6Z0R4A2S8R4Vnew;A2A2S36S35S38R5A1VCL0;R4R3R2A6S36S35S38R6A1VCL1;R5R4R3A6F_;F_;Fw;Ftp;Fr;Fi;").
Proof.
  intros i r tp w Hi H. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof H as [HsmA HJ]. pose proof HJ as ((HFz & HGh & _ & _ & HR & _) & H0 & H2 & H3).
  set (Ci := FAb A rb + 4 * (nf + new - 1 - i)) in *.
  assert (CiR : FAb A rb + 4 * nf <= Ci /\ Ci + 4 <= FAb A rb + 4 * (nf + new)) by (unfold Ci; clear -Hi; lia).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & _ & _ & _ & _ & _ & (T1 & T2 & TI & PS1) & TB).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CL0) [O_pcc0; O_st; O_pcm; O_ri] r _ HW HE HFz Hsm SK_l XF_l) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r ori O_ri SKr) in RNr.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
  assert (E3 : bv_unsigned (eval r (SVar LV3)) = Ci) by (cbn [eval]; rewrite H3; apply u64_lit; clear -CiR N5 N6 N7 N8; lia).
  apply (SPA_carve_unk segs (JRfill i) r CL0 tp w (SVar LV3) (SLit 0) (SLit 4) LNX H W_l1 ltac:(apply Pos.eqb_eq in NX_l; rewrite NX_l; apply Pos.le_refl));
    rewrite ?E3, ?soff_lit_small by (clear; lia).
  - clear; lia.
  - clear; lia.
  - clear -CiR N5 N7; lia.
  - clear -CiR N5 N6 N7 N8; lia.
  - replace (Ci + 0) with Ci by (clear; lia). rewrite EO. apply Forall_app. split.
    + apply BZ. right; left. rewrite kSpaceSize_val. rewrite FAr in CiR. clear -CiR N5 N6 C1. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
        unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; rewrite FAr in CiR; clear -CiR N5 N6 C1 T1 PS1; lia.
  - intros a Ha. assert (Ha64 : 0x643000 <= a < 2 ^ 64) by (rewrite FAr in CiR; clear -Ha CiR N5 N6 C1 G13 G14; lia).
    pose proof (HDEF i (view segs (rm r)) ltac:(clear -Hi; lia) HR a ltac:(clear -Ha CiR; lia)) as D. rewrite view_in in D by (clear -Ha64; lia).
    pose proof (wok_rd_off_image (rm r) a) as WK.
    destruct (rd_of segs (rm r) (Z_to_bv 64 a)) as [x|]; [exact (WK x Ha64 eq_refl) | contradiction].
  - unfold xwords_clear. rewrite XX_l. intros rr y j [].
Qed.

Lemma fill_iter : ltac2:(tb__ "0|1|
S21SeS24S3aQ40A1A1S5eS1S6Z0R4A2S8R4Vnew;A2A2S8S5R5Z1M0A2Vnew;A2SeVTR;S36S35S38S5R7G0A2A1VCL0;R1R5A5R4A2Fr';F_;S0S21S5R6G0A2Vnew;A3SeVTR;S36S35S40VA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S4eS31VLX;A1VnobF;A2R1R6A5R5A2Fr';F_;VTR;S36S35S38R7A1VCL0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;").
Proof.
  intros i r tp Q Hi HKb HKx. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  apply (tr_pre Kc TR KIT (SPA segs (JRfill i) CL1 r tp)); [intros w Hw; exact (fill_carve i r tp w Hi Hw)|].
  apply (tr_run Kc TR KIT F [0x418d4; 0x418e0] CL1 [LB; LX] (JRfill i) r tp Q (JRfill_K i) (JRfill_stable i (ss_next (ax_S CL1)) eq_refl) R_l1 LN_l1).
  intros L r2 HL Hag.
  set (JREL := (fun r' t tr md => JRp (phL (i + 1)) r' t tr md /\ rw r' LV0 = rw r2 LV0 /\ rw r' LV2 = rw r2 LV2) : jpredA).
  assert (REL : forall (LL : leafA), ss_objs (ax_S (la_state LL)) = firstn nobF (ss_objs (ax_S (la_state LL))) ++ [O_fcell] ->
            forall w, SPA segs (JRfill i) (la_state LL) r2 tp w ->
              exists r3, SPA segs JREL (keepn (la_state LL) nobF) r3 tp w).
  { intros LL HO [tr [ms md]] Hw. exists (rho_absorb r2 [O_fcell] (vms md tp ms)).
    apply (SPA_unobj_J (JRfill i) JREL r2 (la_state LL) _ [O_fcell] tp tr ms md HO Hw).
    intros Hsm HJ. split; [|split; reflexivity].
    exact (fill_release (ax_S (la_state LL)) _ r2 tp tr (vms md tp ms) (vmd md) md i Hi HO Hsm HJ). }
  destruct HL as [<-|[<-|[]]].
  -
    apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FB_b) as BF. unfold F_lt in BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 < new /\ rw r2 LV0 = Z_to_bv 64 (i + 1) /\ rw r2 LV2 = Z_to_bv 64 (au + i * S))).
    { intros w [_ ((HFz & HGh & _) & H0 & H2 & _)]. split; [|split; [exact H0 | exact H2]].
      destruct HGh as (_ & _ & _ & _ & _ & _ & _ & _ & Q228 & _). fold new in Q228.
      unfold branch_taken, bv_ltu, vNEW in BF. cbn [eval] in BF. rewrite H0, Q228, !u64_lit in BF by (clear -Hi N4; lia). apply Z.ltb_lt in BF. exact BF. }
    intros (Hlt & H0 & H2).
    apply (tr_cut Kc TR KIT valuation _ _ Q (REL LB OB_b)). intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRfill (i + 1)) CL0 (rho_sub r3 s_bk) tp)); [|exact (HKb Hlt _)].
    intros w Hw. apply (SPA_entails_J JREL (JRfill (i + 1)) _ CL0 s_bk r3 tp w ENT_bk); [|exact Hw].
    intros (HJ & E0 & E2). pose proof (rho_sub_agree s_bk GR r3 SID_bk) as AGs. pose proof HJ as (HFz & HGh & _).
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
    assert (AIS : 0 <= au + i * S /\ au + (i + 1) * S <= 3758096384) by (clear -Hi Hlt N1 N2 N3; nia).
    split; [|split; [|split]].
    + eapply (JR_stable A Kc rb tp0 md0 (phL (i + 1)) GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    + cbn [rho_sub rw]. rewrite S_bk0. cbn [eval]. rewrite E0, H0. apply bv_eq. rewrite add_val, !u64_lit by (clear -Hi N4; lia). rewrite Z.mod_small by (clear -Hi N4; lia). clear; lia.
    + cbn [rho_sub rw]. rewrite S_bk2. unfold V_SIZE. cbn [eval]. rewrite E2, H2, E148. apply bv_eq. rewrite add_val, !u64_lit by (clear -AIS N1; lia).
      rewrite Z.mod_small by (clear -AIS N1; lia). clear; lia.
    + cbn [rho_sub rw]. rewrite S_bk3. cbn [eval]. fold (eval r3 faend_e). apply bv_eq.
      rewrite add_val, (faend_val r3 HFz HGh), sll_val, xor_val, E0, H0.
      replace (bv_unsigned (Z_to_bv 64 18446744073709551615)) with 18446744073709551615 by reflexivity.
      rewrite !u64_lit by (clear -Hi N4 N5 N6 N7 N8; lia). rewrite lxor_ones64 by (clear -Hi N4; lia).
      change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by (clear; lia).
      replace (((18446744073709551615 - (i + 1)) * 2 ^ 2) mod 2 ^ 64) with (2 ^ 64 - 4 * (i + 2)).
      2: { apply (Z.mod_unique_pos _ _ 3); [clear -Hi N4; lia | clear; lia]. }
      rewrite (u64_lit (FAb A rb + 4 * (nf + new - 1 - (i + 1)))) by (clear -Hi Hlt N4 N5 N6 N7 N8; lia).
      symmetry. apply (Z.mod_unique_pos _ _ 1); [clear -Hi Hlt N4 N5 N6 N7 N8; lia | clear; lia].
  -
    apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FB_x) as BF. unfold F_lt in BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 = new)).
    { intros w [_ ((HFz & HGh & _) & H0 & _)].
      destruct HGh as (_ & _ & _ & _ & _ & _ & _ & _ & Q228 & _). fold new in Q228.
      unfold branch_taken, bv_ltu, vNEW in BF. cbn [eval] in BF. rewrite H0, Q228, !u64_lit in BF by (clear -Hi N4; lia).
      destruct (Z.ltb_spec (i + 1) new) as [X|X]; [exfalso; apply BF; reflexivity | clear -X Hi; lia]. }
    intros Heq.
    apply (tr_cut Kc TR KIT valuation _ _ Q (REL LX OB_x)). intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRp (phL new)) (keepn (la_state LX) nobF) r3 tp)); [|exact (HKx Heq _)].
    intros w Hw. apply (SPA_J JREL (JRp (phL new)) _ r3 tp w); [|exact Hw]. intros (HJ & _). rewrite <- Heq. exact HJ.
Qed.

Lemma fill_loop : ltac2:(tb__ "0|0|
S2fS21SeS24S3aQ40A1A1S5eS0S21S9Vnew;R4A2SaR5A1A3S1S6Z0R5A2S8R5Vnew;A2A2SeVTR;S36S35S40VA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S4eS31VLX;A1VnobF;A2R1R5A5R4A2Fr';VTR;S36S35S38R7A1VCL0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;Fn;").
Proof.
  induction n as [|n IH]; intros i r tp Q Hn Hi HX; [clear -Hn Hi; lia|].
  apply (fill_iter i r tp Q Hi).
  - intros Hlt r'. apply (IH (i + 1) r' tp Q); [clear -Hn; lia | clear -Hi Hlt; lia | exact HX].
  - intros _ r'. apply HX.
Qed.

Variables (E3 LH : axst) (LFL LJP : leafA) (s_in : wsub).
Let FR : list sprop := factsR E3.
Let XLF : axst := ltac2:(tb__ "0|0|
S4eS31VLX;A1VnobF;A2").
Let CXL : axst := cXL FR XLF.
Hypothesis R_h : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z418d4S27S21A1A3VLH;S26A5S2aG0S23S32VLFL;S27S32A1A3A2A3").
Hypothesis LN_h : ltac2:(tb__ "0|0|
S0S25S17S30VLH;A1A1S28A3").
Hypothesis NX_h : ltac2:(tb__ "0|0|
S0S25S63S4cS13S30VLH;A1A1A2S26A3").
Hypothesis ENT_in : ltac2:(tb__ "0|0|
S0S25S34S31VLFL;A1VCL0;Vs_in;A3S26A3").
Hypothesis SID_in : ltac2:(tb__ "0|0|
S0S25S3eVs_in;S4cA2S26A3").
Hypothesis S_in0 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S4aA2S10Z1A1A3").
Hypothesis S_in2 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S4bA2S55A3").
Hypothesis S_in3 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S4dA2SfS57S61S10N4A1A3A3").
Hypothesis W_xl : ltac2:(tb__ "0|0|
S0S25S19S30VCXL;A1A1S26A3").
Hypothesis D_xl : ltac2:(tb__ "0|4|
S0S29S2cS24S2cSdSdA2M0A1M1S24S11A1M2A2M3A1S6dS30VXLF;A1S30VCXL;A1A2S2aG3S2dG1G2S27G0A1S23S11S50S23S11S51S27S11A1A3A3A4A2A3").
Hypothesis NX_xl : ltac2:(tb__ "0|0|
S0S25S64S13S30VCXL;A1A1S13S30VXLF;A1A1A2S26A3").
Hypothesis R_j : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z41560S27S21A1A3VCXL;S26A5S2aG0S23S32VLJP;S27S32A1A3A2A3").
Hypothesis LN_xl : ltac2:(tb__ "0|0|
S0S25S17S30VCXL;A1A1S28A3").
Hypothesis NXr_xl : ltac2:(tb__ "0|0|
S0S25S63S4cS13S30VCXL;A1A1A2S26A3").

Theorem fill_all : ltac2:(tb__ "0|0|
SeS24S3aQ40A1A1S5eSeVTR;S36S35S40VA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S31VLJP;A1R1R3A5R2A2Fr';VTR;S36S35S40VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VLH;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HX. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x418d4] LH [LFL] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _.
  apply (tr_pre Kc TR KIT (SPA segs (JRfill 0) CL0 (rho_sub r1 s_in) tp)).
  { intros w Hw. apply (SPA_entails_J (JRp ph) (JRfill 0) _ CL0 s_in r1 tp w ENT_in); [|exact Hw].
    intros HJ. pose proof (rho_sub_agree s_in GR r1 SID_in) as AGs. pose proof HJ as (HFz & HGh & _).
    split; [|split; [|split]].
    - rewrite phL0. eapply (JR_stable A Kc rb tp0 md0 ph GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    - cbn [rho_sub rw]. rewrite S_in0. reflexivity.
    - cbn [rho_sub rw]. rewrite S_in2. unfold vAU. cbn [eval]. destruct HGh as (_ & _ & _ & Q223 & _). fold nv c cs au in Q223. rewrite Q223. f_equal. clear; lia.
    - cbn [rho_sub rw]. rewrite S_in3. cbn [eval]. fold (eval r1 faend_e). apply bv_eq. rewrite add_val, (faend_val r1 HFz HGh).
      replace (bv_unsigned (Z_to_bv 64 (-4))) with 18446744073709551612 by reflexivity. rewrite u64_lit by (clear -N4 N5 N6 N7 N8; lia).
      symmetry. apply (Z.mod_unique_pos _ _ 1); [clear -N4 N5 N6 N7 N8; lia | clear; lia]. }
  apply (fill_loop (Z.to_nat new) 0 _ tp Q); [clear -N4; lia | clear -N4; lia|].
  intros r2. fold XLF.

  apply (jr_restate A Kc rb tp0 md0 TR KIT XLF (ax_S CXL) _ _ (phL new) r2 tp Q W_xl D_xl NX_xl).
  { intros tr md (HFz & HGh & _) _. split; [constructor|].
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
    destruct (new_nums A rb CF PF) as (_ & M2 & M3 & _ & M5 & M6 & _). cbn zeta in M2, M3, M5, M6. fold nv c cs in M2, M3, M5, M6. fold S nf au new in M2, M3, M5, M6.
    destruct HGh as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & Q228 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q224, Q227. fold nf au new in Q221, Q223, Q228.
    destruct (kchunks_facts c C1) as (K1 & _).
    assert (NS : 0 <= new * S <= 3758096384) by (clear -N1 N2 N3 N4; nia).
    repeat apply Forall_cons; try apply Forall_nil.
    - unfold HINT_au. cbn [holds]. unfold branch_taken, bv_ltu, vMU, vAU, vNEW, V_SIZE. cbn [eval]. rewrite !add_val, mul_val, E148, Q223, Q224, Q228, !u64_lit by (clear -N1 N2 N4 M2 M3; lia).
      rewrite (Z.mod_small (new * S)) by (clear -NS; lia). rewrite !Z.mod_small by (clear -NS N2 M2 M3; lia).
      intros X. apply Z.ltb_lt in X. clear -X M6. lia.
    - unfold HINT_k. cbn [holds]. unfold branch_taken, bv_ltu, vNF, vNEW, vK. cbn [eval]. rewrite add_val, Q221, Q227, Q228, !u64_lit by (clear -N4 N5 N6 K1; lia).
      rewrite Z.mod_small by (clear -N4 N5 N6; lia). intros X. apply Z.ltb_lt in X. clear -X M5 N5. lia. }
  change (ax_setS XLF (ax_S CXL)) with CXL.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41560] CXL [LJP] (phL new) r2 tp Q R_j LN_xl NXr_xl).
  intros L r3 [<-|[]] _. exact (HX r3).
Qed.
End FILL.
End SpineCallocR13.

(* [comment removed for export] *)
Module DrainF.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "bool"; "true"; "andb"; "pair"; "prod"; "false"; "option"; "Some"; "nat"; "app"; "None"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "eqb"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "SLit"; "cell"; "rm"; "eval"; "sprop"; "ss_lenient"; "ss_objs"; "rl"; "rw"; "smatch"; "ss_next"; "sv_eqb"; "DUnknown"; "SAlu"; "c_off"; "c_val"; "c_width"; "mkCell"; "mkObj"; "sstate"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "sym_runA"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "cell_insv"; "JDr"; "O_riX"; "entryD"; "mid_ok"; "ri_hasD"; "frozenD"; "leaf_ok"; "rstD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "Pre_dh_f"; "L_dh_f"; "NXD"; "JLD"; "O_cntD"; "O_dstD"; "dst_cells"; "JD"; "dfacts"; "drain_zone"; "dst_e"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vRI"; "ri_e"; "vMFA"; "nobj"; "nxt"; "pcof"; "updR"; "vAU"; "vMU"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "vmd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.DCHAIN"; "mid_ok"; "leaf_ok"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.DJ"; "frozenD"; "JDr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Kc_ok"; "KcA"; "top_high"; "tp_ok"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.DFIN"; "JDfin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drainA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "free_array"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "AInvQ"; "K0"; "rigidQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "cs_mapped_free_array"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "mlink"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@Stdlib.PArith.BinPos.Pos";
"eqb"; "le"; "leb"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 DepotCall PrimCredit PrimCreditLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.RebuildR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.RebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma cst_ok_nil : cst_ok []. Proof. intros a (b & k & [] & _). Qed.
Lemma xgl_ok_nil : xgl_ok []. Proof. intros a (b & k & [] & _). Qed.

Lemma SPA_rebase_J : ltac2:(tb__ "0|3|
S46S46S1cS35S5S1aA1M0G0S5S33Q40A1A1S5S54A1M1S6aS53S1S5ScS1bS1bA2M2A1S3aR7A1S7G2A1A3S1G0S23S37R8A1A1S11S1aR7R6A3A3S45S32RcR9RaR6SbG1S55R5S56R4R3A2A4A6S26S32RbS37RaA1SbG1S55R6S56S66R4R7R5A3S67R4A1A2A4A4ReRcR8R7R5A4ReS63RdRaS66R6R9R7A3A3R9R8R6A4F_;F_;S45S32RdRbS63RcR9S66R5R8R6A3A3R8SbG1S55R7S56R6R5A2A4A6F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;FR;Fobjs;FA;Frho;FJ';FJ;").
Proof.
  intros J J' rho A objs R tp tr ms md HX HO HS HJ.
  apply (SPA_absorb_any segs J J' rho A R (vms md tp ms) tp (tr, mkCfg ms md) HX); [| exact HS |].
  - intros o a Ho Ha. exists o. split; [rewrite HO; apply in_or_app; right; exact Ho | exact Ha].
  - cbn [w_tr w_cfg cfg_model fst snd]. apply HJ; [exact (proj1 (proj1 HS)) | exact (proj2 HS)].
Qed.

Section DJ.
Variable n : Z.
Variables (A : AA) (Kc : KcA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Definition entryD : Prop := ltac2:(tb__ "0|0|
S0S81VA;Vrb;Vtp0;Vmd0;A4S0S71VA;Vrb;A2S0S70VA;Vrb;A2S0S83VA;Vrb;A2S50Vn;SdVA;Vc;Vrb;A5A2A2A2A2").
Definition frozenD (r : valuation) : Prop := ltac2:(tb__ "0|0|
S0S14S8dR1Pf0A2S1S33Q40A1S25Vrb;R2A2S25Vr;R2A2A3F_;Fi;S14S1S5S33Q8A1A1S24Vrb;R1A2S24Vr;R1A2A3Fl;A2").
Definition JDr : jpredA := ltac2:(tb__ "0|1|
S1cS5S33Q40A1M0A1S5S54A1S53S0S6cR4A1S0VKc;R2R1A2S0S87VA;Vrb;Vtp0;Vmd0;S88R3R1A7G0S1SeS33Q8A1A1S1fR5R1A2S1fVrb;R1A2A3Fa;A2A2A2Lmd;Ltr;Ltp;Lr;").

Lemma JDr_K : JK Kc JDr.
Proof. intros r t tr md (_ & HK & _). exact HK. Qed.
Lemma JDr_stable : ltac2:(tb__ "0|0|
S14S6eVKc;A1S8bPf0R2A2S47S32R3S6dA3F_;F_;Fm;").
Proof.
  intros m HKc Hm r r' tp tr md md' Hag Hme (HF & HK & HM & HR).
  destruct Hag as (Hw & Hl & Hrm). destruct Hme as ((mat' & ->) & Hpaid & _).
  split; [|split; [|split]].
  - destruct HF as [F1 F2]. split; [intros i Hi; rewrite (F1 i Hi); apply Hw; lia | intros l; rewrite (F2 l); apply Hl].
  - rewrite with_vm_backing_with_vm. apply HKc. exact HK.
  - unfold mlink in *. cbn zeta in *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|].
    exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. rewrite Hpaid. exact M10.
  - intros a. rewrite <- (Hrm a). exact (HR a).
Qed.

Hypothesis HE : entryD.
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let SB : Z := ag_spacebeg G.
Let cs : class_state := SegQ_wf2.cls_of A c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).

Lemma d_nums : ltac2:(tb__ "0|7|
S0S0S15Z1M0Vc;A2S15Vc;Z1eA2A2S0S1S13S89Vc;A1Vn;A3S0S0S15G0Vn;A2S15Vn;Z8A2A2S0S1S13S7fVc;A1S17Z2Vn;A2A3S0S15Z1000M1VT;A2S0S15S16VT;G1A2M2S86VG;A1M3A2S0S15G3Z7fffff800000A2S0S4S15G2Z10000A2S15Z643000VT;A2A2S0S15Z10007fff8000M4VSB;A2S0S15S16S16VSB;Z2000000000A2G1A2M5G3A2S0S4S15G2VSB;A2S15G5VT;A2A2S0S4S15G2Z7fff7000A2S15G4VT;A2A2S0S15Z0Vnf;A2S0S15S17Z4S16Vnf;Vn;A2A2S85Vcs;A1M6A2S15G6Z20000000A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  destruct HE as (HA & _ & _ & _ & DF). destruct DF as (Hini & C1 & EK & HFULL & HGR & _). fold cs in HFULL, HGR.
  destruct (kchunks_facts c C1) as (K1 & K2 & K3). rewrite EK in K1, K2.
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). fold G in HG, HRest.
  pose proof (geom_numsS _ HG) as (_ & _ & _ & G4 & G5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG). fold T in G4, G5.
  pose proof (geom_old _ HG) as X. rewrite FS_total_val, kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold SB in X.
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _ & _). fold T in TB, TI. unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TB, TI.
  destruct (proj1 HI3) as (T3 & _). rewrite kSpaceSize_val in T3. fold G in T3. fold T SB in T3.
  destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & PC). pose proof (PC c C1) as PCc. unfold class_repr in PCc.
  destruct PCc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N6 & _). change (nthZ (aa_cls A) c cs_empty) with cs in N6. fold nf in N6. unfold kFreeArraySize in N6.
  unfold drain_grows in HGR. fold nf in HGR. apply Z.ltb_ge in HGR. rewrite EK in HGR.
  split; [exact C1|]. split; [exact EK|]. split; [exact K1|]. split; [symmetry; exact K2|].
  split; [exact G4|]. split; [exact G5|]. split; [clear -TG; lia|]. split; [clear -TI; lia|].
  split; [clear -X; tauto|]. split; [clear -X; lia|]. split; [clear -T3; lia|]. split; [clear -TB; lia|].
  split; [unfold nf; apply Zle_0_nat|]. split; [exact HGR | clear -N6; lia].
Qed.

Lemma d_evals : ltac2:(tb__ "0|2|
S1cS6cR1A1S0S1S13S34Q40M0S20R2S78A2A2S16S16VT;Zd0A2S17Z50Vc;A2A2A3S0S1S13S34G0S20R2S59A2M1A2S80VSB;Vc;A2A3S0S1S33G0A1S20R2S5aA2G1A3S1S13S34G0S20R2S52A2A2S16S7eVSB;Vc;A2S17Z4Vnf;A2A2A3A2A2A2F_;Fr;").
Proof.
  intros r [Fw _]. destruct d_nums as (C1 & _ & K1 & _ & T1 & T2 & TG & _ & S1 & S2 & _ & _ & NF0 & NF1 & NF2).
  destruct HE as (_ & _ & _ & (E151 & _ & E155 & E156) & DF). destruct DF as (_ & _ & _ & _ & _ & E158 & _ & E221 & _ & _ & _ & E225 & _).
  fold G in E151, E155, E156, E225. fold T in E151. fold SB in E155, E156, E225. fold cs in E221. fold nf in E221.
  rewrite (Fw 151%positive) in E151 by lia. rewrite (Fw 155%positive) in E155 by lia. rewrite (Fw 156%positive) in E156 by lia.
  rewrite (Fw V_CLS) in E158 by (unfold V_CLS; lia). rewrite (Fw 221%positive) in E221 by lia. rewrite (Fw 225%positive) in E225 by lia.
  rewrite kSpaceSize_val in E156.
  assert (RIv : region_info SB c = SB + 137438953472 + c * 128) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (FAv : free_array SB c = SB + c * 4294967296 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  split; [|split; [|split]].
  - unfold pc_base, vT, V_CLS in *. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (_ * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. lia.
  - unfold vRI. cbn [eval]. rewrite E225. apply u64_lit. rewrite RIv. lia.
  - unfold ri_e, vRI, vRIS, V_CLS in *. cbn [eval]. rewrite E156, E158, E225. apply bv_eq.
    rewrite add_val, sll_val, !u64_lit by (rewrite ?RIv; lia). change (7 mod 64) with 7. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 7)) by lia. rewrite Z.mod_small by lia. rewrite RIv. lia.
  - assert (EFA : bv_unsigned (eval r fa_e) = free_array SB c).
    { unfold fa_e, vSB, V_CLS in *. cbn [eval]. rewrite E155, E158.
      rewrite add_val, add_val, sll_val, !u64_lit by lia. change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia.
      rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + 3758096384)) by lia. rewrite Z.mod_small by lia. rewrite FAv. lia. }
    unfold dst_e, vNF. cbn [eval]. rewrite add_val, EFA, sll_val, E221, !u64_lit by lia. change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (nf * 2 ^ 2)) by lia. rewrite Z.mod_small by (rewrite FAv; lia). lia.
Qed.
End DJ.

Definition cell_insv (off w : Z) (v : sv) (cells : list cell) : bool := ltac2:(tb__ "0|0|
S73S1eS1eSaSaS28S2bR1A1S1dVoff;A1A2S18S2dR1A1Vw;A2A2S28S2cR1A1Vv;A2A2Lcl;Vcells;A3").
Lemma cell_insv_In : ltac2:(tb__ "0|0|
S13S13S1bS5S1eA1S1S8S3cR4R3R2R1A4S9A3S72S1eS2eS1dR5A1R4R3A3R2A3F_;Fcells;Fv;Fw;Foff;").
Proof.
  intros off w v cells H. unfold cell_insv in H. apply existsb_exists in H as ([o w' v'] & Hin & E). cbn [c_off c_width SymState.c_val] in E.
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply sv_eqb_sound in E1. apply sv_eqb_sound in E3. apply Z.eqb_eq in E2.
  subst o w' v'. exact Hin.
Qed.
Definition O_riX (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S2fS59S1dZ0A1S1dZ80A1Vcells;S29A5").
Definition ri_hasD (n : Z) (mfa' : sv) (cells : list cell) : bool := ltac2:(tb__ "0|3|
SaSaSaSaSaSaSaS3cZ0M0Z8M1S1dG0A1M2Vcells;A4S3cZ10G1S2aS76S62S1dVn;A1A3Vcells;A4A2S3cZ18G1Vmfa';Vcells;A4A2S3cZ20G1S60Vcells;A4A2S3cZ28G1G2Vcells;A4A2S3cZ30G1S61Vcells;A4A2S3cZ38G1G2Vcells;A4A2S3cZ44Z1G2Vcells;A4A2").

Section DFIN.
Variable n : Z.
Variables (A : AA) (Kc : KcA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Hypothesis HE : ltac2:(tb__ "0|0|
S3fVn;VA;Vc;Vrb;Vtp0;Vmd0;A6").
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let SB : Z := ag_spacebeg G.
Let cs : class_state := SegQ_wf2.cls_of A c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).

Definition JDfin : jpredA := ltac2:(tb__ "0|8|
S1cS5S33Q40M0A1M1A1M2S5S54A1S53S0S82VKc;S7aVA;Vc;A2R4R3R2R1A6S0G1S3S51VG;Vc;Vcs;S34G0R1A2M3A4A1S1SeS33Q8A1M4A1M5S1fR6R2A2S1fVrb;R2A2M6A3F_;Fa;S0G1S0S15S7dG3A2S19G3S7cA2A2S3S1G5G6S12G4A1M7A3A1S3S1G5S1fR7R3A2G7A3A1F_;F_;Fa;S0S42Vrb;R4A2S1G2R3Vtp0;A3A2A2A2A2Lmd;Ltr;Ltp';Lr';").

Lemma d_final : ltac2:(tb__ "0|4|
S30S5S1aA1M0S5S1eA1S1cS5S33Q40A1A1S5S54A1M1S6aS53S53S1G0S23R9A1S11S1aR8S6S1aS4cVn;A1M2S6S1aS3eR7A1S6S1aS4dVn;S4eVn;A1A2S7S1aA1A3M3A3A3A3A3S1S8S41Vn;S5bR8A3S9A3S26S32R8RbSbG1S55R6S56R5R4A2A4A4S3dVA;VKc;Vrb;Vtp0;Vmd0;R9R8R7R4A9S79S63RaS6S1aG2S6S1aS3eRbA1G3A3A3R7A3R9R8R5A4F_;F_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;FcellsR;FK;FS;").
Proof.
  intros S K cellsR r tp tr ms md mdJ HO HRI Hsm (HFz & HK & HM & HRM).
  destruct (d_nums n A c rb tp0 md0 HE) as (C1 & EK & K1 & EMC & T1 & T2 & TG & TI & S1 & S2 & TS & TB & NF0 & NF1 & NF2).
  fold G in T1, T2, TG, TI, S1, S2, TS, TB. fold T in T1, T2, TI, TS, TB. fold SB in S1, S2, TS. fold cs in NF1, NF2. fold nf in NF0, NF1.
  destruct (d_evals n A c rb tp0 md0 HE r HFz) as (EB & ERI & _ & EDS). fold G in EB, ERI, EDS. fold T in EB. fold SB in ERI, EDS. fold cs in EDS. fold nf in EDS.
  pose proof HE as (HA & Htp & Htop & HRG & DF). destruct DF as (Hini & _ & _ & HFULL & HGR & E158 & _ & E221 & E222 & E223 & E224 & E225 & ECH).
  fold cs in HFULL, HGR, E221, E222, E223, E224, ECH. fold nf in E221.
  assert (Erm : rm r = rm rb) by (apply functional_extensionality; exact HRM).
  set (R := [O_cntD n; O_riX cellsR; O_dstD n (dst_cells n)]) in *. set (r3 := rho_absorb r R ms).
  set (pce := T + 208 + 80 * c) in *. set (ri := region_info SB c) in *. set (fa := free_array SB c) in *.
  assert (RIv : ri = SB + 137438953472 + c * 128) by (unfold ri, region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (FAv : fa = SB + c * 4294967296 + 3758096384) by (unfold fa, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  assert (RC : obj_range r (O_cntD n) = (pce, pce + 4)) by (unfold O_cntD; rewrite obj_range_mk by lia; rewrite EB; f_equal; lia).
  assert (RR : obj_range r (O_riX cellsR) = (ri, ri + 128)) by (unfold O_riX; rewrite obj_range_mk by lia; rewrite ERI; f_equal; lia).
  assert (RD : obj_range r (O_dstD n (dst_cells n)) = (fa + 4 * nf, fa + 4 * nf + 4 * n)) by (unfold O_dstD; rewrite obj_range_mk by lia; rewrite EDS; f_equal; lia).

  assert (ZEQ : forall z, drain_zone G c cs z <-> (pce <= z < pce + 4 \/ ri <= z < ri + 128 \/ fa + 4 * nf <= z < fa + 4 * nf + 4 * n)).
  { intros z. unfold drain_zone. cbv zeta. fold T SB. fold ri fa nf. rewrite HGR, EK. unfold pce. split.
    - intros [X|[X|[X|(X & _)]]]; [left; lia | right; right; lia | right; left; exact X | discriminate X].
    - intros [X|[X|X]]; [left; lia | right; right; left; exact X | right; left; lia]. }
  assert (INR : forall a : word, in_ranges r R a <-> drain_zone G c cs (bv_unsigned a)).
  { intros a. rewrite ZEQ. unfold in_ranges, R. split.
    - intros (o & [<-|[<-|[<-|[]]]] & Hr); [rewrite RC in Hr | rewrite RR in Hr | rewrite RD in Hr]; cbn [fst snd] in Hr; tauto.
    - intros [X|[X|X]]; [exists (O_cntD n); split; [left; reflexivity | rewrite RC; exact X]
                        | exists (O_riX cellsR); split; [right; left; reflexivity | rewrite RR; exact X]
                        | exists (O_dstD n (dst_cells n)); split; [right; right; left; reflexivity | rewrite RD; exact X]]. }
  assert (RAW : forall a : word, ~ drain_zone G c cs (bv_unsigned a) -> rm r3 a = rm rb a).
  { intros a Ha. unfold r3. rewrite rm_absorb_out by (intros X; apply Ha; apply INR; exact X). exact (HRM a). }

  assert (ZOUT : forall z, drain_zone G c cs z -> (z < 65536 \/ 6565888 <= z) /\ (z < 2147446784 \/ 17594333495296 <= z) /\ 0 <= z < 2 ^ 64).
  { intros z Hz. apply ZEQ in Hz. unfold pce in Hz. rewrite RIv, FAv in Hz. clear -Hz C1 T1 T2 TG TI S1 S2 TB NF0 NF1 NF2 K1. lia. }

  set (vE := view segs (rm rb)). set (v3 := view segs (rm r3)).
  assert (VO : forall z, ~ drain_zone G c cs z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE, view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    unfold rd_of. rewrite RAW by (rewrite u64_lit by lia; exact Hz). reflexivity. }
  assert (ABS : forall o, In o R -> forall cl, In cl (ob_cells o) -> forall j, (j < Z.to_nat (c_width cl))%nat ->
            v3 (bv_unsigned (eval r (ob_base o)) + soff r (c_off cl) + Z.of_nat j) = Some (nth j (enc_bytes (Z.to_nat (c_width cl)) (eval r (SymState.c_val cl))) (Z_to_bv 8 0))
            /\ obj_lo_of r o <= soff r (c_off cl) /\ soff r (c_off cl) + c_width cl <= obj_hi_of r o).
  { intros o Ho cl Hcl j Hj. destruct (absorb_obj r S tr ms md K R o Hsm HO Ho) as (B0 & AS & _).
    destruct (AS cl Hcl) as (B1 & B2 & ASb). specialize (ASb j Hj). split; [|exact (conj B1 B2)].
    unfold v3. rewrite view_in; [exact ASb|]. clear -B0 B1 B2 Hj. cbv zeta in B0. lia. }
  assert (PRS : forall z, drain_zone G c cs z -> exists b, v3 z = Some b).
  { intros z Hz. pose proof (ZOUT z Hz) as (_ & _ & Z64). apply ZEQ in Hz.
    assert (X : exists o off, In o R /\ (ob_dflt o = DUnknown) /\ z = bv_unsigned (eval r (ob_base o)) + off /\ obj_lo_of r o <= off < obj_hi_of r o).
    { unfold obj_lo_of, obj_hi_of. destruct Hz as [X|[X|X]].
      - exists (O_cntD n), (z - pce). split; [left; reflexivity|]. split; [reflexivity|]. cbn [ob_base ob_lo ob_hi O_cntD]. rewrite EB, !soff_lit_small by lia. unfold pce in *. lia.
      - exists (O_riX cellsR), (z - ri). split; [right; left; reflexivity|]. split; [reflexivity|]. cbn [ob_base ob_lo ob_hi O_riX]. rewrite ERI, !soff_lit_small by lia. lia.
      - exists (O_dstD n (dst_cells n)), (z - (fa + 4 * nf)). split; [right; right; left; reflexivity|]. split; [reflexivity|]. cbn [ob_base ob_lo ob_hi O_dstD]. rewrite EDS, !soff_lit_small by lia. lia. }
    destruct X as (o & off & Ho & Hd & -> & Hoff). destruct (absorb_obj r S tr ms md K R o Hsm HO Ho) as (_ & _ & AP & _).
    destruct (AP (or_introl Hd) off Hoff) as [x Hx]. exists x. unfold v3. rewrite view_in by exact Z64. exact Hx. }

  assert (CELL : forall o off w v (e : sv), In o R -> In (mkCell (SLit off) (Z.of_nat w) e) (ob_cells o) -> - 2 ^ 62 <= off < 2 ^ 62 -> eval r e = Z_to_bv 64 v ->
            cell_ok v3 (mkACell (bv_unsigned (eval r (ob_base o)) + off) w v)).
  { intros o off w v e Ho Hcl Hoff Ee j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (ABS o Ho _ Hcl j ltac:(cbn [c_width]; rewrite Nat2Z.id; exact Hj)) as (X & _). cbn [c_off c_width SymState.c_val] in X.
    rewrite soff_lit_small in X by lia. rewrite Nat2Z.id, Ee in X. exact X. }
  repeat (apply andb_prop in HRI as [HRI ?]).
  repeat match goal with X : cell_insv _ _ _ _ = true |- _ => apply cell_insv_In in X end.
  assert (Ekeep : drain_keep c cs = Z.to_nat n) by (unfold drain_keep; rewrite EK; lia).
  assert (HDM : drain_mem A c vE v3).
  { unfold drain_mem. cbv zeta. fold G. fold T SB. change (nthZ (aa_cls A) c cs_empty) with cs. fold nf. fold ri fa. replace (T + 208 + 80 * c) with pce by reflexivity.
    split; [exact VO|]. split; [exact PRS|].
    split.
    { rewrite Ekeep, Z2Nat.id by lia. replace pce with (bv_unsigned (eval r (ob_base (O_cntD n))) + 0) by (cbn [ob_base O_cntD]; rewrite EB; unfold pce; lia).
      apply (CELL (O_cntD n) 0 4%nat n (SLit n)); [left; reflexivity | left; reflexivity | lia | reflexivity]. }
    split.
    { intros i Hi. rewrite EK in Hi. rewrite Ekeep.
      replace (fa + 4 * (nf + Z.of_nat i)) with (bv_unsigned (eval r (ob_base (O_dstD n (dst_cells n)))) + 4 * Z.of_nat i) by (cbn [ob_base O_dstD]; rewrite EDS; lia).
      apply (CELL (O_dstD n (dst_cells n)) (4 * Z.of_nat i) 4%nat _ (SExt true 32 (vCH i))); [right; right; left; reflexivity | | lia |].
      - cbn [ob_cells O_dstD]. unfold dst_cells. apply (proj1 (in_rev _ _)). apply in_map_iff. exists i. split; [reflexivity | unfold idxs; apply in_seq; lia].
      - cbn [eval vCH]. destruct HFz as [Fw _]. rewrite <- (Fw (Pos.of_nat (170 + i))) by lia. rewrite (ECH i Hi).
        apply sext32_small.

        pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & PC). pose proof (PC c C1) as PCc. unfold class_repr in PCc.
        destruct PCc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & N3 & _ & _ & _ & _ & _ & N7 & _). change (nthZ (aa_cls A) c cs_empty) with cs in N2, N3, N7.
        assert (HIN : In (nth (Z.to_nat n + i) (cs_cache cs) 0) (cs_free_array cs ++ cs_cache cs)).
        { apply in_or_app; right. apply nth_In. rewrite <- (Nat2Z.id (length (cs_cache cs))), HFULL, EMC. lia. }
        destruct (N7 _ HIN) as (X1 & _ & X3). unfold kCompactPtrScale in X3. rewrite Z.shiftl_mul_pow2 in X3 by lia. change (2 ^ 4) with 16 in X3.
        destruct (cap_facts c C1) as (SZ & _). unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in N3. clear -X1 X3 N2 N3 SZ. lia. }
    assert (RIC : forall off w v (e : sv), In (mkCell (SLit off) (Z.of_nat w) e) cellsR -> - 2 ^ 62 <= off < 2 ^ 62 -> eval r e = Z_to_bv 64 v -> cell_ok v3 (mkACell (ri + off) w v)).
    { intros off w v e Hcl Hoff Ee. replace ri with (bv_unsigned (eval r (ob_base (O_riX cellsR)))) by (cbn [ob_base O_riX]; exact ERI).
      apply (CELL (O_riX cellsR) off w v e); [right; left; reflexivity | exact Hcl | exact Hoff | exact Ee]. }
    destruct HFz as [Fw _].
    assert (V221 : rw r 221%positive = Z_to_bv 64 nf) by (rewrite <- (Fw 221%positive) by lia; exact E221).
    assert (V222 : rw r 222%positive = Z_to_bv 64 (cs_mapped_free_array cs)) by (rewrite <- (Fw 222%positive) by lia; exact E222).
    assert (V223 : rw r 223%positive = Z_to_bv 64 (cs_allocated_user cs)) by (rewrite <- (Fw 223%positive) by lia; exact E223).
    assert (V224 : rw r 224%positive = Z_to_bv 64 (cs_mapped_user cs)) by (rewrite <- (Fw 224%positive) by lia; exact E224).
    unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted.
    split; [apply (RIC 0 8%nat 0 (SLit 0)); [assumption | lia | reflexivity]|].
    split.
    { rewrite EK. apply (RIC 16 8%nat (nf + n) (SAlu ALU_ADD vNF (SLit n))); [assumption | lia |].
      unfold vNF. cbn [eval]. rewrite V221. apply bv_eq. rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia. }
    split.
    { unfold drain_cs. cbn [cs_mapped_free_array]. rewrite HGR. apply (RIC 24 8%nat _ vMFA); [assumption | lia | unfold vMFA; cbn [eval]; exact V222]. }
    split; [apply (RIC 32 8%nat _ vAU); [assumption | lia | unfold vAU; cbn [eval]; exact V223]|].
    split; [apply (RIC 40 8%nat 0 (SLit 0)); [assumption | lia | reflexivity]|].
    split; [apply (RIC 48 8%nat _ vMU); [assumption | lia | unfold vMU; cbn [eval]; exact V224]|].
    split; [apply (RIC 56 8%nat 0 (SLit 0)); [assumption | lia | reflexivity]|].
    apply (RIC 68 1%nat 0 (SLit 0)); [assumption | lia | reflexivity]. }

  pose proof HA as (_ & _ & _ & _ & HM0 & _ & HB0).
  unfold mlink in HM. cbn zeta in HM. unfold ph0, committed, revealedp, subU, subF in HM. cbn [ph_u ph_f Nat.leb] in HM.
  destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & _ & M10).
  assert (Etp1 : tp1 = []).
  { destruct tp1 as [|p tp1']; [reflexivity|]. exfalso. destruct (M8 p (or_introl eq_refl)) as [_ [[X _]|[X _]]]; discriminate X. }
  subst tp1. cbn [app length Z.of_nat] in M7, M10. subst tp.
  assert (HFULL' : Z.of_nat (length (cs_cache (nthZ (aa_cls A) c cs_empty))) = max_count c) by exact HFULL.
  assert (HMD : model_inv segs (drainA A c) tp0 mdJ).
  { apply (model_inv_fields A (drainA A c) tp0 md0 mdJ); try reflexivity; try assumption; [|clear -M10; lia].
    apply prim_credit_maps. intros c' Hc'. unfold drainA. cbn [aa_cls].
    destruct (Z.eq_dec c' c) as [->|Hne].
    - rewrite nth_list_upd_same by (pose proof HA as (_ & _ & _ & HRest' & _); destruct HRest' as (_ & _ & (PL & _) & _); rewrite PL; clear -C1; lia).
      unfold drain_cs. cbn [cs_mapped_user cs_mapped_free_array]. change (nth (Z.to_nat c) (aa_cls A) cs_empty) with cs. rewrite HGR. split; reflexivity.
    - rewrite nth_list_upd_other by (clear -Hne Hc' C1; lia). split; reflexivity. }
  assert (HBT : bandtp_inv v3 tp0).
  { eapply bandtp_mono; [|exact HB0]. intros z Hz Hd. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hz.
    rewrite VO; [exact Hd|]. intros X. destruct (ZOUT z X) as (_ & B & _). clear -Hz B. lia. }
  assert (RMI : forall a, IMG_LO <= a < IMG_HI -> rm r3 (Z_to_bv 64 a) = rm rb (Z_to_bv 64 a)).
  { intros a Ha. apply RAW. unfold IMG_LO, IMG_HI in Ha. rewrite u64_lit by lia. intros X. destruct (ZOUT a X) as (B & _). clear -Ha B. lia. }
  destruct (drain_rebuild [] [] cst_ok_nil xgl_ok_nil A rb r3 tp0 tp0 md0 mdJ c HA C1 Hini HFULL' HDM RMI HMD HBT) as (HAQ & _).
  assert (RW3 : forall i, rw r3 i = rw r i) by (intros i; reflexivity).
  destruct HFz as [Fw Fl].
  split.
  { split; [exact HAQ|]. split; [exact HK|].
    split; [unfold tp_ok in *; change (aa_geom (drainA A c)) with (aa_geom A); rewrite RW3, <- (Fw 24%positive) by lia; exact Htp|].
    split; [unfold top_high in *; change (aa_geom (drainA A c)) with (aa_geom A); rewrite !RW3, <- (Fw 10%positive), <- (Fw V_DEPTH) by (unfold V_DEPTH; lia); exact Htop|].
    destruct HRG as (Q1 & Q2 & Q3 & Q4). unfold rigidQ. change (aa_geom (drainA A c)) with (aa_geom A).
    rewrite !RW3, <- (Fw 151%positive), <- (Fw 152%positive), <- (Fw 155%positive), <- (Fw 156%positive) by lia. exact (conj Q1 (conj Q2 (conj Q3 Q4))). }
  split; [exact RAW|].
  split.
  { intros a Ha Hd. rewrite RAW; [exact Hd|]. intros X. destruct (ZOUT _ X) as (_ & B & _).
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Ha. clear -Ha B. lia. }
  split; [split; [intros i Hi; rewrite RW3; exact (Fw i Hi) | intros l; exact (Fl l)] | reflexivity].
Qed.
End DFIN.

Definition rstD (E : axst) (reg : nat) : axst := ltac2:(tb__ "0|2|
S5fS7S21A1M0VE;S5eVE;A1S6ScS10S1bA2M1SbS10S1bVreg;S59A4S7G1A1A3S7S1aA1SdG0S5dVE;A1A8").

Section DCHAIN.
Variable n : Z.

Definition leaf_ok (L : axst) : Prop := ltac2:(tb__ "0|3|
S2S5S1eA1M0G0S2S64S64S0S1S5ScS1bS1bA2M1A1S3aVL;A1S7G1A1A3S0S1S5S1aA1S23S37VL;A1A1M2S11S1aS75S1aS74S5cVL;A1U3A2G2A3S6S1aS4cVn;A1S6S1aS3eR2A1S6S1aS4dVn;S4eVn;A1A2S7S1aA1A3A3A3A3A3S0S1S8S41Vn;S5bR2A3S9A3S0S1S8S3bVL;S49Vn;A1R1A3S9A3S1S8S65R1S4aA2S9A3A2A2A2A2Ls;A2LcellsR;A2").

Definition mid_ok (F : nat) (reg : nat) (cuts : list Z) (next_ok : axst -> Prop) (L : axst) : Prop := ltac2:(tb__ "0|9|
S0S1S8S31S37S44VL;Vreg;A2M0A1M1A1S9A3S0S1SeScS5ScS1bS1bA2M2A1M3S5S21A1M4A2M5A1S77S37VL;A1M6G1A2SfG5SbG3G4S6G2SbS1bS1bS5aS59A4S7G2A1A3S7S21A1A4A2A3S0S1S8S8aS27G1A1M7S27G6A1A2S9A3S0S1S8S22G1A1SdA3S0S1S8S8cPf0G7A2S9A3S2S5S36A1M8G8S0S1SeG8A1S39S32VF;Vcuts;G0S9A5SfG8R1A2A3S36S72S36R1R2A3Vnext_ok;S38R2A1A1F_;FL';A2Lleaves;A2A2A2A2A2A2").

Variables (A : AA) (Kc : KcA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRokD Kc TR.
Hypothesis HKc : Kc_ok Kc.
Hypothesis HE : ltac2:(tb__ "0|0|
S3fVn;VA;Vc;Vrb;Vtp0;Vmd0;A6").
Notation JDp := (JDr A Kc rb tp0 md0).
Notation KT := (trd_ok Kc TR KIT).
Let Q : assn := ltac2:(tb__ "0|1|
S58S32S4aVrb;Vtp0;S6ScS35S57A2M0SbS35S57S49Vn;A1S4bVA;VKc;Vc;A3A4S7G0A1A3A5").

Lemma d_leaf : ltac2:(tb__ "0|0|
S35S1cS5S33Q40A1A1S69R3A1VTR;S45S32S3dVA;VKc;Vrb;Vtp0;Vmd0;A5R4R3R2A5VQ;A2F_;Ftp;Fr;FL;").
Proof.
  intros L r tp (cellsR & s & HX & HO & HRI & HENT & HSID).
  set (R := [O_cntD n; O_riX cellsR; O_dstD n (dst_cells n)]) in *.
  apply (tr_cut Kc TR KT valuation _ (fun r3 => SPA segs (JDfin A Kc c rb tp0) L r3 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r R (vms md tp ms)).
    apply (SPA_rebase_J JDp (JDfin A Kc c rb tp0) r L _ R tp tr ms md HX HO Hw).
    intros Hsm HJ. exact (d_final n A Kc c rb tp0 md0 HE _ _ cellsR r tp tr (vms md tp ms) (vmd md) md HO HRI Hsm HJ). }
  intros r3.
  apply (tr_pre Kc TR KT (SPA segs (JDfin A Kc c rb tp0) (L_dh_f n) (rho_sub r3 s) tp)).
  { intros w Hw. apply (SPA_entails_J (JDfin A Kc c rb tp0) (JDfin A Kc c rb tp0) L (L_dh_f n) s r3 tp w HENT); [|exact Hw].
    intros (J1 & J2 & J3 & J4 & J5). pose proof (rho_sub_agree s NXD r3 HSID) as AG.
    split; [|split; [exact J2 | split; [exact J3 | split; [|exact J5]]]].
    - eapply (K0_stable Kc (drainA A c) HKc); [|apply mat_equiv_refl | exact J1]. eapply agree_below_le; [|exact AG]. unfold QNPRE, NXD. lia.
    - destruct J4 as [F1 F2]. destruct AG as (Aw & Al & _). split; [intros i Hi; rewrite (F1 i Hi); apply Aw; unfold NXD; lia | intros l; rewrite (F2 l); apply Al]. }
  apply (tr_done Kc TR KIT). intros w [Hsm (J1 & J2 & J3 & J4 & J5)].
  exists (L_dh_f n), (JLD A Kc c), (rho_sub r3 s), tp.
  split; [left; reflexivity|]. split; [destruct J4 as [F1 F2]; split; [intros i Hi; apply F1; unfold NXD in Hi; lia | exact F2]|].
  split; [exact Hsm|]. unfold JLD. split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. intros l. symmetry. exact (proj2 J4 l).
Qed.

Lemma d_mid : ltac2:(tb__ "0|2|
S10S10S5S13A1S35OF_;S35S1cS5S33Q40A1A1M0S68R7R6R5R4R3A5S35S1cG0R8R3A1VTR;S45S32S3dVA;VKc;Vrb;Vtp0;Vmd0;A5M1R4R3R2A5VQ;A2F_;Ftp';Fr';FL';VTR;S45S32G1R5R4R3A5VQ;A2F_;F_;Ftp;Fr;FL;Fnext_ok;Fcuts;Freg;FF;").
Proof.
  intros F reg cuts next_ok L r tp (HW & HD & HNX & HLN & HNL & leaves & HRUN & HNEXT) HC.
  apply (tr_pre Kc TR KT (SPA segs JDp (rstD L reg) r tp)).
  { intros w Hw. pose proof (SPA_facts_hold segs _ r L tp w Hw) as HF. destruct (proj2 Hw) as (HFz & _).
    unfold rstD at 1. apply (SPA_restate segs _ r L (ax_S (rstD L reg)) tp w _ _ HW HD); [apply Pos.eqb_eq; exact HNX | | apply Forall_nil | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    exact (proj1 (proj2 (proj2 (d_evals n A c rb tp0 md0 HE r HFz)))). }
  apply (tr_run Kc TR KT F cuts (rstD L reg) leaves JDp r tp Q (JDr_K A Kc rb tp0 md0)); [|exact HRUN | exact HLN|].
  - apply JDr_stable; [exact HKc | apply Pos.leb_le; exact HNL].
  - intros L' r' HIn _. exact (HC (la_state L') r' tp (HNEXT L' HIn)).
Qed.

Variable F : nat.
Variable L1 : leafA.
Hypothesis R_1 : ltac2:(tb__ "0|1|
S1SeS5S36A1M0A1S39S32VF;S6S13Z3f124S7S13A1A3S48Vn;A1S9A5SfG0S6S36VL1;S7S36A1A3A2A3").
Hypothesis LN_1 : ltac2:(tb__ "0|0|
S1S8S22S37S48Vn;A1A1A1SdA3").
Hypothesis M_1 : ltac2:(tb__ "0|1|
S68VF;U8S6S13Z3f5d4S7S13A1M0A3S68VF;U16S6S13Z3ef78G0A3S69A4S38VL1;A1A5").

Theorem drain_fast_chain : ltac2:(tb__ "0|0|
S1cS5S33Q40A1A1VTR;S45S32S3dVA;VKc;Vrb;Vtp0;Vmd0;A5S48Vn;A1R2R1A5VQ;A2Ftp;Fr;").
Proof.
  intros r tp.
  apply (tr_run Kc TR KT F [0x3f124] (Pre_dh_f n) [L1] JDp r tp Q (JDr_K A Kc rb tp0 md0)); [|exact R_1 | exact LN_1|].
  - apply JDr_stable; [exact HKc | unfold Pre_dh_f, mkA, NXD; cbn [ax_S ss_next]; lia].
  - intros L r' [<-|[]] _.
    apply (d_mid F 8 [0x3f5d4] (mid_ok F 22 [0x3ef78] leaf_ok) (la_state L1) r' tp M_1). intros L2 r2 tp2 M2.
    apply (d_mid F 22 [0x3ef78] leaf_ok L2 r2 tp2 M2). intros L3 r3 tp3 M3. exact (d_leaf L3 r3 tp3 M3).
Qed.
End DCHAIN.

Section DTOP.
Variable n : Z.
Variable F : nat.
Variable L1 : leafA.
Hypothesis R_1 : ltac2:(tb__ "0|1|
S1SeS5S36A1M0A1S39S32VF;S6S13Z3f124S7S13A1A3S48Vn;A1S9A5SfG0S6S36VL1;S7S36A1A3A2A3").
Hypothesis LN_1 : ltac2:(tb__ "0|0|
S1S8S22S37S48Vn;A1A1A1SdA3").
Hypothesis M_1 : ltac2:(tb__ "0|1|
S40VF;U8S6S13Z3f5d4S7S13A1M0A3S40VF;U16S6S13Z3ef78G0A3S43Vn;A1A4S38VL1;A1A5").

Theorem drain_f : ltac2:(tb__ "0|1|
S6fS6bS6bOF_;F_;S7bR2R1A2S6eR3A1S84S13S1cS5S33Q40A1A1R7S45S32S4fVn;SdR4R8R3A5S48Vn;A1R2R1A5S58S32S4aR2R1S6ScS35S57A2M0SbS35S57S49Vn;A1S4bR4R8R3A3A4S7G0A1A3A5A2Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  intros Kc TR KIT HKc A c rho tp.
  apply (tr_cutP Kc TR (trd_ok Kc TR KIT) Model _ (fun md0 => entryD n A c rho tp md0) (fun md0 => SPA segs (JDr A Kc rho tp md0) (Pre_dh_f n) rho tp)).
  { intros w Hw. exists (cfg_model (w_cfg w)). destruct Hw as [HsmA ((HAQ & HK & Htp & Htop & HRG) & DF)].
    split; [exact (conj HAQ (conj Htp (conj Htop (conj HRG DF))))|].
    split; [exact HsmA|]. unfold JDr. split; [split; intros; reflexivity|]. split; [exact HK|]. split; [|intros a; reflexivity].
    unfold mlink, ph0, committed, revealedp, subU, subF. cbn [ph_u ph_f Nat.leb].
    repeat (split; [reflexivity|]). exists []. cbn [app length Z.of_nat]. split; [reflexivity|]. split; [intros p []|]. split; [lia | lia]. }
  intros md0 HE. exact (drain_fast_chain n A Kc c rho tp md0 TR KIT HKc HE F L1 R_1 LN_1 M_1 rho tp).
Qed.
End DTOP.
End DrainF.

(* [comment removed for export] *)
Module SpineMallocSec5J.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@Corelib.Init.Datatypes"; "list"; "nil"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I"; "nx0"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4I"; "T4ac"; "T4bc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U0Vst;S14S6S2eR1A1LX;R9R8R7R6A8S31R5R4R3A6S23S4R3S33A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0ha : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S31R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_0ha : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U0M4Vst;S14S24S6S2eR1A1LX;M5R6A2ReRdR5RbA8S2fR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S31R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_0ha : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S38R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_0ha).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U0Vst;S14S6R1LX;R9R8R7R6A8S32R5R4R3A6S23S4R3S34A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0hb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S32R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_0hb : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U0M4Vst;S14S24S6R1LX;M5R6A2ReRdR5RbA8S30R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S32R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_0hb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S39R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_0hb).
Qed.
End INST.
End SpineMallocSec5J.

