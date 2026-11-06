(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "Pre_mallocI"; "JL_malloc_ok"; "J_alloc_preT"; "L_malloc_ok"; "Posts_malloc"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Logic"; "eq"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CertMallocSPc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.SpineMallocS5iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS6iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS7iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS9iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocS9jW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.MallocHit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineMallocEiW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l3.DepotCallHW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocEc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.MallocHitTail2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lw.MallocHitTail2E.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSPeW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SpineMallocS12iW2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section HIT0E.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S6S12VCST;R1A2S12S21R2A2S14F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S6S12VCST;R1A2S15S22R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
ScVAInv;VW;Vst;VA;VKc;S4PcA1A6").
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x17fbdc 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 2.
Let st0 : ustop := UStopLe.

Theorem emalloc_hit_2_P : ltac2:(tb__ "0|4|
S1cS8S2SfS1fQ40M0A1A1SfS11S17S19A2M1A1S18Vsegs;S16R3R2R1A5S1S23G1S10S17S19SdS7VW0;Vst0;A3SbVAInv;VCST;VXGL;R6R5A5A4R2A3S9R6A1S13S6S1dR8S20G0S3R6PcA2A2A2Z0A3S2S0Vsegs;S5Vsegs;S1eVW0;Vst0;RaR9R8A5M2S1bVW0;Vst0;Z4M3A3R1R7A5R5A3FrhoE;F_;S2S0Vsegs;S5Vsegs;G2S1aVW0;Vst0;G3Z8A4R1R7A5R5A3FrhoE;S0Vsegs;S5Vsegs;VJ;VW0;Vst0;RaR9A4SaS7VW0;Vst0;A3R8R7A5R5A3F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Posts Q HPin HKc HREF HSEC.
  assert (HUS : stopJ_stable W0 st0) by (apply stopJ_stable_le).
  assert (HW : st0 = UStopLeOrPc -> W0 = []) by (intros E; discriminate E).
  apply (espine_s1 2%nat st0 4 law_die WC1_2 DC1_2 NXhi_0 NXlo_0 ECert1_0 A Kc rho tp Q HW HUS HKc Wa_0 Da_0 Wb_0 Fbh_0 Fbl_0); [|exact HSEC].
  intros rhoE1.
  apply (espine_s2c 2%nat st0 4 OVa_2 OVb_2 TABa_2 TABb_2 Wa'_2 Wb'_0 Da'_2 Db'_0 NXa_2 NXb_0 Fa_0 Fb_0 Ga_0 Gb_0 SKa_0 SKb_0 XXa_0 XXb_0 XFa_0 XFb_0
           W1a_0 W1ba_0 W1ca_0 W2a_0 W1ra_0 W2ra_0 W1b_0 W1bb_0 W1cb_0 W2b_0 W1rb_0 W2rb_0 sa_0 sra_0 sb_0 srb_0 ENTa_0 ENTra_0 ENTb_0 ENTrb_0
           SIDa_0 SIDra_0 SIDb_0 SIDrb_0 FB_0 FBr_0 NXC1g_0 s2_ecert_2 A Kc rho tp Q HW HUS HKc).
  2: { intros Hz0 rhoE2. apply (espine_s3r 2%nat st0 4 NXC2r_0 s3r_ecert_2 A Kc rho tp Q HUS HKc). exact (HREF Hz0). }
  intros rhoE2.

  apply (espine_s3p_cert 2%nat st0 4 NXC2p_0 s3p_ecert_2 A Kc rho tp Q HUS HKc).
  exact (emalloc_hit_tail_2_P CST XGL HCST HXGL HCSTM HCSTD A Kc rho tp Posts HPin HKc).
Qed.

Theorem emalloc_hit_2 : ltac2:(tb__ "0|3|
S1cS8S2SfS1fQ40M0A1A1S18Vsegs;S16R2R1SeS7VAInv;VCST;VXGL;VW0;Vst0;R4R3A8A5S1S9R4A1S13S6S1dR6S20G0S3R4PcA2A2A2Z0A3S2S0Vsegs;S5Vsegs;S1eVW0;Vst0;R8R7R6A5M1S1bVW0;Vst0;Z4M2A3R1R5A5R4A3FrhoE;F_;S2S0Vsegs;S5Vsegs;G1S1aVW0;Vst0;G2Z8A4R1R5A5R4A3FrhoE;S0Vsegs;S5Vsegs;VJ;VW0;Vst0;R8R7A4SaS7VW0;Vst0;A3R6R5A5R4A3F_;F_;F_;TQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp. exact (emalloc_hit_2_P A Kc rho tp (Posts_malloc AE_A AInv CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0E.
