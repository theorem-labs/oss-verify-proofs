(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "KcA"; "JL_malloc_ok"; "Kc_ok"; "L_malloc_ok"; "Wcan"; "ulink"; "ustop"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.MallocAsmS.ASMS"; "PostsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceS"; "malloc_contractA_strong"; "malloc_contractA_strong_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2 TopGlueA MallocHit0 MallocHit0E.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require MallocHit2E IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ka.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ks.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ku.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.TopGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.MallocHit0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.MallocHit0E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.MallocHit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.MallocHit2E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ka.SpineMallocSecOK0S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kh.SpineMallocSecOK0SE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineMallocSecOK0SW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ku.SpineMallocSecOK0SEW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.MallocHitTail0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.MallocHitTail0E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.MallocHitTail2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lw.MallocHitTail2E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.RefillPlug0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m0.RefillPlug2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section ASMS.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SaSbVCST;R1A2SbS2aR2A2S18F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
SaSbVCST;R1A2SbS2cR2A2S18F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SaSbVCST;R1A2S1aS2bR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segsA.

Definition PostsS (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : list (axst * jpostA) := ltac2:(tb__ "0|1|
S14S13SeSfA2M0S12SeSfS6S2VW;Vst;A3S4VAInv;VCST;VXGL;VA;VKc;A5A4S15G0A1A3").
Lemma PostsS_ok : ltac2:(tb__ "0|0|
S11S8A1S9S17S3S2dS13SeSfA2S12SeSfS6S2R4R3A3S4VAInv;VCST;VXGL;R2R1A5A4S16R4R3R2R1A4A3FKc;FA;Fst;FW;").
Proof. intros. left. reflexivity. Qed.

Definition HREFS_stmt (nW : nat) (tmax : Z) : Prop := ltac2:(tb__ "0|2|
S26OF_;S17S3ScS11S22Q40M0A1A1S5R3A1S1eS0R6S1dR4A1A3S27S0R7S1dR5A1A3S19SaS20R7S23G0SdR5PcA2A2A2Z0A3ScS25S0RaS1cS0S21S7VnW;A1M1S1R9R8R7A5S1fG1S1Vtmax;A3R1R6A5S10S0S1bR7R6S16G1S1R9R8A4A5A4FrhoE;F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition HREFES_stmt (nW : nat) (tmax : Z) : Prop := ltac2:(tb__ "0|2|
S17S3ScS11S22Q40M0A1A1S5R3A1S19SaS20R5S23G0SdR3PcA2A2A2Z0A3ScS24S0S1cS0S21S7VnW;A1M1S1R7R6R5A5S1fG1S1Vtmax;A3R1R4A5S10S0S1bR5R4S16G1S1R7R6A4A5A3FrhoE;F_;F_;Ftp;Frho;FKc;FA;").

Lemma HREFS0 : HREFS_stmt 0 2.
Proof.
  intros ok A Kc rho tp HKc Hokl Hokp Hcnt rhoE.
  apply (refill_core_0 CST XGL HCST HXGL Kc (triple segsA ok) (TRok_triple Kc ok Hokl Hokp) HKc (PF_ok CST XGL (Wcan 0) UStopLe) (posts_conv_ok CST XGL (Wcan 0) UStopLe)); [|exact Hcnt].
  intros A' rho' tp' rX. exact (malloc_hit_tail_0_P CST XGL HCST HXGL HCSTM HCSTD ok A' Kc rho' tp' _ (PostsS_ok (Wcan 0) UStopLe A' Kc) HKc Hokl Hokp rX).
Qed.
Lemma HREFS2 : HREFS_stmt 2 4.
Proof.
  intros ok A Kc rho tp HKc Hokl Hokp Hcnt rhoE.
  apply (refill_core_2 CST XGL HCST HXGL Kc (triple segsA ok) (TRok_triple Kc ok Hokl Hokp) HKc (PF_ok CST XGL (Wcan 2) UStopLe) (posts_conv_ok CST XGL (Wcan 2) UStopLe)); [|exact Hcnt].
  intros A' rho' tp' rX. exact (malloc_hit_tail_2_P CST XGL HCST HXGL HCSTM HCSTD ok A' Kc rho' tp' _ (PostsS_ok (Wcan 2) UStopLe A' Kc) HKc Hokl Hokp rX).
Qed.
Lemma HREFES0 : HREFES_stmt 0 2.
Proof.
  intros A Kc rho tp HKc Hcnt rhoE.
  apply (refill_core_0 CST XGL HCST HXGL Kc (etriple segsA) (TRok_etriple Kc) HKc (PF_ok CST XGL (Wcan 0) UStopLe) (posts_conv_ok CST XGL (Wcan 0) UStopLe)); [|exact Hcnt].
  intros A' rho' tp' rX. exact (emalloc_hit_tail_0_P CST XGL HCST HXGL HCSTM HCSTD A' Kc rho' tp' _ (PostsS_ok (Wcan 0) UStopLe A' Kc) HKc rX).
Qed.
Lemma HREFES2 : HREFES_stmt 2 4.
Proof.
  intros A Kc rho tp HKc Hcnt rhoE.
  apply (refill_core_2 CST XGL HCST HXGL Kc (etriple segsA) (TRok_etriple Kc) HKc (PF_ok CST XGL (Wcan 2) UStopLe) (posts_conv_ok CST XGL (Wcan 2) UStopLe)); [|exact Hcnt].
  intros A' rho' tp' rX. exact (emalloc_hit_tail_2_P CST XGL HCST HXGL HCSTM HCSTD A' Kc rho' tp' _ (PostsS_ok (Wcan 2) UStopLe A' Kc) HKc rX).
Qed.

Theorem malloc_contract_A_strong : ltac2:(tb__ "0|0|
S28S0S2VAInv;VCST;VXGL;A5").
Proof.
  intros W st ok A Kc rho tp HW HKc Hokl Hokpl HROOMw.
  apply (triple_pre_pure segsA ok _ _ (alloc_roomA A (bv_unsigned (rw rho 12%positive)))).
  { intros [tr cf] Hw. exact (HROOMw tr cf Hw). }
  intros HROOM.
  eapply triple_conseq; [apply SPA_malloc_T | intros w Hw; exact Hw |].
  destruct HW as [E|[E|[]]]; injection E as <- <-.
  - exact (malloc_hit_0_P CST XGL HCST HXGL HCSTM HCSTD ok A Kc rho tp _ (PostsS_ok (Wcan 0) UStopLe A Kc) HKc Hokl Hokpl
             (fun Hz rhoE => HREFS0 ok A Kc rho tp HKc Hokl Hokpl Hz rhoE)
             (malloc_sec_ok_0_S CST XGL HCST HXGL HCSTM HCSTS HCSTD (PostsS (Wcan 0) UStopLe) (PostsS_ok (Wcan 0) UStopLe) ok A Kc rho tp HKc Hokl Hokpl HROOM)).
  - exact (malloc_hit_2_P CST XGL HCST HXGL HCSTM HCSTD ok A Kc rho tp _ (PostsS_ok (Wcan 2) UStopLe A Kc) HKc Hokl Hokpl
             (fun Hz rhoE => HREFS2 ok A Kc rho tp HKc Hokl Hokpl Hz rhoE)
             (malloc_sec_ok_2_S CST XGL HCST HXGL HCSTM HCSTS HCSTD (PostsS (Wcan 2) UStopLe) (PostsS_ok (Wcan 2) UStopLe) ok A Kc rho tp HKc Hokl Hokpl HROOM)).
Qed.

Theorem malloc_contract_A_strong_ex : ltac2:(tb__ "0|0|
S29S0S2VAInv;VCST;VXGL;A5").
Proof.
  intros W st A Kc rho tp HW HKc HROOMw.
  apply (etriple_pre_pure segsA _ _ (alloc_roomA A (bv_unsigned (rw rho 12%positive)))).
  { intros [tr cf] Hw. exact (HROOMw tr cf Hw). }
  intros HROOM.
  eapply etriple_conseq; [apply SPA_malloc_T | intros w Hw; exact Hw |].
  destruct HW as [E|[E|[]]]; injection E as <- <-.
  - exact (emalloc_hit_0_P CST XGL HCST HXGL HCSTM HCSTD A Kc rho tp _ (PostsS_ok (Wcan 0) UStopLe A Kc) HKc
             (fun Hz rhoE => HREFES0 A Kc rho tp HKc Hz rhoE)
             (emalloc_sec_ok_0_S CST XGL HCST HXGL HCSTM HCSTS HCSTD (PostsS (Wcan 0) UStopLe) (PostsS_ok (Wcan 0) UStopLe) A Kc rho tp HKc HROOM)).
  - exact (emalloc_hit_2_P CST XGL HCST HXGL HCSTM HCSTD A Kc rho tp _ (PostsS_ok (Wcan 2) UStopLe A Kc) HKc
             (fun Hz rhoE => HREFES2 A Kc rho tp HKc Hz rhoE)
             (emalloc_sec_ok_2_S CST XGL HCST HXGL HCSTM HCSTS HCSTD (PostsS (Wcan 2) UStopLe) (PostsS_ok (Wcan 2) UStopLe) A Kc rho tp HKc HROOM)).
Qed.
End ASMS.
