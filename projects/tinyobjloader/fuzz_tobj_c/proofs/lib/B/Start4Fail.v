(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "true"; "Some"; "bool"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "mkLeafA"; "sym_runA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4FailCut"; "E_spin"; "C2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start4FailStates"; "PC_SPIN"; "F0"; "FUEL1"; "PC_OUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "E_k8x"; "fail_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ne.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start4FailStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4FailCut.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma spin_ok : ltac2:(tb__ "0|1|
SdS6S2SaA1M0A1ScS8U2S0S7S12S1S7A1A3SeS3A5S4G0S0SaSbSeS1dA2S1SaA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma check_s8f : ltac2:(tb__ "0|1|
SdS5S1eS8S14S0S7S15S0S7S12S1S7A1A3A3P1fS0S9S13S0S9SfS1S9A1M0A3A3S0S9SeG0A3A6S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section S8F.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S20S16S2S17Q40A1A1S2S11A1M0S10R5R4R3R2R1A4SdG0R3S1S11A1A3F_;Fmd;Ftr;Ftp;Frho;S21S8Vok;R2A3F_;FJ;").

Theorem s8_fail_safe : ltac2:(tb__ "0|0|
S10S7S16S2S17Q40A1A1S1bS1cS8Vok;S1fS8S18R5R4A2S1aS19A1R3R2A5R1A4FQ;Ftp;Frho;FB;Fm;").
Proof.
  intros m B rho tp Q.
  assert (OKJ : ok_frameA segsA ok (KxA m B)) by (apply OKF; intros; eapply KxA_nil; eassumption).
  change (fail_state E_k8x) with F0.
  apply (cfg_soundA segsA FUEL1 [PC_OUT; PC_SPIN] 31 [F0; C2] [E_spin] (KxA m B) ok Q tp OKJ (stableA_KxA segsA 31 m B) check_s8f).
  - intros E rho' [<-|[]]. apply (triple_spinA ok (KxA m B) E_spin rho' tp); [exact OKJ | apply stableA_KxA | reflexivity | exact spin_ok].
  - left. reflexivity.
Qed.
End S8F.
