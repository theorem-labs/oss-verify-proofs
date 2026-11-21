(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the failed RI mmap's path of the fourth start-up segment runs on the states B/StartRegenS2b.v computes per CONFIG_RSEQ, with its spin run and CFG check per value of the flag in B/StartRegen2b.v; the theorem takes the flag, its statement written as plain text). *)

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartRegenS2 StartRegenS2b StartRegen2b.
(* LPS 727298f3: the path's states are those B/StartRegenS2b.v computes per CONFIG_RSEQ (Start4FailR,
   from Start4R's [E_k8x r]); its spin run and check are B/StartRegen2b.v's [spin_ok r] and
   [check_s8f r].  B/ne.v and B/ng.v are read for the path's constants only. *)
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS2.Start4R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS2b.Start4FailR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegen2b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section S8F.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S20S16S2S17Q40A1A1S2S11A1M0S10R5R4R3R2R1A4SdG0R3S1S11A1A3F_;Fmd;Ftr;Ftp;Frho;S21S8Vok;R2A3F_;FJ;").

Theorem s8_fail_safe : forall (r : bool) (m : Model) (B : Z) (rho : valuation) (tp : list (bv 64)) (Q : assn),
  triple segsA ok (SPA segsA (KxA m B) (fail_state (E_k8x r)) rho tp) Q.
Proof.
  intros r m B rho tp Q.
  assert (OKJ : ok_frameA segsA ok (KxA m B)) by (apply OKF; intros; eapply KxA_nil; eassumption).
  change (fail_state (E_k8x r)) with (F0 r).
  apply (cfg_soundA segsA FUEL1 [PC_OUT; PC_SPIN] 31 [F0 r; C2 r] [E_spin r] (KxA m B) ok Q tp OKJ (stableA_KxA segsA 31 m B) (check_s8f r)).
  - intros E rho' [<-|[]]. apply (triple_spinA ok (KxA m B) (E_spin r) rho' tp); [exact OKJ | apply stableA_KxA | destruct r; reflexivity | destruct r; exact (spin_ok _)].
  - left. reflexivity.
Qed.
End S8F.
