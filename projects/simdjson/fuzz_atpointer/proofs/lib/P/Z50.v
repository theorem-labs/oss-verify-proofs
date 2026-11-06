(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu Zpz.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Zp8.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw Zwn Zpw Z44 Z72.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z4d Z51 Z53 Z58.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis S2 : stage2t_stmt.
  Hypothesis ROOT : forall E, aenv_ok E -> atp_root_stmt E.

  Theorem rfuzz_one_of_parts : rfuzz_one_stmt.
  Proof.
    unfold rfuzz_one_stmt. intros until canary.
    intros HEAP LXS SJS SEW SSP AUX SPB B63 ST CEIL GLO LO ERR TP MI AL16 PL FRM HA0 HA1.
    unfold Z3o.fuzz_one, fuzz_one_with. cbn [bind ret lib_malloc lib_free lops Target.ops cho].
    eapply (lftoi_vec_cps HM HF); try eassumption.
    cbv beta. intros v st1 ms1 VP. unfold vec_post in VP.
    destruct VP as (x1 & t0' & t1' & t2' & xs0 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & xs2 & xs3 & xs4 & xs5 & xs6 & t3' & t4' & t5' & t6' & m1 & errv1 & A & cap & bv & jr
                    & jo & c48 & c56 & c64 & c72 & c80 & j88 & jr0 & jr8 & jr16 & jr20 & j169 & jn
                    & -> & -> & CAPB & MI1 & ST1 & ERR1 & AUX1 & FA1 & SO1 & HEAP1 & VR1 & PRES1 & SJS1 & PL1 & OUT & RES & PARS & XFD & ROOTC & SAVE).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK in LO.
    eapply (lftoi_parse_cps HM HF S2) with (m0 := m) (s00 := s) (init := init);
      [exact HEAP| exact LXS| exact HEAP1| exact AUX1| lia| exact B63| exact ST1| exact CEIL| exact GLO| unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK; lia
      | exact ERR1| exact MI1| replace (bv_unsigned sp - 256 + 256) with (bv_unsigned sp) by lia; exact AL16| exact FRM| exact FA1| exact SO1
      | exact VR1| exact CAPB| exact PRES1| exact SJS1| exact PL1| exact OUT| exact RES| exact PARS| exact XFD| exact ROOTC| exact SAVE|].
    cbv beta. intros psb ptp pim pix poc pia st2 ms2 GP.
    eapply (lftoi_back HF ROOT) with (m0 := m); eassumption.
  Qed.
End Proofs.
End WithCeiling0.
