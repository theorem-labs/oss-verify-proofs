(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import PropExec MState Mem Frame Exec RegsEquiv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CkP Require Import RegsFull.
Require OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk
        OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Frame OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec
        OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module OP := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Module OC := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Module OS := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Module OF := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Frame.
Module OH := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Module OR := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.RefMemcpyLib.

Lemma mkst_MS : forall (R F : bvmap 5 word) (pc : word) (fc : bv 32) (m ro : word -> option byte),
  @OP.mkst (OP.mkFP F fc) R pc m ro = MS R F pc fc None m ro.
Proof. reflexivity. Qed.

Lemma msteps_conv : forall segs a b, OC.msteps segs a b -> msteps segs a b.
Proof.
  intros segs a b H. induction H as [ms|ms ms' ms'' Hsvc Hstep _ IH]; [apply msteps_refl|].
  eapply msteps_cons; [split; [exact Hsvc| exact Hstep]| exact IH].
Qed.

Lemma rdn_conv : forall segs m a n, OP.rdn segs m a n = rdn segs m a n.
Proof. intros segs m a n. revert a. induction n as [|n IH]; intros a; [reflexivity|]. cbn [OP.rdn rdn]. rewrite IH. reflexivity. Qed.

Lemma getr_reg_get : forall (R : bvmap 5 word) (r : reg), is_x0 r = false -> OP.getr R r = reg_get R r.
Proof. intros R r H. unfold OP.getr. rewrite OP.bv_eqb0_is_x0, H. reflexivity. Qed.

Section GetR.
Variables x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word.
Local Notation RR := (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
End GetR.




Section WithSegs.
Variable segs : list Segment.

Lemma mem_grows_wmono : forall m m', OS.mem_grows m m' -> wmono segs m m'.
Proof.
  intros m m' HG x Hx. unfold wview in *. destruct (m x) as [b|] eqn:E.
  - specialize (HG x ltac:(rewrite E; discriminate)). destruct (m' x); [discriminate| contradiction].
  - destruct (m' x); [discriminate| exact Hx].
Qed.


Lemma evt_of_msteps_mkR : forall (Q : machine_state -> Prop) (R F : bvmap 5 word) (pc pc' : word) (fc : bv 32) (m m' ro : word -> option byte) (R' : bvmap 5 word),
  rfull R ->
  OC.msteps segs (@OP.mkst (OP.mkFP F fc) R pc m ro) (@OP.mkst (OP.mkFP F fc) R' pc' m' ro) ->
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
     R' = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ->
     Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc' fc None m' ro)) ->
  evt segs Q (MS R F pc fc None m ro).
Proof.
  intros Q R F pc pc' fc m m' ro R' HR HS HQ.
  apply msteps_conv in HS. rewrite !mkst_MS in HS.
  pose proof (msteps_rfull segs _ _ HS HR) as HR'. cbn [ms_regs MS] in HR'.
  destruct HR' as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & E).
  exists (MS R' F pc' fc None m' ro). split; [exact HS|]. rewrite E. apply HQ. exact E.
Qed.
End WithSegs.
