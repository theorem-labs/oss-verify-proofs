(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import ItB_base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top TY : Z) (m1 : amem).
  Variables (lf wf cf : Z -> Z) (lo codes bits : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hbits : 1 <= bits <= 15.

  Notation LP := (S + 168 + 2 * lo).
  Notation ST := (bst SP SPA S F PB LP TY gp tp FR fc).
  Notation cA := (arr_get (cntA lf lo codes)).
  Notation mx := (mxA lf lo codes).
  Notation SHPB := (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)).

  Lemma cA_range : forall j, 0 <= cA j <= codes.
  Proof. intros j. rewrite cntA_eq. apply cntK_le; lia. Qed.

  Definition max_post (m : amem) (x1 x5 x6 x7 x11 x12 x16 x17 x25 x28 x29 x30 x31 : word) : machine_state -> Prop :=
    fun ms' => exists (q10 q15 : word),
      (ms' = ST x1 x5 x6 x7 q10 x11 x12 SHPB (Z_to_bv 64 bits) (Z_to_bv 64 mx) x16 x17 x25 x28 x29 x30 x31 0x970c4 m /\ 2 <= mx)
      \/ (ms' = ST x1 x5 x6 x7 q10 x11 x12 SHPB (Z_to_bv 64 bits) q15 x16 x17 x25 x28 x29 x30 x31 0x97bd4 m
          /\ forall j, 2 <= j <= 15 -> cA j = 0).

  Ltac max_found k ZZ NZ :=
    zs; zs; apply evtF_done; unfold max_post; eexists; exists (Z_to_bv 64 0); left;
    assert (MXK : mx = k) by (unfold mxA; apply (mx_found _ k); [lia | exact ZZ | exact NZ]);
    rewrite MXK; split; [reflexivity | lia].
  Ltac max_zero k ZZ K :=
    let ZZ' := fresh "ZZ" in
    assert (ZZ' : forall j, k - 1 < j <= 15 -> cA j = 0)
      by (let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; destruct (Z.eq_dec j k) as [->|]; [exact K | apply ZZ; lia]);
    clear ZZ K; rename ZZ' into ZZ.
  Ltac max_stage k CR ZZ :=
    let K := fresh "K" in
    zs; rewrite (zx16_small (cA k)) by apply CR;
    zs; zbr K; [ max_zero k ZZ K | max_found k ZZ K ].

  Lemma it_max : forall (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (offs : Z -> Z) (next : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144
            cA offs lf wf cf next (Z_to_bv 64 bits) ->
    evtF bsegs RNG (max_post m x1 x5 x6 x7 x11 x12 x16 x17 x25 x28 x29 x30 x31)
      (ST x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 0x96fc8 m).
  Proof using All.
    intros. rename H into INV. open_ctx CX. open_inv INV. unfold bst.
    pose proof (f16arr_to_cells bsegs m (F + 32) 16 _ CNT) as CC.
    cbv [fws map seq Z.of_nat Pos.of_succ_nat Pos.succ] in CC.
    assert (CR : forall j, 0 <= cA j < 65536) by (intros j; pose proof (cA_range j); lia).
    pose proof (CR 15) as R15. pose proof (CR 14) as R14. pose proof (CR 13) as R13. pose proof (CR 12) as R12.
    pose proof (CR 11) as R11. pose proof (CR 10) as R10. pose proof (CR 9) as R9. pose proof (CR 8) as R8.
    pose proof (CR 7) as R7. pose proof (CR 6) as R6. pose proof (CR 5) as R5. pose proof (CR 4) as R4.
    pose proof (CR 3) as R3. pose proof (CR 2) as R2.
    zs. ubg. zs. zs. ubg.
    do 4 zs.
    zs. rewrite (zx16_small (cA 15)) by apply CR.
    zs. rewrite (sx32_small bits) by lia.
    assert (ZZ : forall j, 15 < j <= 15 -> cA j = 0) by (intros; lia).
    zs. zbr K15; [ max_zero 15 ZZ K15 | max_found 15 ZZ K15 ].
    max_stage 14 CR ZZ. max_stage 13 CR ZZ. max_stage 12 CR ZZ. max_stage 11 CR ZZ. max_stage 10 CR ZZ.
    max_stage 9 CR ZZ. max_stage 8 CR ZZ. max_stage 7 CR ZZ. max_stage 6 CR ZZ. max_stage 5 CR ZZ.
    max_stage 4 CR ZZ. max_stage 3 CR ZZ.
    zs. rewrite (zx16_small (cA 2)) by apply CR. zs. zbr0 K2.
    2:{ zs. apply evtF_done. unfold max_post. eexists. exists (Z_to_bv 64 0). left.
        assert (MXK : mx = 2) by (unfold mxA; apply (mx_found _ 2); [lia | exact ZZ | exact K2]).
        rewrite MXK. split; [reflexivity | lia]. }
    max_zero 2 ZZ K2.
    apply evtF_done. unfold max_post. do 2 eexists. right. split; [reflexivity|]. intros j Hj. apply ZZ. lia.
  Qed.
End P.
End CANSEC1.
