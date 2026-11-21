(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import ItB_base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
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
  Variables (lf wf cf : Z -> Z) (lo codes : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis Hlf : forall i, 0 <= i < 320 -> 0 <= lf i < 65536.
  Hypothesis Hlo : 0 <= lo.
  Hypothesis Hlc : lo + codes <= 320.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hl15 : forall s, 0 <= s < codes -> lf (lo + s) <= 15.

  Notation LP := (S + 168 + 2 * lo).
  Notation ST := (bst SP SPA S F PB LP TY gp tp FR fc).

  Definition cnt_post (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (offs : Z -> Z) (next bitsw : word)
      (x1 x7 x25 x28 x29 x30 x31 : word) : machine_state -> Prop :=
    fun ms' => exists (m : amem) (q5 q6 q10 q11 q12 q13 q14 q15 q16 q17 : word),
      ms' = ST x1 q5 q6 x7 q10 q11 q12 q13 q14 q15 q16 q17 x25 x28 x29 x30 x31 0x96fc8 m
      /\ itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144
                 (arr_get (cntA lf lo codes)) offs lf wf cf next bitsw.

  Lemma it_count_loop : forall (k : nat) (i : Z) (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (offs : Z -> Z) (next bitsw : word)
      (x1 x6 x7 x11 x25 x28 x29 x30 x31 : word),
    Z.of_nat k = codes - i -> 0 <= i < codes ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144
            (arr_get (cntK lf lo i)) offs lf wf cf next bitsw ->
    evtF bsegs RNG (cnt_post v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 offs next bitsw
                             x1 x7 x25 x28 x29 x30 x31)
      (ST x1 (Z_to_bv 64 (LP + 2 * i)) x6 x7 (Z_to_bv 64 (LP + 2 * i)) x11 (Z_to_bv 64 (2 * i)) (Z_to_bv 64 (Z.lxor (F + 32) 18446744073709551615))
          (Z_to_bv 64 (Z.land LP 1)) (Z_to_bv 64 (Z.lxor LP 18446744073709551615)) (Z_to_bv 64 (2 * codes)) (Z_to_bv 64 16) x25 x28 x29 x30 x31
          0x96f48 m).
  Proof using All.
    induction k as [|k IH]; intros i m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 offs next bitsw
      x1 x6 x7 x11 x25 x28 x29 x30 x31 Hk Hi INV; [lia|].
    open_ctx CX. open_inv INV. unfold bst.
    pose proof (Hlf (lo + i) ltac:(lia)) as L0. pose proof (Hl15 i Hi) as L15.
    pose proof (cntK_le lf lo i (lf (lo + i)) ltac:(lia) ltac:(lia)) as CK.
    replace (S + 168 + 2 * lo + 2 * i) with (S + 168 + 2 * (lo + i)) by lia.
    zs. ubg. zs. ubg.
    do 4 zs.
    pose proof (f16arr_read bsegs m (S + 168) 320 lf (lo + i) _ LENS ltac:(lia) eq_refl) as RD.
    zs. rewrite (zx16_small (lf (lo + i))) by lia. clear RD.
    zs. ubg.
    zs. setreg 11 (Z_to_bv 64 (2 * lf (lo + i))) ltac:(rewrite shl1_2x; reflexivity).
    zs. ubg.
    zs.
    do 4 zs.
    f16_open_at CNT (lf (lo + i)) C EC CH CC.
    zs. rewrite (sx16_small (arr_get (cntK lf lo i) (lf (lo + i)))) by lia.
    do 4 zs.
    f16_close_at CH CC EC (arr_get (cntK lf lo i) (lf (lo + i)) + 1) CNT; [reflexivity|].
    assert (CNT' : f16arr bsegs m0 (F + 32) 16 (arr_get (cntK lf lo (i + 1)))).
    { eapply f16arr_ext; [exact CNT|]. intros j Hj. rewrite (cntK_step lf lo i) by lia.
      apply fupd_arr_set. rewrite cntK_len. lia. }
    clear CNT. subst C.
    zs. zs. zbr0 K.
    -
      setreg 5 (Z_to_bv 64 (S + 168 + 2 * lo + 2 * (i + 1))) ltac:(f_equal; lia).
      setreg 10 (Z_to_bv 64 (S + 168 + 2 * lo + 2 * (i + 1))) ltac:(f_equal; lia).
      setreg 12 (Z_to_bv 64 (2 * (i + 1))) ltac:(f_equal; lia).
      eapply (IH (i + 1)); [lia | lia |].
      close_inv.
    -
      zs. apply evtF_done. unfold cnt_post. exists m0. do 10 eexists. split; [reflexivity|].
      replace codes with (i + 1) by lia. rewrite cntA_eq.
      close_inv.
  Qed.

  Lemma it_count : forall (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (offs : Z -> Z) (next bitsw : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144
            (fun _ => 0) offs lf wf cf next bitsw ->
    evtF bsegs RNG (cnt_post v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 offs next bitsw
                             x1 x7 (Z_to_bv 64 codes) x28 x29 x30 x31)
      (ST x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 codes) x28 x29 x30 x31 0x96f1c m).
  Proof using All.
    intros. rename H into INV.
    assert (INV0 : itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144
                           (arr_get (cntK lf lo 0)) offs lf wf cf next bitsw).
    { destruct INV as (MI & MU & WM & FRM & CNT & REST). split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact FRM|].
      split; [| exact REST]. eapply f16arr_ext; [exact CNT|]. intros j Hj. cbv beta.
      unfold cntK. rewrite itm_count_k_0 by lia. rewrite it_zero_count_spec. reflexivity. }
    clear INV. open_ctx CX. unfold bst. zs. zbr0 K.
    -
      apply evtF_done. unfold cnt_post. exists m. do 10 eexists. split; [reflexivity|].
      replace codes with 0 by lia. rewrite cntA_eq. exact INV0.
    - zs. ubg. zs. zs. zs. zs. zs. zs.
      setreg 16 (Z_to_bv 64 (2 * codes)) ltac:(rewrite zext32_shift31 by lia; reflexivity).
      zs. zs. zs.
      pose proof (it_count_loop (Z.to_nat codes) 0 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 offs next bitsw
                    x1 x6 x7 x11 (Z_to_bv 64 codes) x28 x29 x30 x31 ltac:(lia) ltac:(lia) INV0) as HL.
      rewrite Z.mul_0_r, Z.add_0_r in HL. exact HL.
  Qed.
End P.
End CANSEC1.
