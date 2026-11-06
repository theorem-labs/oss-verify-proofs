(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages ITreeA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BM_monadx BM_syscalls BM_stdio_lib BX_file BM_stdio_write BP_policy BP_mjx BP_fwritex BP_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Flush.
Variable P : acc -> Prop.
Hypothesis PSTK : POL_STACK P.
Hypothesis PIMG : POL_IMG P.
Hypothesis PHSH : POL_HSH P.
Hypothesis PLSH : POL_LSH P.
Hypothesis PNUL : POL_NUL P.

Theorem stdio_write_flush_proof : stdio_write_flush_stmt P.
Proof.
  unfold stdio_write_flush_stmt. intros until canary. intros SINK -> -> -> ST LO GLO SPHI TOP SEPB SSP MI.
  destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO & BSTK & MJ). cbn [fst] in FC, BUF, LEN.
  unfold in_stackw in BSTK. unfold OUT_DEPTH, GLOBALS_TOP, TOPOK_stk, A_STK_HI, A_CEIL in *.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
  assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
  pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
  apply bytes_at_app in BY as [BY _].
  eapply implMA_mono.
  { eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := RSTDERR) (buf := buf) (s := []) (S := 0) (lo := lo) (canary := canary)
      (wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
      try reflexivity; try lia.
    - intros a k H1 H2. apply PSTK; lia.
    - exact PIMG.
    - intros a k H1 H2. apply PIMG; lia.
    - intros a k H1 H2. apply PSTK; lia.
    - intros a k H1 H2. destruct k; [apply PNUL|]. exfalso. unfold zlength in H2. cbn [length] in H2. lia.
    - exact FC.
    - exact BY.
    - apply bytes_at_nil. unfold zlength; cbn [length]. lia.
    - exact ST.
    - unfold STDIO_WRITE_DEPTH. lia.
    - exact SSP.
    - exact MI.
    - unfold got_ssp. lia.
    - unfold ssp_guard. lia.
    - unfold zlength in *; cbn [length]. lia.
    - unfold zlength; cbn [length]. lia.
    - left. reflexivity. }
  cbv beta. intros [] st' ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FC' & SSP' & ->).
  unfold STDIO_WRITE_DEPTH in MU.
  unfold stdio_write_flush_post. do 16 eexists. split; [reflexivity|].
  assert (MU2 : munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (B, B + 80)] m m').
  { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. unfold STDIO_WRITE_DEPTH in *. intros; lia. }
  split; [exact MU2|].
  split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [| exact SSP'].
  (* [comment removed for export] *)
  exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
  split. { rewrite Z.add_0_r. exact FC'. }
  split; [exact FL32|]. split; [exact FL8|].
  split.
  { (* [comment removed for export] *)
    eapply (rw_cells_transport _ _ m m'); [exact BUF | exact MU | exact WM |].
    cbn. unfold zlength in *. lia. }
  split. { unfold zlength in *. cbn [length]. rewrite length_app. unfold zb. rewrite length_map. lia. }
  split; [exact BHI|]. split; [exact BGLO|]. split; [exact BSTK|].
  eapply mjx_transport; [exact MJ | exact MU2 | exact WM |].
  unfold mjx_ok_iv, A_CEIL, A_STK_HI. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
Qed.
End Flush.
End RC__1.
