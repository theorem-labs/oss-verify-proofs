(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import F_syscalls F_printf_iface F_stdio_write StdioFiles Stdio_kit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg MonadF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Theorem stdio_write_flush_proof : stdio_write_flush_stmt.
Proof.
  unfold stdio_write_flush_stmt. intros until canary. intros SINK -> -> -> ST LO GLO SPHI SEPB SSP MI RSTK RIMG RB R0.
  destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO). cbn [fst] in FC, BUF, LEN.
  unfold OUT_DEPTH, GLOBALS_TOP in *.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
  Local Ltac2 Set LiaHints.tbl := fun () => "00[0>1022551726.65 14003936005.6515611896614.8616451674837.6517207757472.8620638285087.6521893744088.6524400993639.652659082097.65 29158771112.6329570283451.6532782333415.6533349666099.6533593929797.653394109735.65 34001667906.6536405888793.6538904281761.6539657619045.6540003895694.6540072193256.6541994782400.6542148970988.6546493764493.6550093979609.6551359764854.6553519253561.6556406556289.6557622410744.8857643476229.6559230584638.6559850698631.6561917045697.6561928856784.656340305863.62 63857250370.6565440274022.6566142504428.6566232523617.656685819.65    67084129609.658836835345.65 940469664.65  00000100200700800I00J00K00L00M00N00O00P00Q00W00X00Y00^00_00`00a00b00c00h01=01A01B01C01D01V01W01_01h01l01m02102202302402<02=02H02P02QFSS3LENSS4BGLO2LO4SEPB2BBFFFFSFFFS4SPHIFSS3GLOSSFFFS3GLOS3LEN4BGLO4SEPB2BB2LRS2LOFSFS2LO3GLO4SEPB2BB1HSS3LEN2LRS4BGLO2BBS2BBFS2BBSFSS3BHI2BBSS3LEN2BB2LRS3BHI2BBF".
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
  pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
  apply bytes_at_app in BY as [BY _].
  eapply implAM_mono.
  { eapply (stdio_write_spec (St:=St) RNG) with (B := B) (fd := 2) (Fp := 644584) (buf := buf) (s := []) (S := 0) (lo := lo) (canary := canary)
      (wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
      try reflexivity; try lia.
    - exact FC.
    - exact BY.
    - apply bytes_at_nil. unfold zlength; cbn [length]. lia.
    - exact ST.
    - unfold STDIO_WRITE_DEPTH. lia.
    - unfold GLOBALS_TOP in *. lia.
    - exact SSP.
    - exact MI.
    - unfold got_ssp. lia.
    - unfold ssp_guard. lia.
    - unfold zlength in *; cbn [length]. lia.
    - left. reflexivity.
    - solve_rng.
    - eapply rng_sub; [exact RIMG| lia| lia].
    - eapply rng_sub; [exact RB| lia| unfold zlength in *; lia].
    - (* [comment removed for export] *) unfold zlength; cbn [length Z.of_nat]. apply (rng0_use _ _ R0). lia.
    - exact RIMG.
    - unfold zlength in *; cbn [length]. lia.   (* [comment removed for export] *) }
  cbv beta. intros [] st' ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FC' & SSP' & ->).
  unfold STDIO_WRITE_DEPTH in MU.
  unfold stdio_write_flush_post. do 16 eexists. split; [reflexivity|].
  split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. unfold STDIO_WRITE_DEPTH in *. intros; lia. }
  split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [| exact SSP'].
  (* [comment removed for export] *)
  exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
  split. { rewrite Z.add_0_r. exact FC'. }
  split; [exact FL32|]. split; [exact FL8|].
  split.
  { (* [comment removed for export] *)
    eapply (rw_cells_transport _ _ m m'); [exact BUF | exact MU | exact WM |].
    cbn. unfold zlength in *. lia. }
  split; [| split; [exact BHI| exact BGLO]]. unfold zlength in *. cbn [length]. rewrite length_app. unfold zb. rewrite length_map. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
