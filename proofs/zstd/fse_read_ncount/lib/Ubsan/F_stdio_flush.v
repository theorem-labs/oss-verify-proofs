(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_syscalls F_printf_iface F_stdio_write StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Theorem stdio_write_flush_proof : stdio_write_flush_stmt.
Proof.
unfold stdio_write_flush_stmt. intros until canary. intros SINK -> -> -> ST LO GLO SPHI SEPB SSP MI.
destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO). cbn [fst] in FC, BUF, LEN.
unfold OUT_DEPTH, GLOBALS_TOP in *.
pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
Local Ltac2 Set LiaHints.tbl := fun () => "00R0>1022551726.59 14003936005.5915611896614.8016451674837.5917207757472.8020638285087.5921893744088.592659082097.59 27874655001.5929158771112.5729570283451.5933349666099.5933593929797.5939657619045.5940072193256.5942148970988.5946493764493.5950093979609.5951359764854.5953237369230.5953519253561.5956406556289.5957622410744.8259230584638.595977813253.59 59850698631.5961116472386.596340305863.56 66142504428.5966232523617.5966938009126.597486760002.59 8836835345.59 940469664.59  00000100200700800I00J00K00L00Q00R00S00T00Z00[00\00a01601:01;01<01=01>01H01P01Q01Z01[01_01`01h01i01j022023FSS3LENSS4BGLO2LO4SEPB2BBFFFS3GLOSFFS4SPHISFS3GLOS3LEN4BGLO4SEPB2BB2LRS2LOFFSFS2LO3GLO1HS3LEN2LRSS4BGLO2BBSS2BBSS3BHI2BBFSS3BHI2BBF".
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
apply bytes_at_app in BY as [BY _].
eapply implM_mono.
{ eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 125936) (buf := buf) (s := []) (S := 0) (lo := lo) (canary := canary)
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
- unfold zlength in *; cbn [length]. lia.
- left. reflexivity. }
cbv beta. intros [] st' ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FC' & SSP' & ->).
unfold STDIO_WRITE_DEPTH in MU.
unfold stdio_write_flush_post. do 16 eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. unfold STDIO_WRITE_DEPTH in *. intros; lia. }
split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [| exact SSP'].
exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
split. { rewrite Z.add_0_r. exact FC'. }
split; [exact FL32|]. split; [exact FL8|].
split.
{
eapply (rw_cells_transport _ _ m m'); [exact BUF | exact MU | exact WM |].
cbn. unfold zlength in *. lia. }
split; [| split; [exact BHI| exact BGLO]]. unfold zlength in *. cbn [length]. rewrite length_app. unfold zb. rewrite length_map. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
