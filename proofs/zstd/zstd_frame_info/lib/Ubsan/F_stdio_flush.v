(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_syscalls F_printf_iface F_stdio_write StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Theorem stdio_write_flush_proof : stdio_write_flush_stmt.
Proof.
  unfold stdio_write_flush_stmt. intros until canary. intros SINK -> -> -> ST LO GLO SPHI SEPB SSP MI.
  destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO). cbn [fst] in FC, BUF, LEN.
  unfold OUT_DEPTH, GLOBALS_TOP in *.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
  Local Ltac2 Set LiaHints.tbl := fun () => "00R0>1022551726.59 14003936005.5915611896614.8016451674837.5917207757472.8020638285087.5921893744088.592659082097.59 29158771112.5729570283451.5933349666099.5933522364805.5933593929797.5936179806274.5939657619045.5940072193256.5942148970988.5943009432642.5946493764493.5950093979609.5951359764854.5953519253561.5956406556289.5956832220390.5957622410744.8259230584638.5959850698631.5960524134041.596340305863.56 66142504428.5966232523617.5968035864206.598836835345.59 940469664.59  00000100200700800I00J00K00L00M00N00O00P00V00W00X00Y00^00_01401801901:01;01<01N01V01_01d01h01i02102202:02;FSS3LENSS4BGLO2LO4SEPB2BBFFFSFFSS4SPHISSFS3GLOSS3LEN4BGLO4SEPB2BB2LRS2LOFSFFS2LO3GLO4SEPB2BB1HS3LEN2LRS4BGLO2BBS3GLOS2BBSS3BHI2BBFS3BHI2BBF".
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
  pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
  apply bytes_at_app in BY as [BY _].
  eapply implM_mono.
  { eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 122104) (buf := buf) (s := []) (S := 0) (lo := lo) (canary := canary)
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
