(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bs X1c2 X1bn X1cc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gj X1fl X1ei X1ea X1fr X1gg.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Theorem stdio_write_flush_proof : stdio_write_flush_stmt.
Proof.
unfold stdio_write_flush_stmt. intros until canary. intros SINK -> -> -> ST LO GLO SPHI SEPB SSP MI.
first [ sf_destruct 11%nat SINK as flags mode tail rest FC FL32 FL8 BUF LEN BHI BGLO | sf_fb; destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO) ]. cbn [fst] in FC, BUF, LEN.
unfold OUT_DEPTH, GLOBALS_TOP in *.
pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
apply bytes_at_app in BY as [BY _].

assert (BT : B + 80 <= TASK_SIZE) by exact (wr_at_below _ _ _ _ MI (proj2 BUF) ltac:(cbn; lia)).
eapply implM_mono.
{ eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 250128) (buf := buf) (s := []) (S := 0) (lo := lo) (canary := canary)
(wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
try reflexivity; try lia.
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
first [ sf_destruct 23%nat PO as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' ST' FC' SSP' -> | sf_fb; destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FC' & SSP' & ->) ].
unfold STDIO_WRITE_DEPTH in MU.
unfold stdio_write_flush_post. sf_eexists 16%nat. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. unfold STDIO_WRITE_DEPTH in *. intros; lia. }
split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [| exact SSP'].

first [ unshelve sf_eexists 4%nat; [ exact (flags) | exact (mode) | exact (tail) | exact ((zb buf ++ rest)) | ] | sf_fb; exists flags, mode, tail, (zb buf ++ rest) ]. cbn [fst].
split. { rewrite Z.add_0_r. exact FC'. }
split; [exact FL32|]. split; [exact FL8|].
split.
{
eapply (rw_cells_transport _ _ m m'); [exact BUF | exact MU | exact WM |].
cbn. unfold zlength in *. lia. }
split; [| split; [exact BHI| exact BGLO]]. unfold zlength in *. cbn [length]. rewrite length_app. unfold zb. rewrite length_map. lia.
Qed.
