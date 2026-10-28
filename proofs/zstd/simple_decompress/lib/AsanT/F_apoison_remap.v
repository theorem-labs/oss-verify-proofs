(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanCtrlProps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit ARep F_apoison APoisonR_iface F_apoisonz.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC2. Context {rc : runConstT}.
Theorem poison_remap_proof : poison_remap_stmt.
Proof.
  unfold poison_remap_stmt.
  intros until junk. intros ST CEIL LO MI PC PRM RR E0 E1 E2 AL SL SPOS HI HCE BIG DST RIMG RSTK RSH KONT.
  eapply (poison0_spec_gen R k Q RNG) with (addr := addr) (size := size) (lo := lo) (junk := junk); try eassumption.
  intros RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PP.
  eapply KONT. unfold poison0_post in PP. destruct PP as (LE & MUp & WMp & MIp & STp & SHZ & PC' & PRM' & _).
  unfold premap_post.
  split; [exact LE|]. split; [exact MUp|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|].
  split; [exact SHZ|]. split; [eapply rng_fp_le; [exact LE| exact RSH]|]. split; [exact PC'| exact PRM'].
Qed.
Definition poison_remap : poison_remap_stmt := poison_remap_proof.
End CANSEC2.
