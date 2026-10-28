(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma region_kept_live_blk : forall (MR : MR_t) (LAWS : MR_laws ubs2_msyms MR) E (mem mem' : word -> option byte) n lo hi wlo whi cs b m L2 A2 md2,
bv_unsigned (ew E n) = b -> heap_ok MR L2 A2 mem' md2 -> In (b, m) (blocks L2 A2) ->
(forall i, 0 <= i < m -> mbyte ubs2segs mem' (b + i) = mbyte ubs2segs mem (b + i)) ->
0 <= lo -> hi <= m -> 0 <= wlo -> whi <= m ->
region_kept ubs2segs E mem mem' (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros MR LAWS E mem mem' n lo hi wlo whi cs b m L2 A2 md2 Hn HH Hin Hk Hlo Hhi Hwlo Hwhi.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; rewrite Hn; intros a Ha.
- replace a with (b + (a - b)) by lia. apply Hk. lia.
- intros _. apply (present_writable ubs2_msyms). replace a with (b + (a - b)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem' md2 b m (a - b) HH Hin ltac:(lia))).
Qed.
End c.
