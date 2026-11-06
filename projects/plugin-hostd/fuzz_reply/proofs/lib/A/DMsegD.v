(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMsegD.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 9f30f6f20663) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 1 code pcs the tool read as sizes, by funcpair.py), and 18 pcs named in comments; no other numeral changed. *)
(* The Drain walk's cut at MergeBatches' entry, over the Drain shell of YFgj (same Section variables).

   After the transfer (0x33838-0x338a4), Drain tail-jumps into Recycle (0x3393c -> 0x33990, frame 0x50), which
   takes the cache lock and tests the batch bytes [LBv] against the batch count [LSZv] (0x339f0-0x33a14):
   - 0x339fc bltu: bytes < LSZv * kBatchBytes -> the CHECK_GE die path 0x33b58 (excluded by the premise);
   - 0x33a00 bgeu / 0x33a14 bgeu: no merge -> 0x33a4c (YFgj.at_L0 at the dequeue loop head 0x33a8c);
   - else (kBatchBytes * L < bytes < 2 * kBatchBytes * L): 0x33a18-0x33a30 save a0..a3 in s0..s4, a0 := the global
     list (inst + 0xa0 of the Quarantine object, A_QUAR + 160), a1 := Recycle's sp (the temp list), and
     0x33a34 jal MergeBatches (0x33b74): [at_MB].
   [postDm] is YFgj.postD with that third case. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFgj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (gq tq : qcache).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Local Notation LSZv := (AFgj.LSZv gq tq).
Local Notation LBv := (AFgj.LBv gq tq).
Local Notation LFv := (AFgj.LFv ly gq tq).
Local Notation TLv := (AFgj.TLv ly tq).
Local Notation TFv := (AFgj.TFv ly tq).
Local Notation GLv := (AFgj.GLv ly gq).
Local Notation WIN := (AFgj.WIN ly regs0 gq).
Local Notation MEQ := (AFgj.MEQ ly regs0 mem0 gq).
(* The registers MergeBatches' caller keeps from Drain's entry (s0..s4 now hold Recycle's arguments). *)
Definition SREGS_M : list (bv 5) := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_MB (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33b74) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = w64 (sp0 - 80) /\ getr regs' 1 = w64 0x33a38 /\
getr regs' 10 = w64 (A_QUAR + 160) /\ getr regs' 11 = w64 (sp0 - 80) /\
getr regs' 12 = w64 (T + t_cache) /\ getr regs' 13 = getr regs0 13 /\
getr regs' 8 = w64 (A_QUAR + 160) /\ getr regs' 9 = w64 kQuarantineMin /\ getr regs' 18 = w64 A_QUAR /\
getr regs' 19 = getr regs0 13 /\ getr regs' 20 = w64 (T + t_cache) /\
(forall r : bv 5, In r SREGS_M -> getr regs' r = getr regs0 r) /\
MEQ mem' /\
(forall a, WIN a -> kHighMemBeg <= a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m (A_QUAR + 152) 4 257 /\
val_mem tfibsegs m (A_QUAR + 160) 8 LSZv /\ val_mem tfibsegs m (A_QUAR + 168) 8 LFv /\
val_mem tfibsegs m (A_QUAR + 176) 8 TLv /\ val_mem tfibsegs m (A_QUAR + 184) 8 LBv /\
val_mem tfibsegs m (T + t_qc) 8 0 /\ val_mem tfibsegs m (T + t_qc + 8) 8 0 /\ val_mem tfibsegs m (T + t_qc + 16) 8 0 /\ val_mem tfibsegs m (T + t_qc + 24) 8 0 /\
(forall lastb initr, rev (qc_list gq) = lastb :: initr -> val_mem tfibsegs m GLv 8 TFv) /\
val_mem tfibsegs m (sp0 - 80) 8 0 /\ val_mem tfibsegs m (sp0 - 72) 8 0 /\ val_mem tfibsegs m (sp0 - 64) 8 0 /\ val_mem tfibsegs m (sp0 - 56) 8 0 /\
val_mem tfibsegs m (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\ val_mem tfibsegs m (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
val_mem tfibsegs m (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\ val_mem tfibsegs m (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
val_mem tfibsegs m (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\ val_mem tfibsegs m (sp0 - 8) 8 (bv_unsigned (getr regs0 1)).
(* Recycle's merge test (0x33a00 / 0x33a14), as merge_split_cf states it. *)
Definition merge_test : bool := (kBatchBytes * LSZv <? LBv) && (LBv <? 2 * (kBatchBytes * LSZv)).
Definition postDm : world tfibsegs -> config -> Prop :=
if LBv <=? kQuarantineMax then AFgj.at_RETD W ly regs0 mem0 md0 gq tq
else if merge_test then at_MB else AFgj.at_L0 W ly regs0 mem0 md0 gq tq.
End d.
End c.
