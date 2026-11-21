(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Malloc Require Import F_am_A F_am_K.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.

Section CANSEC1. Context {rc : runConstT}.
Definition am_init_st (st : mstate) : mstate :=
  if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

End CANSEC1.
