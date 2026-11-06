(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfm.v at c8557374ad2e, with its module paths changed: lines 1-14 are taken, lines 15-20 (the harness constants) are restated with libreac/fuzz_knock's values, each with its evidence, and lines 21-39 (cgif's harness contract tfib_lib_contract, whose post-condition admits cgif's leak) are left out: the knock harness contract is a Theorem Labs lane's. These are the ASAN image's values (fuzz_knock.asan, sha256 61768cf4739b...). The asan-ubsan twin lib/AU/YCfm.v must NOT copy them: there A_EMPTY is 0x5d0be0 (.bss +0x40), not 0x5d0ba0. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0s YP09.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 ACeh.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* knock symtab: LLVMFuzzerTestOneInput = 0x7eed0, its first instruction `addi sp,sp,-192` (both ASan images). *)
Definition A_LLVMF : Z := 0x7eed0.
(* the return address of `jal 0x108` at 0x7edc8 in target_run (target_run+0xcc), whose target is 0x7eed0 (both ASan images). *)
Definition RA_LLVMF : Z := 0x7edcc.
(* port_addr_check.py maps cgif 0x5d8660 (oft_aligned_copy.empty+0x0) to 0x5d0ba0; target_run.initialized = 0x5d0b90 is formed
   at 0x7ed34 auipc a1,0x552 / 0x7ed38 addi s4,a1,-0x1a4. *)
Definition A_EMPTY : Z := 0x5d0ba0.   (* &oft_aligned_copy.empty (32-byte .bss, nm:975) = target_run.initialized + 16; formed at target_run 0x7edac addi s1,s4,16, passed by 0x7edc0 mv a0,s1 / 0x7edc8 jal LLVMFuzzerTestOneInput; asan 0x5d0ba0, asan-ubsan twin 0x5d0be0 *)
(* [INFERENCE] until a Theorem Labs lane's APgMain typechecks: the harness journal has k = 0 (stack_malloc keeps st_nev, YC85.v:365).
   cgif's value is 2000; a Theorem Labs lane's plan (an internal record:86) proposed 2000 as slack. *)
Definition EV_LIB : Z := 0.
(* the donor value (a Theorem Labs lane's plan :86-87: knock's plain spec has no budget). *)
Definition LIVE_LIB : Z := 2 ^ 33.
(* the stack budget of the harness and its callees for afn_pre, the donor value (a Theorem Labs lane's plan :88: needs >= 208 +
   max(ESTACK, callee STK), about 4.4 KB); not the harness frame, which is 192 bytes. *)
Definition LLVMF_STK : Z := 32768.
