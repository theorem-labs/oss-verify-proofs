(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACfl.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/ACfl.v of this library, made the way derive_y.py makes lib/AU from lib/A: module names A.Axyz -> AU.Yxyz (AWalkFw0 -> AU.AWalkFw0, A.ACeg -> AU.YCeg), lib/Reusable Requires kept, and every address re-measured on the asan-ubsan image (internal path) (sha256 f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82), not copied from the asan file. A_EMPTY is the one that moves: 0x5d0be0 here, 0x5d0ba0 in lib/A/ACfl.v. EV_LIB, LIVE_LIB and LLVMF_STK are image-independent budgets copied from lib/A/ACfn.v / ACfl.v. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0s YP09.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCe5.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YCeg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* asan-ubsan fuzz_knock.nm.txt:2068 `000000000007eed0 0000000000000578 T LLVMFuzzerTestOneInput`;
   asan-ubsan fuzz_knock.objdump.txt `000000000007eed0 <LLVMFuzzerTestOneInput>:` / `7eed0: f4010113 addi sp,sp,-192`. *)
Definition A_LLVMF : Z := 0x7eed0.
(* the return address of target_run's call: asan-ubsan fuzz_knock.objdump.txt
   `7edc8: 108000ef jal 7eed0 <LLVMFuzzerTestOneInput>`, next instruction `7edcc: 00050993 mv s3,a0`. *)
Definition RA_LLVMF : Z := 0x7edcc.
(* asan-ubsan fuzz_knock.nm.txt:975 `00000000005d0be0 0000000000000020 b oft_aligned_copy.empty`; target_run forms it
   at objdump `7ed34: auipc a1,0x552` / `7ed38: addi s4,a1,-356 # 5d0bd0 <target_run.initialized>` and
   `7edac: 010a0493 addi s1,s4,16`, passed by `7edc0: mv a0,s1`. The asan twin's value is 0x5d0ba0. *)
Definition A_EMPTY : Z := 0x5d0be0.
(* image-independent budgets, copied from lib/A/ACfl.v / ACfn.v. *)
Definition EV_LIB : Z := 2000.
Definition LIVE_LIB : Z := 2 ^ 33.
Definition LLVMF_STK : Z := 32768.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tfib_lib_contract (B : asyms) : Prop :=
forall ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n,
afn_pre tfibsegs B LLVMF_STK ly S W regs mem md [] ->
raZ regs = RA_LLVMF ->
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
frames S = [] -> st_nev S + EV_LIB <= EV_MAX -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
SRr tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
ajournal tfibsegs B LLVMF_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
exists leak, Permutation (ablocks B ly' S') (leak ++ ablocks B ly S) /\
(leak = [] \/ exists a m, leak = [(a, m)] /\ 0 <= m < 3 * 2 ^ 16)).
End b.
