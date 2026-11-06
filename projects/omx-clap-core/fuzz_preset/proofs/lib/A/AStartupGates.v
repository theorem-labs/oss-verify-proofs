(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: acceptance gates of omx-clap-core/fuzz_preset's start-up certificate (image A,
   pin 1be0f53d96cb9d6c, twin bff8519bbe3ea0e4). Each gate is checked against the start-up certificate's STATE AT MAIN:
   every one of the 50 hand-off states HS_tfib_list (the checker's own run, A/AB01.v) must know the cell, by the same
   xcell test A/AD1g.v applies to every const cell (tfib_holes_if). These cells are in .bss: their FILE byte is 0 and
   start-up's init sets them, so a file-byte check of them could not fail; this one can, and the NEGATIVE CONTROLS
   below show it rejecting a wrong value.
   asan_inited (__asan::asan_inited, 1 byte, 0xabb98) = 1 at main.
   malloc_context_size (common_flags + 36 = 0x13ca0c, 4 bytes) = 30 at main; the state holds it as the high half of
   the 8-byte cell at common_flags + 32 (0x13ca08), whose value 0x1e00010000 has 30 in its bytes 4..7 (and 1 at byte 2,
   fast_unwind_on_malloc). *)
(* Generator: tools/startup/gen_gates.py sha256 4ede9a3948ae2c8b668812e2014eea087f1a54fffe59edf92a30961a6fb922d1; twin sha256 bff8519bbe3ea0e4d8edf35fa48015b5846960886633a77a5e9f86cb565bd590; pin sha256 1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44; template sha256 02a9d18b9a28328cc32e6835581cb262a28a73c83e07f71d9d13c889c48719ed; A/AF0m.v blob 97f423adf6ebdee1e409e001a5e3cb7acc241b0a; A/AB01.v blob d18d06d86ad4f8c265d5659d2c10228cdcb642aa; A/AImgCells.v blob b5ce63262b021e413490a266a2d787ea30ed0bba. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12 AB1h AB13 AB01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m AD1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AImgCells.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.
Definition A_ASAN_INITED : Z := 0xabb98.
Definition A_CF_32 : Z := 0x13ca08.
Definition CELL_ASAN_INITED : acell := z1 (ANum A_ASAN_INITED) 1.
Definition CF_32_VAL : Z := 0x1e00010000.   (* common_flags + 32 .. + 39 at main: +34 = 1 (fast_unwind_on_malloc), +36 .. +39 = 30 (malloc_context_size) *)
Definition CELL_MALLOC_CONTEXT : acell := z8 (ANum A_CF_32) CF_32_VAL.
Lemma malloc_context_size_is_30 : (CF_32_VAL / 2 ^ 32) mod 2 ^ 32 = 30.
Proof. reflexivity. Qed.
(* the seventh certificate fact: fast_unwind_on_malloc = 1 at main. common_flags + 0x22 (0x13ca0a), 1 byte (byte 2 of the
   certified cell CELL_MALLOC_CONTEXT), is what ___interceptor_malloc (0x539e0), ___interceptor_free (0x53880) and
   ___interceptor_realloc (0x53c7c) load with `lbu` and pass as request_fast to BufferedStackTrace::UnwindImpl
   (0x5b4d4); with it 0 the unwind would be UnwindSlow (libunwind, whose allocations no walk covers). *)
Lemma fast_unwind_on_malloc_field_is_1 : (CF_32_VAL / 2 ^ 16) mod 2 ^ 8 = 1.
Proof. reflexivity. Qed.
Definition CELL_FAST_UNWIND_ON_MALLOC : acell := z1 (ANum (A_CF_32 + 2)) 1.
Definition A_ASAN_FLAGS_24 : Z := 0xa86d0.
Definition AF_24_VAL : Z := 0x101010000000001.   (* asan_flags 0xa86b8 + 24 .. + 31 at main: bytes 0..3 = report_globals = 1 *)
Definition CELL_REPORT_GLOBALS : acell := z8 (ANum A_ASAN_FLAGS_24) AF_24_VAL.
Lemma report_globals_is_1 : AF_24_VAL mod 2 ^ 32 = 1.
Proof. reflexivity. Qed.
(* detect_stack_use_after_return, the flags-struct field asan_flags + 0x1f = 0xa86d7 (FlagHandler<bool>), is byte 7
   of the same certified cell: 1 at main. AsanInitInternal + 0x13c (0x5a5c4) copies it into the 4-byte option the
   instrumented prologues read, __asan_option_detect_stack_use_after_return (CELL_UAR below). *)
Lemma detect_stack_use_after_return_field_is_1 : (AF_24_VAL / 2 ^ 56) mod 2 ^ 8 = 1.
Proof. reflexivity. Qed.
(* the option cell the instrumented code reads: __asan_option_detect_stack_use_after_return (twin .symtab, 4 bytes,
   .bss, file bytes 0), AImgCells.A_UAR_OPT; = 1 at main. Its .got slot AImgCells.A_GOT_UAR_OPT (.got, image bytes)
   holds its address; the prologues load the slot, then the 4-byte flag, and branch on it (`lw a2, 0(a2)`; `beqz a2`
   past their frame_alloc call: round_trip_text 0x849cc / 0x849d8, check_round_trip 0x828c8 / 0x828d4,
   check_reject_clean_starved 0x821c4 / 0x821d0, the internal file neutral_dis.py on 1be0f53d96cb9d6c). *)
Definition CELL_UAR : acell := z4 (ANum AImgCells.A_UAR_OPT) 1.
Definition CELL_GOT_UAR : acell := z8 (ANum AImgCells.A_GOT_UAR_OPT) AImgCells.A_UAR_OPT.
(* what the pinned run sets: nothing. __asan_default_options (0x81134) returns the .rodata string
   "allocator_may_return_null=1" (0x1de9b), which names no stack flag, and GetEnv (0x65580) returns NULL whenever the
   .got word AImgCells.A_GOT_SEALED_FLAG is non-zero (`ld a1, 0(.got 0xa2050)`; `beqz a1`; `li a0, 0`; `ret`), so no
   ASAN_OPTIONS string is ever parsed. CELL_SEALED pins that word at main. *)
Definition CELL_SEALED : acell := z8 (ANum AImgCells.A_GOT_SEALED_FLAG) AImgCells.A_SEALED_FLAG_VALUE.
Definition A_CF_F0 : Z := 0x13cad8.
Definition CF_F0_VAL : Z := 0x101000100000000.   (* common_flags 0x13c9e8 + 0xf0 .. + 0xf7 at main: bytes 0..3 = compress_stack_depot = 0; value copied by script from A/AF0m.v's certified cell, not typed (the field CompressThread::NewWorkNotify+? and CompressStackStore read with `lw` at CF+0xf0, 0x73388 / 0x73b80) *)
Definition CELL_COMPRESS : acell := z8 (ANum A_CF_F0) CF_F0_VAL.
Lemma compress_stack_depot_is_0 : CF_F0_VAL mod 2 ^ 32 = 0.
Proof. reflexivity. Qed.
Definition A_INST_28 : Z := 0xa7880.
Definition RTO_VAL : Z := 0xffffffff.   (* __asan::instance 0xa7858 (twin .symtab) + 0x28 = release_to_os_interval_ms (s32); value copied by script from A/AF0m.v's certified cell; the 50 states carry KWord a_off 686208 w 4 (ELit 2^64 - 1) *)
Definition CELL_RTO : acell := z8 (ANum A_INST_28) RTO_VAL.
(* release_to_os_interval_ms < 0 at main: its s32 has the sign bit set. This makes the refill guard at PopulateFreeArray +
   0x260 (0x37a10, `bltz a1` with a1 = lw 0x28(a0), the primary allocator's own field) take the never-release arm,
   so the non-negative arm's MonotonicNanoTime call (0x37a1c) and with it clock_gettime are dead. cgif's value is
   the same, -1 (its YF0m.v:120, guard at 0x3679c). *)
Lemma release_to_os_interval_negative : 2 ^ 31 <= RTO_VAL mod 2 ^ 32.
Proof. unfold RTO_VAL. vm_compute. intro H. discriminate H. Qed.
Section gates. Context {fx : YK11.FPState}.
Lemma gate_asan_inited_at_main : forallb (fun ch => xcell ch CELL_ASAN_INITED) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gate_malloc_context_size_at_main : forallb (fun ch => xcell ch CELL_MALLOC_CONTEXT) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gate_fast_unwind_on_malloc_at_main : forallb (fun ch => xcell ch CELL_FAST_UNWIND_ON_MALLOC) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gate_compress_stack_depot_at_main : forallb (fun ch => xcell ch CELL_COMPRESS) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
(* NEGATIVE CONTROL for a cell whose true value is 0: the same test rejects compress_stack_depot = 1 in every state.
   (A file-byte check of this .bss cell reads 0 and would pass whatever start-up did; this test cannot.) *)
Lemma control_compress_1_rejected : existsb (fun ch => xcell ch (z8 (ANum A_CF_F0) (CF_F0_VAL + 1))) HS_tfib_list = false.
Proof. vm_compute. reflexivity. Qed.
Lemma gate_release_to_os_interval_at_main : forallb (fun ch => xcell ch CELL_RTO) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
(* NEGATIVE CONTROL: the same test rejects a NON-NEGATIVE interval (0) in every state *)
Lemma control_rto_0_rejected : existsb (fun ch => xcell ch (z8 (ANum A_INST_28) 0)) HS_tfib_list = false.
Proof. vm_compute. reflexivity. Qed.
Lemma gate_report_globals_at_main : forallb (fun ch => xcell ch CELL_REPORT_GLOBALS) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
(* the gates are cells of the certified constant list, so AD1g's tfib_holes_if covers them as well *)
Lemma gate_cells_in_const : In CELL_ASAN_INITED Tfib_const_abs /\ In CELL_MALLOC_CONTEXT Tfib_const_abs /\ In CELL_REPORT_GLOBALS Tfib_const_abs /\ In CELL_COMPRESS Tfib_const_abs /\ In CELL_RTO Tfib_const_abs /\
In CELL_UAR Tfib_const_abs /\ In CELL_GOT_UAR Tfib_const_abs /\ In CELL_SEALED Tfib_const_abs.
Proof. repeat split; vm_compute; repeat (first [left; reflexivity | right]). Qed.
(* the sixth certificate fact: detect_stack_use_after_return = 1 at main, with its .got slot and the GetEnv seal *)
Lemma gate_detect_stack_use_after_return_at_main : forallb (fun ch => xcell ch CELL_UAR) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gate_got_uar_at_main : forallb (fun ch => xcell ch CELL_GOT_UAR) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gate_getenv_sealed_at_main : forallb (fun ch => xcell ch CELL_SEALED) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
(* NEGATIVE CONTROLS: the same test rejects the flag OFF (0, its file value), a wrong .got word, and an open GetEnv
   (seal word 0), in every state *)
Lemma control_uar_0_rejected : existsb (fun ch => xcell ch (z4 (ANum AImgCells.A_UAR_OPT) 0)) HS_tfib_list = false.
Proof. vm_compute. reflexivity. Qed.
Lemma control_got_uar_wrong_rejected : existsb (fun ch => xcell ch (z8 (ANum AImgCells.A_GOT_UAR_OPT) (AImgCells.A_UAR_OPT + 8))) HS_tfib_list = false.
Proof. vm_compute. reflexivity. Qed.
Lemma control_sealed_0_rejected : existsb (fun ch => xcell ch (z8 (ANum AImgCells.A_GOT_SEALED_FLAG) 0)) HS_tfib_list = false.
Proof. vm_compute. reflexivity. Qed.
(* NEGATIVE CONTROLS: the same test rejects the wrong value (the file byte 0) in every state *)
Lemma control_asan_inited_0_rejected : existsb (fun ch => xcell ch (z1 (ANum A_ASAN_INITED) 0)) HS_tfib_list = false.
Proof. vm_compute. reflexivity. Qed.
Lemma control_malloc_context_0_rejected : existsb (fun ch => xcell ch (z8 (ANum A_CF_32) 0)) HS_tfib_list = false.
Proof. vm_compute. reflexivity. Qed.
Lemma control_fast_unwind_on_malloc_0_rejected : existsb (fun ch => xcell ch (z1 (ANum (A_CF_32 + 2)) 0)) HS_tfib_list = false.
Proof. vm_compute. reflexivity. Qed.
Lemma control_report_globals_0_rejected : existsb (fun ch => xcell ch (z8 (ANum A_ASAN_FLAGS_24) 0)) HS_tfib_list = false.
Proof. vm_compute. reflexivity. Qed.
(* report_globals = 1 (< 2) is what makes __asan_register_globals' UnwindImpl(fatal) dead: it sits behind the
   `report_globals >= 2` verbosity test whose result goes to StackTrace::Print, not to a Report* call. The other half
   is the GetEnv seal, A/AImgCells.v's A_GOT_SEALED_FLAG 0xa2050 = 1 (GetEnv 0x65580), itself a const cell of
   Tfib_const_abs and so certified in all 50 states by A/AD1g.v's tfib_holes_if. *)
End gates.
