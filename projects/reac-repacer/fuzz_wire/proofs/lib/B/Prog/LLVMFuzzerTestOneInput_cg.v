(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* LLVMFuzzerTestOneInput_cg: the statement of the walk of fuzz_wire.asan-ubsan's LLVMFuzzerTestOneInput (wire_text of
   lib/B/Prog/WirePAddr.v, AF_LLVMFuzzerTestOneInput = 0 of lib/B/Prog/WirePList.v; YCfn.A_LLVMF = 0x7fbf8), as a
   STATEMENT only (no proof): the callee contracts give the core's slot.

   The C (fuzz_wire.c LLVMFuzzerTestOneInput, fuzz.h fuzz_dup): return 0 unless 1 <= size < FUZZ_INPUT_MAX (64 MiB);
   bcast = data[0] & 1, slot = (data[0] >> 1) - 2, n = min(size - 1, W_RECV_MAX = 1600); f = fuzz_dup(data + 1, n)
   (malloc(n ? n : 1), abort on NULL, memcpy when n <> 0); the seven checks check_forward (f, n, bcast), check_ret
   (f, n), check_downstream (f, n), check_meter (f, n), check_counter (f, n), check_width (n), check_read (f, n, slot);
   c = fuzz_dup(f, n); len = check_copy (c, f, n); check_read (c, len, slot) when len <> 0; free (c); free (f); return 0.

   The code (listing of image B, 428 bytes), every value measured on fuzz_wire.asan-ubsan, by role:
     role                                                            value
     entry (wire_text = YCfn.A_LLVMF)                                0x7fbf8
     frame (`addi sp, sp, -0x40`; saves ra, s0 .. s6)                0x40
     refusal: `bltu` of size - 2^26 against 2^64 - 2^26 + 1 (taken iff
       size = 0 or size >= 2^26) to the `li a0, 0` of the return     +0x30 -> +0x160
     s4 = data                                                       +0x34
     UBSan trap: data = NULL (`beqz a0`) to `unimp`                  +0x38 -> +0x18c
     shadow base through its .got word (auipc / ld / ld)             +0x3c .. +0x44, .got 0x98878 -> cell 0xa07f8
     shadow byte of data[0] (`lb`); nonzero: the slow path           +0x50; +0x54 -> +0x19c
     slow path (`andi a2, s4, 7`; `blt` back) else report            +0x19c .. +0x1a4
     __asan_report_load1 (data[0])                                   +0x1a8
     UBSan trap: data + 1 wraps (`beq s4, -1`) to `unimp`            +0x5c -> +0x18c
     s6 = size - 1; s1 = n = min(s6, 1600)                           +0x60 .. +0x70
     flag byte data[0] (`lbu s2`)                                    +0x74
     s3 = n + (n == 0) (`seqz`, `add`)                               +0x78, +0x7c
     malloc trampoline (block f), its return address                 +0x84, 0x7fc80
     NULL result to __asan_handle_no_return / abort                  +0x88 -> +0x190 / +0x194
     s0 = f, unchanged to the epilogue's `ld s0` (no frame pointer)  +0x8c .. +0x168
     s5 = bcast, s2 = slot                                           +0x94, +0x98
     __asan_memcpy (f, data + 1, n); skipped when s6 = 0 (`beqz`)    +0xac; +0x9c
     check_forward (f, n, bcast)                                     +0xbc
     check_ret (f, n)                                                +0xc8
     check_downstream (f, n)                                         +0xd4
     check_meter (f, n)                                              +0xe0
     check_counter (f, n)                                            +0xec
     check_width (n)                                                 +0xf4
     check_read (f, n, slot)                                         +0x104
     malloc trampoline (block c, size s3), its return address        +0x10c, 0x7fd08
     NULL result to __asan_handle_no_return / abort                  +0x110 -> +0x190 / +0x194
     __asan_memcpy (c, f, n); skipped when s6 = 0 (`beqz`)           +0x128; +0x118
     len = check_copy (c, f, n)                                      +0x138
     check_read (c, len, slot) unless len = 0 (`beqz a0`)            +0x14c; +0x13c
     free trampoline (c), its return address                         +0x154, 0x7fd50
     free trampoline (f), its return address                         +0x15c, 0x7fd58
     return 0 (`li a0, 0`), epilogue, `ret`                          +0x160, +0x188
     `unimp` after abort (no branch reaches it)                      +0x198
     runtime: malloc / free trampolines, __asan_memcpy               0x52098 / 0x52094, 0x50c14
     runtime: the allocator's trace pc (malloc / free)               0x52334 / 0x521d4
   It calls no fake stack and no __asan_memset, and passes no pointer into its own frame to any callee: f and c are
   heap blocks. The size refusal comes before any read of data, call or heap access (only the saves precede it), so
   size = 0 (p = A_EMPTY) and size >= 2 ^ 26 return 0 at once. The two UBSan
   traps are refuted by the slot's own premise (0 < size < 2 ^ 26 and (data, size) in ablocks: 4096 <= data, and the block ends
   at or below alloc_ceiling); __asan_report_load1 by the shadow of the live input block (size >= 1); the abort by the
   malloc rule (no NULL). *)
From Stdlib Require Import ZArith NArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00 YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YE01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v YCfn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require ZTraceSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import PaBase WirePSyms WirePAddr WirePList WirePImg WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require check_forward_cg check_ret_cg check_downstream_cg
  check_meter_cg check_counter_cg check_width_cg check_read_cg check_copy_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI16.
Module ZTS := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.ZTraceSpec.
Module PFWD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_forward_cg.
Module PRET := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_ret_cg.
Module PDS := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_downstream_cg.
Module PMET := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_meter_cg.
Module PCNT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_counter_cg.
Module PWID := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_width_cg.
Module PRD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_read_cg.
Module PCPY := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_copy_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The entry, as the listing names it (WirePImg.v WIRE_A_LLVMF = wire_text + AF_LLVMFuzzerTestOneInput); it is the
   core's YCfn.A_LLVMF. *)
Lemma wire_a_llvmf_eq : WIRE_A_LLVMF = A_LLVMF.
Proof. reflexivity. Qed.

(* The return addresses of its allocator calls, as offsets from its entry (the jal is 4 bytes before): malloc at
   +0x84 and +0x10c, free at +0x154 and +0x15c (0x7fc80, 0x7fd08, 0x7fd50, 0x7fd58). *)
Definition WIRE_LLVMF_RA_MALLOC1 : Z := WIRE_A_LLVMF + 0x88.
Definition WIRE_LLVMF_RA_MALLOC2 : Z := WIRE_A_LLVMF + 0x110.
Definition WIRE_LLVMF_RA_FREE1 : Z := WIRE_A_LLVMF + 0x158.
Definition WIRE_LLVMF_RA_FREE2 : Z := WIRE_A_LLVMF + 0x160.

(* The frame cut (fuzz_wire.c `n = W_RECV_MAX`, fuzz.h W_RECV_MAX; `li a0, 1600` at +0x64): the largest frame length,
   so the largest size of each of the three blocks f, c and check_copy's u. *)
Definition WIRE_RECV_MAX : Z := 1600.

(* The statement the walk (cgif's lib/A/ACfj.v composition, at fuzz_wire's callees) will prove: the callee contracts
   give the slot, at the core's shape checksum_shape and with XL as both meter bounds (ACfj.v). *)
Section h. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation tfib_K := YE2k.tfib_K.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The meter of one call: its own two allocations (f, c) of at most WIRE_RECV_MAX bytes and two frees, and one call of
   check_copy at its largest frame (WIRE_RECV_MAX bytes); the other checks charge nothing (the fake frames of
   check_meter and check_read, check_clamp_cg.v's form). The input length n does not enter. *)
Definition wire_ccpy_cost_max : Z := @PCPY.wire_check_copy_cost MT WIRE_RECV_MAX.
Definition wire_llvmf_cost (n : Z) : Z := 2 * (mo_malloc MT WIRE_RECV_MAX + mo_free MT) + wire_ccpy_cost_max.

(* The traces its four allocator calls record, which the call rules ask to be in the trace universe (YC5d.v). At the
   first malloc s0 still holds the caller's value, whose chain the slot gives as empty (afn_pre's achain at []), and
   from +0x8c on s0 = f, a heap address below alloc_ceiling, so the chain is empty at every call (YCbq.v achain) and
   the traces are fixed: [pc0; return address] (lib/B/YCej.v TRACES_LLVMFuzzerTestOneInput rows [0x52334; 0x7fc80],
   [0x52334; 0x7fd08], [0x521d4; 0x7fd50], [0x521d4; 0x7fd58]). *)
Definition wire_llvmf_ufix : Prop :=
  In (wire_utrace (pc_malloc_ra0 (as_code B)) [WIRE_LLVMF_RA_MALLOC1]) (as_universe B) /\
  In (wire_utrace (pc_malloc_ra0 (as_code B)) [WIRE_LLVMF_RA_MALLOC2]) (as_universe B) /\
  In (wire_utrace (pc_free_ra0 (as_code B)) [WIRE_LLVMF_RA_FREE1]) (as_universe B) /\
  In (wire_utrace (pc_free_ra0 (as_code B)) [WIRE_LLVMF_RA_FREE2]) (as_universe B).

Definition wire_llvmf_holds_stmt : Prop :=
  pc_wrap_malloc (as_code B) = wire_sigma WS___interceptor_trampoline_malloc ->
  pc_wrap_free (as_code B) = wire_sigma WS___interceptor_trampoline_free ->
  wire_cells B ->
  wire_ro_rd_unowned B -> wire_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  @asink_img_laws tfib_sink_head segs B tfib_K ->
  (* HSINK_KEPT / HMETA_KEPT: cgif's asink_none_kept / ameta_inv_kept (used at lib/A/ACfj.v) specialised to one
     journal step, the form of fuzz_decode's statement (with the premise ~ sink_open_fp FP); the B core's
     lib/B/YE01.v asink_none_kept / ameta_inv_kept give them. *)
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W0 mem0) md0 -> asink_none segs tfib_K (rd W' mem') md') ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W0 mem0) M -> ameta_inv segs tfib_K ly' (rd W' mem') M) ->
  @ro_below_ofl segs RLO RHI tfib_sink_head ->
  wire_llvmf_ufix ->
  (forall fx' : YK11.FPState, @amalloc04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (wire_sigma WS___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @PFWD.wire_check_forward_cg fx' rc B MT (wire_sigma WS_check_forward)) ->
  (forall fx' : YK11.FPState, @PRET.wire_check_ret_cg fx' rc B MT (wire_sigma WS_check_ret)) ->
  (forall fx' : YK11.FPState, @PDS.wire_check_downstream_cg fx' rc B MT (wire_sigma WS_check_downstream)) ->
  (forall fx' : YK11.FPState, @PMET.wire_check_meter_cg fx' rc B MT (wire_sigma WS_check_meter)) ->
  (forall fx' : YK11.FPState, @PCNT.wire_check_counter_cg fx' rc B MT (wire_sigma WS_check_counter)) ->
  (forall fx' : YK11.FPState, @PWID.wire_check_width_cg fx' rc B MT (wire_sigma WS_check_width)) ->
  (forall fx' : YK11.FPState, @PRD.wire_check_read_cg fx' rc B MT (wire_sigma WS_check_read)) ->
  (forall fx' : YK11.FPState, @PCPY.wire_check_copy_cg fx' rc B MT (wire_sigma WS_check_copy)) ->
  (forall n, 0 <= n -> wire_llvmf_cost n <= XL n) ->
  @tfib_lib_contract_x_all rc ZTS.checksum_shape B MT XL XL RLO RHI.
End h.
