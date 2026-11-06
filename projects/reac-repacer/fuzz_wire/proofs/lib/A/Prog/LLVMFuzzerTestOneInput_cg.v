(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: Section h of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_cg.v (origin/ossv/recipes 88154566652a; cgif_file_fuzzer lib/A/ACfn.v / lib/A/ACfj.v) for reac-repacer/fuzz_uci's image A: the slot is the relocated core's lib/A/ACfn.v tfib_lib_contract_x_all (so decode's own slot, Section a, is not copied) at the core's lib_shape checksum_shape, the core's sink names in place of Section Variables, and fuzz_uci's three callees; module paths changed. *)
(* LLVMFuzzerTestOneInput_cg: the statement of the walk of fuzz_wire.asan's LLVMFuzzerTestOneInput (wire_text of
   lib/A/Prog/WirePAddr.v, AF_LLVMFuzzerTestOneInput = 0 of lib/A/Prog/WirePList.v; ACfn.A_LLVMF = 0x7fe58), as a
   STATEMENT only (no proof): its own allocator and memcpy calls and the contracts of its eight callees give the core's
   slot (lib/A/ACfn.v tfib_lib_contract_x_all), at the core's shape checksum_shape. The form is fuzz_uci's
   lib/A/Prog/LLVMFuzzerTestOneInput_cg.v Section h, with the entry's own malloc / free / memcpy premises in the form
   of libreac/fuzz_decode's released lib/A/Prog/LLVMFuzzerTestOneInput_cg.v (dec_llvmf_holds_stmt).

   The code (objdump of record, image A): `addi sp, sp, -0x40` (frame 0x40), saves ra, s0..s6; returns 0 at once
   (+0x154) when n = 0 or n >= 2^26 (`bltu` at +0x30); reads data[0] (shadow check through the GOT word 0x987e8,
   __asan_report_load1 at +0x194); len = min(n - 1, 1600) (s1), sz = len + (len = 0) (s3); s0 = malloc(sz) at +0x78;
   __asan_memcpy(s0, data + 1, len) at
   +0xa0 when n > 1; then check_forward(s0, len, data[0] & 1) +0xb0, check_ret(s0, len) +0xbc,
   check_downstream(s0, len) +0xc8, check_meter(s0, len) +0xd4, check_counter(s0, len) +0xe0, check_width(len)
   +0xe8, check_read(s0, len, (data[0] >> 1) - 2) +0xf8; s3 = malloc(sz) at +0x100; __asan_memcpy(s3, s0, len) at
   +0x11c when n > 1; r = check_copy(s3, s0, len) at +0x12c; check_read(s3, r, (data[0] >> 1) - 2) at +0x140 when
   r <> 0; free(s3) +0x148, free(s0) +0x150; returns 0. A NULL return of either malloc (`beqz` at +0x7c / +0x104)
   goes to __asan_handle_no_return / abort at +0x180 / +0x184. s0 is never a frame pointer: at the first malloc it
   holds the caller's s0 (an empty chain by the slot's entry premise), afterwards a heap block, which lies below
   alloc_ceiling <= ly_stk_lo <= sp (YG0n.v:365, YCbq.v:336), so bad_next holds in chain_pre (YG0d.v:220-224) and the
   chain is empty; so every trace the entry's allocator calls record is [pc0; return address]
   (lib/A/ACej.v TRACES_LLVMFuzzerTestOneInput). *)
From Stdlib Require Import ZArith NArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require ZTraceSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaBase WirePSyms WirePAddr WirePList WirePImg WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require check_forward_cg check_ret_cg check_downstream_cg
  check_meter_cg check_counter_cg check_width_cg check_read_cg check_copy_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI16.
Module ZTS := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.ZTraceSpec.
Module PCF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_forward_cg.
Module PCR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_ret_cg.
Module PCD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_downstream_cg.
Module PCM := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_meter_cg.
Module PCN := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_counter_cg.
Module PCW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_width_cg.
Module PCRD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_read_cg.
Module PCC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_copy_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The entry, as the listing names it; it is the core's ACfn.A_LLVMF. *)
Lemma wire_a_llvmf_eq : WIRE_A_LLVMF = A_LLVMF.
Proof. reflexivity. Qed.

(* The return addresses of this function's allocator calls, as offsets from its entry (the jal is 4 bytes before):
   malloc at +0x78 and +0x100, free at +0x148 and +0x150 (0x7fed4, 0x7ff5c, 0x7ffa4, 0x7ffac). *)
Definition WIRE_LLVMF_RA_MALLOC : list Z := map (fun o => WIRE_A_LLVMF + o) [0x7c; 0x104].
Definition WIRE_LLVMF_RA_FREE : list Z := map (fun o => WIRE_A_LLVMF + o) [0x14c; 0x154].

(* The size of each of the two blocks at input length n (1 <= n < 2^26): len = min(n - 1, 1600), and 1 when len = 0
   (`seqz` / `add` at +0x6c / +0x70). *)
Definition wire_llvmf_len (n : Z) : Z := Z.min (n - 1) 1600.
Definition wire_llvmf_sz (n : Z) : Z := wire_llvmf_len n + (if wire_llvmf_len n =? 0 then 1 else 0).

Section h. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation tfib_K := AE2k.tfib_K.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The traces of this function's own malloc and free calls, which the call rules ask to be in the trace universe
   (YC5d.v amalloc04_rule / afree04_rule). *)
Definition wire_llvmf_ufix : Prop :=
  (forall r, In r WIRE_LLVMF_RA_MALLOC -> In (wire_utrace (pc_malloc_ra0 (as_code B)) [r]) (as_universe B)) /\
  (forall r, In r WIRE_LLVMF_RA_FREE -> In (wire_utrace (pc_free_ra0 (as_code B)) [r]) (as_universe B)).

(* The meter of one call at input length n: nothing when n = 0 or n >= 2^26 (the early return); else the two blocks
   of wire_llvmf_sz n bytes, their two frees, and check_copy's own cost at its length len. No other callee charges
   the meter: the fake frames of check_meter and check_read change only the state's st_fs. *)
Definition wire_llvmf_cost (n : Z) : Z :=
  if (n =? 0) || (2 ^ 26 <=? n) then 0
  else mo_malloc MT (wire_llvmf_sz n) + mo_malloc MT (wire_llvmf_sz n) + (mo_free MT + mo_free MT) +
       @PCC.wire_check_copy_cost MT (wire_llvmf_len n).

(* The statement the walk will prove: the call rules' code addresses (the listing's trampolines), the runtime cells
   and read-only facts of the record, the allocator, meter and sink laws, the entry's own traces, its own malloc /
   free / memcpy contracts and the contracts of its eight callees give the slot, with XL as both meter bounds. *)
Definition wire_llvmf_holds_stmt : Prop :=
  pc_wrap_malloc (as_code B) = wire_sigma WS___interceptor_trampoline_malloc ->
  pc_wrap_free (as_code B) = wire_sigma WS___interceptor_trampoline_free ->
  wire_cells B ->
  wire_ro_rd_unowned B -> wire_rom_no_errno B ->
  wire_llvmf_ufix ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  @asink_img_laws tfib_sink_head segs B tfib_K ->
  (* HSINK_KEPT / HMETA_KEPT: asink_none_kept / ameta_inv_kept of lib/Reusable/YE01.v specialised to one journal
     step (the premise ~ sink_open_fp FP as fuzz_decode's statement states it). *)
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W0 mem0) md0 -> asink_none segs tfib_K (rd W' mem') md') ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W0 mem0) M -> ameta_inv segs tfib_K ly' (rd W' mem') M) ->
  @ro_below_ofl segs RLO RHI tfib_sink_head ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @afree04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (wire_sigma WS___asan_memcpy)) ->
  (forall fx : YK11.FPState, @PCF.wire_check_forward_cg fx rc B MT (wire_sigma WS_check_forward)) ->
  (forall fx : YK11.FPState, @PCR.wire_check_ret_cg fx rc B MT (wire_sigma WS_check_ret)) ->
  (forall fx : YK11.FPState, @PCD.wire_check_downstream_cg fx rc B MT (wire_sigma WS_check_downstream)) ->
  (forall fx : YK11.FPState, @PCM.wire_check_meter_cg fx rc B MT (wire_sigma WS_check_meter)) ->
  (forall fx : YK11.FPState, @PCN.wire_check_counter_cg fx rc B MT (wire_sigma WS_check_counter)) ->
  (forall fx : YK11.FPState, @PCW.wire_check_width_cg fx rc B MT (wire_sigma WS_check_width)) ->
  (forall fx : YK11.FPState, @PCRD.wire_check_read_cg fx rc B MT (wire_sigma WS_check_read)) ->
  (forall fx : YK11.FPState, @PCC.wire_check_copy_cg fx rc B MT (wire_sigma WS_check_copy)) ->
  (forall n, 0 <= n -> wire_llvmf_cost n <= XL n) ->
  @tfib_lib_contract_x_all rc ZTS.checksum_shape B MT XL XL RLO RHI.
End h.
