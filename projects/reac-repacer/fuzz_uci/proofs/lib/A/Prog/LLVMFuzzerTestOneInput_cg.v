(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: Section h of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_cg.v (origin/ossv/recipes 88154566652a; cgif_file_fuzzer lib/A/ACfn.v / lib/A/ACfj.v) for reac-repacer/fuzz_uci's image A: the slot is the relocated core's lib/A/ACfn.v tfib_lib_contract_x_all (so decode's own slot, Section a, is not copied) at the core's lib_shape checksum_shape, the core's sink names in place of Section Variables, and fuzz_uci's three callees; module paths changed. *)
(* LLVMFuzzerTestOneInput_cg: the statement of the walk of fuzz_uci.asan's LLVMFuzzerTestOneInput (uci_text of
   lib/A/Prog/UciPAddr.v, AF_LLVMFuzzerTestOneInput = 0 of lib/A/Prog/UciPList.v; ACfn.A_LLVMF = 0x7f2e8), as a STATEMENT
   only (no proof): the callee contracts give the core's slot.

   The code (DIS of image A): `addi sp, sp, -0x90` (frame 0x90); +0x34 `mv s0, a1` (s0 = n, the input length, from
   here to the epilogue: no frame pointer); returns 0 at once when n >> 26 <> 0; reads the shadow base through its GOT
   word (+0x44 auipc, +0x48 ld: 0x97020); bit = data[0] & 1 (0 when n = 0), and margin_max = MARGIN_MAX[bit], a `lw` at
   +0x98 from 0x20ca0 + 4 bit (+0x78 auipc / +0x7c addi: 0x20ca0), guarded by __asan_report_load4 (+0x1fc); then five
   times: the 4-byte cur (fuzz_le32 inlined, `lbu` of the input with __asan_report_load1 checks), the length byte, the
   slice r = data + off of length min(rest, length byte) <= 255, check_no_overread (r, len, cur) at +0x144 (return
   address +0x148 = 0x7f430), check_value (r, len, cur) at +0x154 (0x7f440), the value stored into an int[5] on the
   frame; then the five ints copied to the struct at sp + 8 and check_clamp (sp + 8, margin_max) at +0x1b0 (0x7f49c);
   returns 0. It calls no allocator, memcpy or fake stack itself. *)
From Stdlib Require Import ZArith NArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require ZTraceSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaBase UciPSyms UciPAddr UciPList UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require rp_uci_int_cg check_no_overread_cg check_value_cg check_clamp_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI16.
Module ZTS := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.ZTraceSpec.
Module PR := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.rp_uci_int_cg.
Module PN := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.check_no_overread_cg.
Module PV := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.check_value_cg.
Module PK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.check_clamp_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The entry, as the listing names it; it is the core's ACfn.A_LLVMF. *)
Definition UCI_A_LLVMF : Z := uci_text + AF_LLVMFuzzerTestOneInput.
Lemma uci_a_llvmf_eq : UCI_A_LLVMF = A_LLVMF.
Proof. reflexivity. Qed.

(* The return addresses of this function's three calls, as offsets from its entry (the jal is 4 bytes before):
   check_no_overread at +0x144, check_value at +0x154, check_clamp at +0x1b0 (0x7f430, 0x7f440, 0x7f49c). *)
Definition UCI_LLVMF_RA_CNO : list Z := map (fun o => UCI_A_LLVMF + o) [0x148].
Definition UCI_LLVMF_RA_CV : list Z := map (fun o => UCI_A_LLVMF + o) [0x158].
Definition UCI_LLVMF_RA_CC : list Z := map (fun o => UCI_A_LLVMF + o) [0x1b4].

(* The call contexts of check_no_overread (fuzz_decode's `raZ :: spine ch` convention,
   check_round_trip_cg.v / LLVMFuzzerTestOneInput_cg.v CTX_check_round_trip). At the call (+0x144) s0 holds n
   (`mv s0, a1` at +0x34), and 0 <= n < 2 ^ 26 lies below alloc_ceiling, so the frame-pointer chain is empty (YCbq.v
   achain_low) and the context is the return address alone: [[0x7f430]]. (lib/A/ACej.v's generator writes
   CTX_check_no_overread = [[]], its own convention for the chain after the return address; it is not this
   statement's CTX.) *)
Definition CTX_check_no_overread : list (list Z) := map (fun r => [r]) UCI_LLVMF_RA_CNO.

(* The statement the walk (cgif's lib/A/ACfj.v composition, at fuzz_uci's callees) will prove: the callee contracts
   give the slot, at the core's shape checksum_shape and with XL as both meter bounds (ACfj.v). *)
Section h. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation tfib_K := AE2k.tfib_K.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The meter of one call: five calls of check_no_overread and of check_value, each at its largest slice
   (REPLY_MAX bytes), and check_clamp, which allocates nothing. The input length n does not enter. *)
Definition uci_cno_cost_max : Z := @PN.uci_cno_cost MT PR.REPLY_MAX.
Definition uci_cv_cost_max : Z := @PV.uci_cv_cost MT PR.REPLY_MAX.
Definition uci_llvmf_cost (n : Z) : Z := 5 * (uci_cno_cost_max + uci_cv_cost_max).

Definition uci_llvmf_holds_stmt : Prop :=
  uci_cells B ->
  uci_ro_rd_unowned B -> uci_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  @asink_img_laws tfib_sink_head segs B tfib_K ->
  (* HSINK_KEPT / HMETA_KEPT: cgif's asink_none_kept / ameta_inv_kept (used at lib/A/ACfj.v) specialised to one
     journal step, the form of fuzz_decode's statement (with the premise ~ sink_open_fp FP); the core's
     lib/Reusable/YE01.v asink_none_kept / ameta_inv_kept give them. *)
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W0 mem0) md0 -> asink_none segs tfib_K (rd W' mem') md') ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W0 mem0) M -> ameta_inv segs tfib_K ly' (rd W' mem') M) ->
  @ro_below_ofl segs RLO RHI tfib_sink_head ->
  (forall fx : YK11.FPState,
     @PN.uci_check_no_overread_cg fx rc B MT (uci_sigma US_check_no_overread) CTX_check_no_overread) ->
  (forall fx : YK11.FPState, @PV.uci_check_value_cg fx rc B MT (uci_sigma US_check_value)) ->
  (forall fx : YK11.FPState, @PK.uci_check_clamp_cg fx rc B MT (uci_sigma US_check_clamp)) ->
  (forall n, 0 <= n -> uci_llvmf_cost n <= XL n) ->
  @tfib_lib_contract_x_all rc ZTS.checksum_shape B MT XL XL RLO RHI.
End h.
