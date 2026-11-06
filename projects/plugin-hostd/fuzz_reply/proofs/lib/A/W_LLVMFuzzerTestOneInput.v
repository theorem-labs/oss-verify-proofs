(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput (fuzz_reply.asan 0x840b0,
   920 instructions): the program contract TFIB_T consumes, in the donor's form (A/ACfn.v:59 tfib_lib_contract_x,
   cf variant, at checksum_shape). *)
(* The cut points, the cut invariants, the walked dispatch (lf_seg_jt) and the composition (the operation loop's
   induction over OPS_MAX and the jump table's ten-arm case split, lf_contract_of_segments) are in
   W_LLVMFuzzerTestOneInput_cut.v.  The segments are walked in W_LLVMFuzzerTestOneInput_<segment>.v; until each lands
   it is a premise of pb_LLVMFuzzerTestOneInput (SEG_PRO, SEG_HEAD, ARM_add / write / drain / close / remove / gone /
   eintr / event / sendmax / default, SEG_LATCH, SEG_EXIT), stated over the cut invariants INV_H / INV_D / INV_A /
   INV_K / INV_X of the _cut file. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
Definition pb_LLVMFuzzerTestOneInput := @lf_contract_of_segments.
