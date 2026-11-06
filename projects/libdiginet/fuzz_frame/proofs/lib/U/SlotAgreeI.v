(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v at bc49657c087a; module path, this image's values, LLVM_K from check_inject. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths and module names changed; 79 of its 98 lines of code are new or changed and 48 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/SlotAgree.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/SlotAgree.v, with its module paths changed; 9 of its 34 lines of code are new or changed and 73 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/SlotAgreeI.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_frame; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract AllocSlots SlotAgree.
Import ListNotations.
Local Open Scope Z_scope.

(* The cut-free free contract free_contract_cf of SlotAgree with no resource bound: the pre asks only II A (the
   allocator's internal invariant, the first conjunct of every resource form: res_ok_slots, res_ok_pack), and the
   post gives II A'. The driver walk twins Reusable/*_cfwi.v use it for every resource form of the walk slot. *)

Section AgreeI.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition free_contract_cfi : Prop :=
  forall L A regs mem md p n,
    call_pre B MR L A regs mem md -> ro_agree segs mem ->
    In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
    II A ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post B MR L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' /\
         (exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         II A').

End AgreeI.
