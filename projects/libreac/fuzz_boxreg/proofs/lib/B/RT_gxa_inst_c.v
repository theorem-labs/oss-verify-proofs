(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new for libreac/fuzz_boxreg (asan-ubsan): RT_gxa_inst.v's instance definitions with
   the three GXA call contracts plugged in, each the relocated proof at this image (RT_gxa_calls_mem.v
   memcpy_stack_contract_A / memset_stack_contract_A, RT_gxa_calls.v strnlen_stack_contract_A). *)
(* proves no function (kind: segment lemma -- instantiation). What stays open is only what the caller supplies:
   INV (the caller's memory invariant), and for musl vsnprintf (fm_vsnprintf_x_proof, at A_img_vsn) its memset
   contract at A_img_vsn and VF (vfprintf_guarded_stmt). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import RT_IImgA RT_gxa_inst.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require RT_gxa_calls RT_gxa_calls_mem.
Module RGC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.RT_gxa_calls.
Module RGM := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.RT_gxa_calls_mem.
Open Scope Z_scope.

Definition box_vfprintf_snf_a_closed (INV : (word -> option byte) -> Prop) :=
  fm_vfprintf_snf_a_closed RGM.copy_ready RGM.set_ready RGC.strn_ready INV
    RGM.memcpy_stack_contract_A RGM.memset_stack_contract_A RGC.strnlen_stack_contract_A.

Definition box_vfprintf_snf_a_guarded_closed (INV : (word -> option byte) -> Prop) :=
  fm_vfprintf_snf_a_guarded_closed RGM.copy_ready RGM.set_ready RGC.strn_ready INV
    RGM.memcpy_stack_contract_A RGM.memset_stack_contract_A RGC.strnlen_stack_contract_A.

Definition box_printf_core_a_all :=
  fm_printf_core_a_all RGM.copy_ready RGM.set_ready RGC.strn_ready
    RGM.memset_stack_contract_A RGC.strnlen_stack_contract_A.

Definition box_sn_write_ok :=
  fm_sn_write_ok RGM.copy_ready RGM.memcpy_stack_contract_A.
