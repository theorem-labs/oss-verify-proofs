(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0j_cfw.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/AgreeWalk.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/AgreeWalk.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06 YO04.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.libdiginet.fuzz_decode.images Require Import Plain.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0k YL0p YL0q YL0n YL0g YL0m YL0s YL0y YL0w YL0x.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t YL0z.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YM05 YM0b YL0j DriverSlots.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YO0d_cf YO04_cfw YK15_cfw YL0i_cfw.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YN3e_cfw YL0p_cfw YL0q_cfw YL0w_cfw YL0x_cfw YL0y_cfw.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YL0n_cfw YL0l_cfw YL0z_cfw.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YL0j_cfw.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Contract SlotAgree.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Section Walk.
Context {rc : YM05.RunCeil} {LS : lib_shape}.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Variable RI : list byte -> nat -> list (Z * Z) -> astate -> Prop.
Variable OUT : list byte -> list byte.
Hypothesis GIL : G_local_T src0segs src0_G GI.
Hypothesis GI0 : forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem.
Hypothesis LIBXc : lib_contract_x_Rc_all src0_msyms API RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis DOB : driver_obligationsX.
Hypothesis DRV : forall data, leaves (run_RI RI (payload data)) (driver_tree data).
Hypothesis FCF : forall fx' : FPState, @free_contract_cf fx' rc src0_msyms API.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr src0segs (Z_to_bv 64 a) = true -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a).
Hypothesis RIres : forall pl j T A, RI pl j T A -> exists b, res_ok_slots A b.
Hypothesis MRC : forall fx' : FPState, @malloc_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis FRC : forall fx' : FPState, @free_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).

Theorem plain_walk_crealizes : forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_input inp -> SRC_LIM_MIN <= lim ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  crealizes src0_msyms (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) (SPECX inp).
Proof using AX GIL GI0 LIBXc DOB DRV FCF TBL RIres MRC FRC LIMLAW.
  exact (src0_realizes_specX_cf API AX GI RI OUT GIL GI0 LIBXc DOB DRV FCF TBL RIres MRC FRC LIMLAW).
Qed.
End Walk.
