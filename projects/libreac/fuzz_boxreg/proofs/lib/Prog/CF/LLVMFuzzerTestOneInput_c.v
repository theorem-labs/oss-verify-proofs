(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v; 94 of its 156 lines of code are new or changed and 400 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocPackCf.v, with its module names changed; 154 of its 182 lines of code are new or changed and 128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Prog/CF/SRCF.v, with its module paths and module names changed; 50 of its 71 lines of code are new or changed and 161 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x12c6c.
Definition LLVM_FRAME : Z := 448.
Definition LLVM_K : Z := LLVM_FRAME + 8224.
Definition LLVM_MALLOC : Z := 0x14788.
Definition LLVM_FREE : Z := 0x14648.
Definition LLVM_GUARD_GOT : Z := 0x1d2e0.
Definition LLVM_GUARD : Z := 0x4e8d0.
Definition LLVM_REQ : Z := 288.

Definition LLVM_PEAK_BLOCKS : Z := 2.
Definition LLVM_PEAK_BYTES : Z := 336.
Definition LLVM_MAX_REQ : Z := 288.
Definition llvm_G : list (Z * Z) := [].
Definition llvm_RELRO : list (Z * Z) := [(0x1d240, 160); (0x1d2e8, 16)].
Definition llvm_GI : nat -> (word -> option byte) -> Prop := fun _ _ => True.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition llvm_binds : Prop :=
  ms_segs B = rsegs /\ ms_malloc B = LLVM_MALLOC /\ ms_free B = LLVM_FREE /\
  ms_got_guard B = LLVM_GUARD_GOT /\ ms_guard B = LLVM_GUARD /\ AllocExtra B MR.

Definition llvm_room (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX.

Definition llvm_ls_laws : Prop :=
  (forall pl fs (K : lleaf -> TSet), t_eq (LIBK pl fs K) (K (LL 0 fs []))) /\
  (forall b n, lib_room b n -> llvm_room b) /\
  (forall n b, lib_delta n b = b).

Definition LLVMFuzzerTestOneInput_contract : Prop :=
  llvm_binds -> llvm_ls_laws ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
    lib_contract_cg B API llvm_G llvm_RELRO llvm_GI j LLVM_ENTRY ra empty stk.

Definition LLVMFuzzerTestOneInput_sr_contract : Prop :=
  llvm_binds ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  forall L A regs mem md p n b,
    lib_pre B API stk empty L A regs mem md ra p n ->
    sink_none B mem md -> spZ regs <= 2 ^ 47 ->
    res_ok_slots A b ->
    llvm_room b ->
    ro_agree rsegs mem -> G_img_c B llvm_RELRO mem ->
    llvm_GI j mem ->
    frm_zero fp_csr ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         lib_post B API llvm_G stk L A regs mem md p L' A' regs' mem' md' /\
         sink_none B mem' md' /\
         res_ok_slots A' b /\
         (forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
         ro_agree rsegs mem' /\
         llvm_GI (S j) mem').

End K.
