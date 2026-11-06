(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths, addresses and numbers changed; 65 of its 99 lines of code are new or changed and 32 lines of the source are left out. *)
(* The slot contracts of LLVMFuzzerTestOneInput (fuzz/fuzz_transport.c:1124-1218) in the ubsan image, the forms the
   frame consumes (U/FrameAPI.v frame_ubsan: lib_contract_g, for ubsan_halts; AgreeFrame.v: lib_contract_cg, the
   cut-free form, for ubsan_agrees; both with G = frame_G, R = frame_RELRO, GI), and the contracts its walk proves
   (the SR and SRcf forms with the world and the model premise). *)
(* LLVMFuzzerTestOneInput at 0x13760, 4300 bytes (EQUAL-mod-pcrel to the pin's at the same address: its op switch's
   jump table stays at 0x10418, the code after it moves). addi sp,sp,-240 at 0x13760 (ra, s0-s11 saved).
   op_frame, op_announce, op_submit, fuzz.h's cursor and m_close are inlined. Callees: memcpy, memset, strlen (kit),
   diginet_session_config_default, diginet_session_init, m_wake, diginet_session_wake, check_state_wake_code,
   diginet_session_close, m_set (0x13c2c, m_close's), m_tick, diginet_session_tick, settle, build_and_receive (ops 1, 2),
   diginet_session_submit, check_refusal_submit, check_latest_submit, receive (ops 0, 8); abort (0x14824) when
   diginet_session_init fails; the UBSan traps (unimp) of its own checks.
   LLVM_FRAME 240, LLVM_K = 240 + build_and_receive_FRAME 9936 = 10176: the deepest callee is build_and_receive
   (receive 8320, every session function at most 3824). LLVM_K <= SLOT_STACK (65536, U/FrameAPI.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Contract Img0 FrameAPI SlotAgree.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem GI receive_c
  build_and_receive_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x13760.
Definition LLVM_FRAME : Z := 240.
Definition LLVM_K : Z := LLVM_FRAME + build_and_receive_FRAME.

Definition llvm_G : list (Z * Z) := frame_G.
Definition llvm_RELRO : list (Z * Z) := frame_RELRO.
Definition llvm_GI : nat -> (word -> option byte) -> Prop := GI.

(* The slot is the function the frame names, and its stack fits the frame's. *)
Example LLVM_ENTRY_frame : LLVM_ENTRY = FrameAPI.ENTRY.
Proof. reflexivity. Qed.
Example LLVM_K_fits : LLVM_K <= SLOT_STACK.
Proof. vm_compute. discriminate. Qed.

(* The address stream of the model (TOps.v LLVMFuzzerTestOneInput_m's A: A k is the heap frame of the k-th
   receive): every index the loop can read (at most one receive per op, OPS_MAX ops) holds an address a successful
   malloc can return. The same text as TSim/LoopOk.v heap_ok. *)
Definition llvm_heap_ok (A : nat -> Z) : Prop :=
  forall k : nat, Z.of_nat k < OPS_MAX -> 0 < A k /\ A k + 65536 <= 2 ^ 64.

(* The model premise of the walk: from the world Bw and the input D, the harness model returns Some (_, 0) for
   every such stream. TSim's harness_model_ok gives it (U/Prog/T/SlotBridge.v). *)
Definition llvm_model_ok (Bw D : list byte) : Prop :=
  forall A, llvm_heap_ok A -> exists Bw', LLVMFuzzerTestOneInput_m timg_ubsan Bw A D = Some (Bw', 0).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition llvm_binds : Prop := h_binds B API.

(* The budgets: the halting form's (U/FrameAPI.v: lib_room gives sb_cap = CAPMAX) and the cut-free form's (the
   donor's llvm_room_cf, fuzz_decode U/Prog/LLVMFuzzerTestOneInput_cfb.v: sb_cap <= CAP_AG, U/SlotAgree.v). *)
Definition llvm_room (b : sbound) : Prop := sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX.
Definition llvm_room_cf (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG.

Definition llvm_ls_laws : Prop :=
  (forall pl fs (K : lleaf -> TSet), t_eq (LIBK pl fs K) (K (LL 0 fs []))) /\
  (forall b n, lib_room b n -> llvm_room b) /\
  (forall n b, lib_delta n b = b).
Definition llvm_ls_laws_cf : Prop :=
  (forall pl fs (K : lleaf -> TSet), t_eq (LIBK pl fs K) (K (LL 0 fs []))) /\
  (forall b n, lib_room b n -> llvm_room_cf b) /\
  (forall n b, lib_delta n b = b).

(* The machine's allocator never runs out of address space in the cut-free form (the donor's llvm_limlaw): what
   room_cf, the budget of malloc_contract_cf, asks of the model's vm_limit. *)
Definition llvm_limlaw : Prop := forall L A mem md, MR L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).

(* The slot, halting form (the kit's lib_contract_g, U/Contract.v:320); with stk = SLOT_STACK and j < 4 it is the
   premise of U/FrameAPI.v frame_ubsan. *)
Definition LLVMFuzzerTestOneInput_contract : Prop :=
  llvm_binds -> llvm_ls_laws ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
    lib_contract_g B API llvm_G llvm_RELRO llvm_GI j LLVM_ENTRY ra empty stk.

(* The slot, cut-free form (U/SlotAgree.v lib_contract_cg), the premise of AgreeFrame.v for ubsan_agrees. *)
Definition LLVMFuzzerTestOneInput_contract_cg : Prop :=
  llvm_binds -> llvm_ls_laws_cf ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
    lib_contract_cg B API llvm_G llvm_RELRO llvm_GI j LLVM_ENTRY ra empty stk.

(* The return state both walk contracts give: the donor's SR post (fuzz_decode U/Prog/LLVMFuzzerTestOneInput_c.v
   LLVMFuzzerTestOneInput_sr_contract). *)
Definition llvm_walk_post (j : nat) (ra stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p n : Z) (b : sbound) (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post B API llvm_G stk L A regs mem md p L' A' regs' mem' md' /\
    sink_none B mem' md' /\
    res_ok_slots A' b /\
    (forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
    ro_agree rsegs mem' /\
    llvm_GI (S j) mem'.

(* The walk's premises besides the budget: the donor's SR premises, plus the world Bw in memory and the model
   premise llvm_model_ok Bw pl. *)
Definition llvm_walk_pre (j : nat) (ra empty stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p n : Z) (pl : list byte) (b : sbound) (Bw : list byte) : Prop :=
  lib_pre B API stk empty L A regs mem md ra p n /\
  n = Z.of_nat (length pl) /\ blk_data B mem p pl /\
  sink_none B mem md /\ spZ regs <= 2 ^ 47 /\
  res_ok_slots A b /\
  ro_agree rsegs mem /\ G_img_c B llvm_RELRO mem /\
  llvm_GI j mem /\
  frm_zero fp_csr /\
  wmem rsegs mem Bw /\
  llvm_model_ok Bw pl.

(* The walk's contract, halting form. Its proof walks the binary, cutting in receive_contract and
   build_and_receive_contract for each receive (their posts name the heap frame each malloc returned, which builds
   the stream A) and the evt contracts of the other callees. *)
Definition LLVMFuzzerTestOneInput_walk_contract : Prop :=
  llvm_binds ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  forall L A regs mem md p n pl b (Bw : list byte),
    llvm_walk_pre j ra empty stk L A regs mem md p n pl b Bw ->
    llvm_room b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom segs)) md)
      (llvm_walk_post j ra stk L A regs mem md p n b).

(* The walk's contract, cut-free form (with receive_contract_cf, build_and_receive_contract_cf, and the
   allocator's contracts in SRcf form). *)
Definition LLVMFuzzerTestOneInput_walk_contract_cf : Prop :=
  llvm_binds -> llvm_limlaw ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  forall L A regs mem md p n pl b (Bw : list byte),
    llvm_walk_pre j ra empty stk L A regs mem md p n pl b Bw ->
    llvm_room_cf b ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom segs)) md)
      (llvm_walk_post j ra stk L A regs mem md p n b).

End K.
