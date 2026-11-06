(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths, addresses and numbers changed; 43 of its 79 lines of code are new or changed and 30 lines of the source are left out. *)
(* The slot contract of LLVMFuzzerTestOneInput (fuzz/fuzz_transport.c:1124-1218) in the plain image, the form the
   frame consumes (FrameAPI.v frame_plain: lib_contract_g with G = frame_G, R = frame_RELRO, GI), and the contract
   its walk proves (the SR form with the world and the model premise). *)
(* LLVMFuzzerTestOneInput at 0x13664, 3720 bytes (EQUAL-mod-pcrel to the pin's at 0x1365c: its op switch's jump
   table stays at 0x10408 while the code moves 8 bytes, so the table's entries change). addi sp,sp,-224 at 0x13664
   (ra, s0-s11 saved). op_frame, op_announce, op_submit, fuzz.h's cursor and m_close are inlined. Callees:
   diginet_session_config_default, memcpy, memset, strlen (kit), diginet_session_init, m_wake,
   diginet_session_wake, check_state_wake_code, diginet_session_close, m_tick, diginet_session_tick, settle,
   build_and_receive (ops 1, 2), diginet_session_submit, check_refusal_submit, check_latest_submit, receive (ops 0,
   8); abort (0x144e8) when diginet_session_init fails.
   LLVM_FRAME 224, LLVM_K = 224 + build_and_receive_FRAME 9856 = 10080: the deepest callee is build_and_receive
   (receive 8240, every session function at most 3840). LLVM_K <= SLOT_STACK (65536, FrameAPI.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem GI receive_c
  build_and_receive_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x13664.
Definition LLVM_FRAME : Z := 224.
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
   every such stream. TSim's harness_model_ok gives it (SlotBridge.v). *)
Definition llvm_model_ok (Bw D : list byte) : Prop :=
  forall A, llvm_heap_ok A -> exists Bw', LLVMFuzzerTestOneInput_m timg_plain Bw A D = Some (Bw', 0).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition llvm_binds : Prop := h_binds B API.

Definition llvm_room (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX.

Definition llvm_ls_laws : Prop :=
  (forall pl fs (K : lleaf -> TSet), t_eq (LIBK pl fs K) (K (LL 0 fs []))) /\
  (forall b n, lib_room b n -> llvm_room b) /\
  (forall n b, lib_delta n b = b).

(* The slot (the kit's lib_contract_g, Contract.v:320): entered at LLVM_ENTRY with a0 = data, a1 = size and the
   payload in a user block (lib_pre_x), GI, the RELRO tables as in the image, read-only memory intact, and a stack of
   stk >= LLVM_K bytes; it returns to ra with lib_post_g: the allocator invariant, a0 = 0, the callee-saved
   registers, every user block and its bytes but the payload's kept, memory outside frame_G (the world), the
   scratch and the allocator unchanged, no output, the budget, the payload bytes, and GI for the next call. With
   stk = SLOT_STACK and j < 4 it is the premise of FrameAPI.v frame_plain. *)
Definition LLVMFuzzerTestOneInput_contract : Prop :=
  llvm_binds -> llvm_ls_laws ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
    lib_contract_g B API llvm_G llvm_RELRO llvm_GI j LLVM_ENTRY ra empty stk.

(* The return state the walk contract gives: the donor's SR post (fuzz_decode Prog/LLVMFuzzerTestOneInput_c.v
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

(* The walk's contract. Its proof walks the binary, cutting in receive_contract and build_and_receive_contract for
   each receive (their posts name the heap frame each malloc returned, which builds the stream A) and the evt
   contracts of the other callees. *)
Definition LLVMFuzzerTestOneInput_walk_contract : Prop :=
  llvm_binds ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  forall L A regs mem md p n pl b (Bw : list byte),
    llvm_walk_pre j ra empty stk L A regs mem md p n pl b Bw ->
    llvm_room b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom segs)) md)
      (llvm_walk_post j ra stk L A regs mem md p n b).

End K.
