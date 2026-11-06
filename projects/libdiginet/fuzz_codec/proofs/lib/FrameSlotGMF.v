(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the twin of lib/Reusable/YL0i.v (posts, contracts), lib/Reusable/YL05.v (lib_post_state) and lib/Reusable/YL06.v (call site) for a return value of the fuzz target of 0 or -1 *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_lock/lib/Prog/FrameRetD1.v, with its module paths changed; 76 of its 245 lines of code are new or changed and 365 lines of the source are left out. *)
(* Modified by Theorem Labs: the twin of lib/U/Reusable/YL0i_cfw.v (lib_contract_x_Rc), lib/U/Reusable/YL06_cfw.v (lib_site_x_R_cf) and lib/U/AgreeZlib.v (lib_contract_x_Rc_of_cg) (no licence line) for a return value of the fuzz target of 0 or -1 *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_lock/lib/U/Prog/AgreeRetD1.v, with its module paths changed; 92 of its 107 lines of code are new or changed and 230 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/FrameSlotG.v; 21 of its 53 lines of code are new or changed and 75 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libdiginet.fuzz_codec Require Images.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
  YK11 YM05 YO0d YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import
  ZTraceSpec ZComplete ZCompleteMF ZAllocator ZAllocatorMF SlotTopG Contract FrameAPI FrameSlotG.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.
Section BridgeM.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape} {AM : AllocMode}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Lemma lib_contract_x_G_of_gm : forall G R GI j pc ra empty stk,
  @lib_contract_gm AM fx rc LS B API SH SK G R GI j pc ra empty stk ->
  @lib_contract_x_G fx rc LS AM B API SH SK G R GI (fun _ => []) j pc ra empty stk.
Proof using TBL.
  intros G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre HGI HR Hfrm HK.
  apply (H L A regs mem md p n pl b K Hpre HGI HR (ro_agree_of_pre_x B API TBL stk empty L A regs mem md ra p n pl b Hpre)
    (lib_pre_x_sp B API stk empty L A regs mem md ra p n pl b Hpre) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_x_G_of_g B API G stk L A regs mem md p n b l L' A' regs' mem' md' Hp) | exact HGI'].
Qed.
End BridgeM.
Theorem plain_halts_mf_of_frame_slot : forall (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_gm MayFail fx rc checksum_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  halts_may_fail Exits.any Images.plain.
Proof.
  intros G GI HG GIL GI0 H.
  apply (plain_halts_mf_from_runtime_contracts_G checksum_shape G frame_RELRO GI (fun _ => []) checksum_permitted
    (fun data => checksum_room_calls _ _) (fun a h => frame_G_src0 a (HG a h))).
  - exact frame_RELRO_src0.
  - exact GIL.
  - exact GI0.
  - intros rc. exists (@zlib_API rc). split; [apply zlib_allocator_extra|].
    split; [exact (zlib_mf_allocator_holds rc)|].
    intros fx j Hj.
    exact (lib_contract_x_G_of_gm (AM:=MayFail) src0_msyms (@zlib_API rc) (zlib_tables rc)
      G frame_RELRO GI j _ _ _ _ (H rc fx j Hj)).
Qed.
