(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the plain realization lemma of fuzz_knock's lib/A/KnockAsanTop.v
   (knock_plain_rz) for fuzz_codec, over the plain main contract, with the plain slot lib/Prog/CodecSlot.codec_slot
   at the agreement shape of lib/AgreeCodec.v; module paths changed. *)
(* The plain side of fuzz_codec's ASan agreement statements: from every valid plain start, the plain build realizes
   SPECX at the agreement shape (AgreeCodec.ag_sil_shape: silent output, the agreement room). As lib/AgreeFrame.v
   builds it for the ubsan agreement: lib/AgreeTop.v plain_rz_of_contracts_R with G = [], GI = True, frame_RELRO and
   the plain slot contract (Prog/CodecSlot.codec_slot), which takes the plain main contract
   (Prog/LLVMFuzzerTestOneInput_c.codec_main_contract) and derives main's RELRO premises itself. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libdiginet.fuzz_codec Require Statements Images.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib AgreeShape.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require AgreeCodec.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require CodecSlot LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Lemma codec_plain_rz :
  OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.LLVMFuzzerTestOneInput_c.codec_main_contract ->
  forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=AgreeCodec.ag_sil_shape) inp).
Proof.
  intros HMAIN.
  assert (Hp : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc AgreeCodec.ag_sil_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      [] frame_RELRO (fun _ _ => True) j ENTRY RA_LIB EMPTY SLOT_STACK).
  { intros rc fx j _. rewrite lib_contract_g_gm.
    eapply (@OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.CodecSlot.codec_slot
      OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable.R.Cfg.AcfgMode fx rc AgreeCodec.ag_sil_shape);
      first [exact HMAIN | reflexivity | (intros; reflexivity) | (vm_compute; reflexivity)]. }
  assert (HROOMp : forall data, @room_calls AgreeCodec.ag_sil_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; exact (ag_room_calls checksum_shape _ _)).
  assert (HG : forall a, in_globals [] a -> in_globals frame_G a) by (intros a (lo & len & [] & _)).
  assert (GIL : G_local_c src0_msyms [] (fun _ _ => True)) by (intros j m m' _ _; exact I).
  assert (GI0 : forall mem, G_img_c src0_msyms [] mem -> (fun _ _ => True) 0%nat mem) by (intros mem _; exact I).
  assert (HC : zlib_runtime_contracts_R AgreeCodec.ag_sil_shape (@RI_G AgreeCodec.ag_sil_shape) [] frame_RELRO
    (fun j T m => T = [] /\ (fun _ _ => True) j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G AgreeCodec.ag_sil_shape) [] frame_RELRO _
      (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step AgreeCodec.ag_sil_shape (fun _ _ => True))).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) [] frame_RELRO (fun _ _ => True) (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) [] frame_RELRO (fun _ _ => True) j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R AgreeCodec.ag_sil_shape (@RI_G AgreeCodec.ag_sil_shape) [] frame_RELRO
    (fun j T m => T = [] /\ (fun _ _ => True) j m) (fun _ => [])
    (driver_RI_AG AgreeCodec.ag_sil_shape HROOMp) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs [] (fun _ _ => True) GIL) (fun mem H => conj eq_refl (GI0 mem H)) HC).
Qed.
