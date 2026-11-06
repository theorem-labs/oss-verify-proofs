(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/AsanTop.v (a working branch
   0bed23e5b69, itself from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v) for fuzz_ctrl: the plain side at fuzz_ctrl's agreement
   shape ag_shape checksum_shape, built as lib/CtrlAgree.v and lib/AgreeFrame.v build it for the ubsan agreement. *)
(* The plain build's proved realization of SPECX at 2^34 for fuzz_ctrl's ASan agreements: AgreeTop.plain_rz_of_contracts_R
   fed by the plain entry-function contract, which is the closed plain slot of the ubsan agreement
   (Prog/Seg/Slot.v slot_of_lemmas over Prog/Seg/Segs.v segs_holds at the frame facts plain_frame_facts_a). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_ctrl Require Statements Images.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZImage OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZTraceSpec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AllocSlots OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AllocRoom OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZComplete OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZAllocator OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Contract OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameAPI OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameSlotG OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Agree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import AgreeTop.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AgreeZlib OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AgreeLim.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import AgreeShape.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.SlotAgree.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof OSSVerify.Proofs.libreac.fuzz_ctrl.lib.SlotTopG.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Slot Segs SlotLink.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Local Abbreviation AGS := (ag_shape checksum_shape).

(* lib/CtrlAgree.v plain_frame_facts, copied (CtrlAgree.v also builds the ubsan slot; this file needs the plain side only). *)
Lemma plain_frame_facts_a :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.SlotInv.frame_facts src0_msyms (@zlib_API) AGS src0_sink_head src0_sink
    RA_LIB EMPTY.
Proof.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.SlotInv.frame_facts.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.SlotTopG.ms_segs_rsegs
             | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof.errno_below_ceiling
             | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof.ctx_not_ro
             | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof.frame_G_facts
             | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof.frame_RELRO_facts
             | exact (ag_room_g checksum_shape) | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof.zlib_frame_allocator
             | (intros; reflexivity) | reflexivity
             | (match goal with |- (_ < _ < _)%Z => split; vm_compute; reflexivity | |- (_ < _)%Z => vm_compute; reflexivity
                | |- (_ mod _ = _)%Z => vm_compute; reflexivity end) ].
Qed.

Lemma ctrl_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=AGS) inp).
Proof.
  assert (Hp : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc AGS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      [] frame_RELRO (fun _ _ => True) j ENTRY RA_LIB EMPTY SLOT_STACK).
  { intros rc fx j Hj.
    exact (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg.Slot.slot_of_lemmas fx rc src0_msyms (@zlib_API) AGS
      src0_sink_head src0_sink RA_LIB EMPTY plain_frame_facts_a
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg.Segs.segs_holds fx rc src0_msyms (@zlib_API) AGS
         src0_sink_head src0_sink RA_LIB EMPTY plain_frame_facts_a
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg.SlotLink.callee_contracts_holds
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg.SlotLink.fragment_contract_holds) j Hj). }
  assert (HROOMp : forall data, @room_calls AGS (payload_len data) (calls data) SBD_AG)
    by (intros data; apply ag_room_calls).
  assert (HG : forall a, in_globals [] a -> in_globals frame_G a) by (intros a (lo & len & [] & _)).
  assert (GIL : G_local_c src0_msyms [] (fun _ _ => True)) by (intros j m m' _ _; exact I).
  assert (GI0 : forall mem, G_img_c src0_msyms [] mem -> (fun _ _ => True) 0%nat mem) by (intros mem _; exact I).
  assert (HC : zlib_runtime_contracts_R AGS (@RI_G AGS) [] frame_RELRO
    (fun j T m => T = [] /\ (fun _ _ => True) j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G AGS) [] frame_RELRO _ (fun _ => [])
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step AGS (fun _ _ => True))).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) [] frame_RELRO (fun _ _ => True) (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) [] frame_RELRO (fun _ _ => True) j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R AGS (@RI_G AGS) [] frame_RELRO
    (fun j T m => T = [] /\ (fun _ _ => True) j m) (fun _ => [])
    (driver_RI_AG AGS HROOMp) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs [] (fun _ _ => True) GIL) (fun mem H => conj eq_refl (GI0 mem H)) HC).
Qed.
