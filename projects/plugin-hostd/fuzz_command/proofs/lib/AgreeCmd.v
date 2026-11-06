From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import
  ZTraceSpec ZAllocator SlotTopG Contract FrameAPI Img0 FrameProof SlotAgree AllocSlots AgreeShape AgreeFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import Slot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Slot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require SlotTopG.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require
  Slot SlotCallees CmdLink VerbsLink CmdEnd HarnessPropsProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require SlotCallees SlotProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require SlotTopCF.
Import ListNotations.
Open Scope Z_scope.

(* The concrete frame values satisfy the AG slot's frame premise at the agreement shape of the plain
   frame's shape. *)
Lemma ag_given_src0 :
  AG.Slot.frame_given src0_msyms (@zlib_API) (ag_shape checksum_shape) src0_sink_head src0_sink RA_LIB EMPTY.
Proof.
  split; [exact ms_segs_rsegs|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact errno_below_ceiling|].
  do 13 (split; [reflexivity|]).
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact ctx_not_ro|].
  split; [exact frame_G_facts|].
  split; [exact frame_RELRO_facts|].
  split; [intros pl fs K; rewrite ag_LIBK; reflexivity|].
  split; [intros n b; exact (ag_delta checksum_shape n b)|].
  split; [intros b n H; exact H|].
  exact zlib_frame_allocator.
Qed.

Lemma debruijn_len_src0 : ms_debruijn_len src0_msyms = 32.
Proof. reflexivity. Qed.

(* The plain frame premise from the AG one, at the plain frame's shape: the conjuncts that do not
   mention the shape carry over, and checksum_shape has the plain LIBK, lib_delta and room (cap CAPMAX). *)
Lemma plain_given_of_ag : forall B API LS SH SK ra empty, AG.Slot.frame_given B API LS SH SK ra empty ->
  lib.Prog.Slot.frame_given B API checksum_shape SH SK ra empty.
Proof.
  intros B API LS SH SK ra empty (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 &
    F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & _ & _ & _ & F31).
  refine (conj F0 (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj F7 (conj F8 (conj F9 (conj F10
    (conj F11 (conj F12 (conj F13 (conj F14 (conj F15 (conj F16 (conj F17 (conj F18 (conj F19 (conj F20 (conj F21
    (conj F22 (conj F23 (conj F24 (conj F25 (conj F26 (conj F27 (conj _ (conj _ (conj _ F31))))))))))))))))))))))))))))))).
  - intros pl fs K. reflexivity.
  - intros n b. reflexivity.
  - intros b n H. exact H.
Qed.

(* The callees of the AG slot: lib/Prog/CmdLink.v cmd_callees_of_given through the plain frame premise
   (AG.SlotCallees.cmd_callees is the plain cmd_callees by unfolding). *)
Lemma ag_cmd_callees : forall B API LS SH SK ra empty, AG.Slot.frame_given B API LS SH SK ra empty ->
  lib.Prog.AG.SlotCallees.cmd_callees B API.
Proof.
  intros B API LS SH SK ra empty FG.
  exact (lib.Prog.CmdLink.cmd_callees_of_given lib.Prog.VerbsLink.verbs_receive_of_given
    lib.Prog.CmdEnd.rec_calls_copy_of_given B API checksum_shape SH SK ra empty (plain_given_of_ag B API LS SH SK ra empty FG)).
Qed.

(* The plain slot at the agreement room. *)
Lemma ag_slot : AG.Slot.fuzz_command_slot.
Proof.
  exact (lib.Prog.AG.SlotProof.fuzz_command_slot_ag_closed ag_cmd_callees
    lib.Prog.HarnessPropsProof.harness_props_holds).
Qed.

Section AgreeCmd.

(* The ubsan cut-free slot at the agreement shape. *)
Hypothesis UCG : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @U.SlotAgree.lib_contract_cg fx rc (ag_shape checksum_shape) U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
    U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
    U.Prog.Slot.G_cmd U.FrameAPI.frame_RELRO U.Prog.Slot.GI_cmd j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB
    U.Reusable.YL0s.EMPTY U.FrameAPI.SLOT_STACK.

Theorem ubsan_agrees_of_ucg : Statements.ubsan_agrees.
Proof.
  apply (ubsan_agrees_of_slots (ag_shape checksum_shape) AG.Slot.G_cmd AG.Slot.GI_cmd
    U.Prog.Slot.G_cmd U.Prog.Slot.GI_cmd).
  - intros a Ha. exact Ha.
  - exact (AG.Slot.GI_cmd_local src0_msyms ms_segs_rsegs).
  - exact (AG.Slot.GI_cmd_img src0_msyms ms_segs_rsegs).
  - intros rc fx j Hj.
    exact (ag_slot src0_msyms (@zlib_API) (ag_shape checksum_shape) src0_sink_head src0_sink RA_LIB EMPTY
      ag_given_src0 debruijn_len_src0 rc fx j Hj).
  - intros data. apply ag_room_calls.
  - intros a Ha. exact Ha.
  - exact (U.Prog.Slot.GI_cmd_local U.Reusable.YH02.src0_msyms U.SlotTopG.ms_segs_rsegs).
  - exact (U.Prog.Slot.GI_cmd_img U.Reusable.YH02.src0_msyms U.SlotTopG.ms_segs_rsegs).
  - exact UCG.
Qed.

End AgreeCmd.

(* The ubsan cut-free slot is CF.SlotTopCF.ucg_holds (lib/U/Prog/CF, generated by twin.py). *)
Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof. exact (ubsan_agrees_of_ucg OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF.SlotTopCF.ucg_holds). Qed.
