From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import ZAllocator Contract FrameAPI Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require SlotTopG FrameProof AllocCf AgreeZlib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require ZTraceSpec AgreeShape.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Slot SlotProof SlotItProof SlotItB3q CmdLink
  CmdLink2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Slot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require HarnessPropsProof.
Import ListNotations.
Local Open Scope Z_scope.

(* The concrete ubsan frame values satisfy the cut-free slot's frame premise (CF.Slot.frame_given_u) at the
   agreement shape of the plain checksum shape. The allocator clause is the prelude's cut-free frame_allocator,
   from the halts frame allocator and the cut-free malloc/free/free(NULL) contracts (frame_allocator_of_cf). *)
Lemma cf_given_src0 :
  CF.Slot.frame_given_u src0_msyms (@zlib_API) (lib.AgreeShape.ag_shape lib.ZTraceSpec.checksum_shape)
    src0_sink_head src0_sink RA_LIB EMPTY.
Proof.
  split; [exact U.SlotTopG.ms_segs_rsegs|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact U.FrameProof.errno_below_ceiling|].
  do 13 (split; [reflexivity|]).
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact U.FrameProof.ctx_not_ro|].
  split; [exact U.FrameProof.frame_G_facts|].
  split; [exact U.FrameProof.frame_RELRO_facts|].
  split; [intros pl fs K; reflexivity|].
  split; [intros n b; reflexivity|].
  split; [intros b n H; first [exact H | exact (lib.AgreeShape.ag_room_cg _ b n H)]|].
  intros rc fx.
  exact (frame_allocator_of_cf src0_msyms (@zlib_API rc) (U.FrameProof.zlib_frame_allocator rc fx)
    U.AllocCf.zlib_malloc_contract_cf U.AllocCf.zlib_free_contract_cf U.AllocCf.src0_free_null_cf
    (U.AgreeZlib.zlib_limit rc)).
Qed.

Lemma debruijn_len_src0 : ms_debruijn_len src0_msyms = 32.
Proof. reflexivity. Qed.

(* The ubsan cut-free slot at the agreement shape: CF.SlotProof's slot with the iteration (CF.SlotItProof,
   CF.SlotItB3q.seg_b2_q), the callees (CF.CmdLink.cmd_callees_of_given with the CF.CmdLink2 lemmas), the harness
   properties, and the concrete frame values. CF.Slot.G_cmd / GI_cmd are U.Prog.Slot's texts (convertible). *)
Theorem ucg_holds : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @U.SlotAgree.lib_contract_cg fx rc (lib.AgreeShape.ag_shape lib.ZTraceSpec.checksum_shape)
    U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc) U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
    U.Prog.Slot.G_cmd U.FrameAPI.frame_RELRO U.Prog.Slot.GI_cmd j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB
    U.Reusable.YL0s.EMPTY U.FrameAPI.SLOT_STACK.
Proof.
  intros rc fx j Hj.
  exact (CF.SlotProof.fuzz_command_slot_holds
    (CF.SlotItProof.iter_spec_holds CF.SlotItB3q.seg_b2_q)
    (CF.CmdLink.cmd_callees_of_given CF.CmdLink2.cl2_sup_host_setting_of_given
      CF.CmdLink2.cl2_sup_instance_verb_of_given CF.CmdLink2.cl2_sup_add_of_given
      CF.CmdLink2.cl2_sup_chain_of_given CF.CmdLink2.cl2_rec_calls_copy_of_given)
    lib.Prog.HarnessPropsProof.harness_props_holds
    src0_msyms (@zlib_API) (lib.AgreeShape.ag_shape lib.ZTraceSpec.checksum_shape) src0_sink_head src0_sink
    RA_LIB EMPTY cf_given_src0 debruijn_len_src0 rc fx j Hj).
Qed.
