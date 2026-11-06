From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL0g YL01 YI14 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import Slot rec_calls_copy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require sup_after_reply_c sup_broadcast_c
  sup_host_setting_c sup_connect_c descriptors_get_c sup_worker_env_c sup_instance_info_c sup_call_c
  sup_instance_verb_c sup_lv2_worker_set_c descriptors_panel_get_c sup_pin_accept_c pins_clear_c
  lv2_refusals_forget_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
  sup_reset_c sup_worker_list_c sup_chain_clear_c sup_add_c descriptors_add_c sup_chain_c pins_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require SlotIter SlotProof CmdLink CmdLink2 SlotItProof
  SlotItB3q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require HarnessPropsProof.
From OSSVerify.plugin_hostd.fuzz_command Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

(* The last link of ubsan_halts for LLVMFuzzerTestOneInput (ubsan 0x14060): the frame (FrameProof), the slot
   (SlotProof) with the callees of CmdLink.cmd_callees_of_given (the supervisor calls and rec_calls_copy from
   CmdLink2) and the harness properties, for one iteration of the slot loop (ITER). *)

Section End.

Hypothesis ITER : U.Prog.SlotIter.iter_spec.

Theorem ubsan_halts_of_open : Statements.ubsan_halts.
Proof.
  apply U.Prog.Slot.ubsan_halts_of_frame; [exact U.FrameProof.frame_ubsan_holds|].
  exact (U.Prog.SlotProof.fuzz_command_slot_holds ITER
    (U.Prog.CmdLink.cmd_callees_of_given U.Prog.CmdLink2.cl2_sup_host_setting_of_given
      U.Prog.CmdLink2.cl2_sup_instance_verb_of_given U.Prog.CmdLink2.cl2_sup_add_of_given
      U.Prog.CmdLink2.cl2_sup_chain_of_given
      U.Prog.CmdLink2.cl2_rec_calls_copy_of_given)
    lib.Prog.HarnessPropsProof.harness_props_holds).
Qed.

End End.

(* One iteration of the slot loop: SlotItProof.iter_spec_holds with its (b2) step from SlotItB3q. *)
Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof. exact (ubsan_halts_of_open (U.Prog.SlotItProof.iter_spec_holds U.Prog.SlotItB3q.seg_b2_q)). Qed.
