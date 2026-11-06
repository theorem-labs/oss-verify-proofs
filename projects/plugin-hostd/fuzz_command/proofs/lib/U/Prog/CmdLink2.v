From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL0g YL01 YI14 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import Slot VerbsLink.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import sup_host_setting_c sup_instance_verb_c
  sup_add_c sup_chain_c rec_calls_copy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require sup_host_setting sup_instance_verb sup_add
  sup_chain sprintf strcat strcpy stpcpy strspn rec_calls_copy.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cl2_strcat : strcat_c.strcat_contract.
Proof.
  exact (U.Prog.strcat.strcat_holds U.Prog.strlen.strlen_holds
    (U.Prog.strcpy.strcpy_holds U.Prog.stpcpy.stpcpy_holds)).
Qed.

Lemma cl2_sup_host_setting_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_host_setting_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_line_of_given FG rc fx.
  vl_dep vl_arg_s_of_given FG rc fx. vl_dep vl_xmalloc_of_given FG rc fx. vl_setup FG B API rc fx.
  pose proof cl2_strcat as K_SCAT.
  eapply U.Prog.sup_host_setting.sup_host_setting_holds; eassumption.
Qed.

Lemma cl2_sup_instance_verb_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_instance_verb_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_line_of_given FG rc fx.
  vl_dep vl_arg_s_of_given FG rc fx. vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  pose proof U.Prog.strspn.strspn_holds as K_SSPN.
  eapply U.Prog.sup_instance_verb.sup_instance_verb_holds; eassumption.
Qed.

Lemma cl2_sup_add_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_add_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_hand_back_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_add.sup_add_holds; eassumption.
Qed.

Lemma cl2_sup_chain_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_chain_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_dep vl_xmalloc_of_given FG rc fx. vl_setup FG B API rc fx.
  pose proof U.Prog.sprintf.sprintf_holds as K_SPR.
  eapply U.Prog.sup_chain.sup_chain_holds; eassumption.
Qed.

Lemma cl2_rec_calls_copy_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @rec_calls_copy_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_xmalloc_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.rec_calls_copy.rec_calls_copy_holds; eassumption.
Qed.