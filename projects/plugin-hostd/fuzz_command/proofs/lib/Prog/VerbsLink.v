From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL0g YL01 YI14 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP
  VerbsB Slot verbs_receive_c strnlen_c memcpy_c strspn_c strcspn_c rec_calls_free_c strdup_c strcmp_c strncmp_c
  atoi_c snprintf_c strlen_c sup_reply_code_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strndup_c strtok_r_c
  reply_c sup_resp_c sup_after_reply_c sup_broadcast_c sup_host_setting_c chain_words_c sup_connect_c
  descriptors_get_c sup_worker_env_c sup_instance_info_c sup_call_c sup_instance_verb_c sup_lv2_worker_set_c
  descriptors_panel_get_c sup_pin_accept_c pins_clear_c lv2_refusals_forget_c sup_policy_set_c sup_pool_config_c
  sup_quarantine_clear_c sup_remove_c sup_remove_all_c sup_reset_c sup_worker_list_c sup_chain_clear_c
  pin_set_words_c sup_add_c descriptors_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import xstrdup_c rec_canonical_c arg_line_c
  arg_i_c hand_back_c answer_code_c socket_send_c pins_set_c sup_chain_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require mix_call_c number_c verb_is_c
  is_instance_verb_c RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require
  strlen strcmp strncmp atoi snprintf memcpy strspn strtok_r strtol __shlim __intscan __errno_location number
  verb_is is_instance_verb mix_call xstrdup rec_canonical arg_line arg_i hand_back answer_code socket_send reply
  strndup sup_resp sup_after_reply sup_broadcast sup_connect descriptors_get sup_worker_env sup_instance_info
  sup_call sup_instance_verb sup_lv2_worker_set descriptors_panel_get sup_pin_accept pins_clear
  lv2_refusals_forget sup_policy_set sup_pool_config sup_quarantine_clear sup_remove sup_remove_all sup_reset
  sup_worker_list sup_chain_clear descriptors_add pins_set pin_set_words chain_words answer sup_add verbs_receive
  strcat strcpy stpcpy sup_host_setting sprintf sup_chain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CmdLink.
Import ListNotations.
Local Open Scope Z_scope.

Lemma mix_call_ok : mix_call_c.mix_call_contract.
Proof. exact (lib.Prog.mix_call.mix_call_holds lib.Prog.strlen.strlen_holds). Qed.

Lemma number_ok : number_c.number_contract.
Proof.
  exact (lib.Prog.number.number_holds (lib.Prog.strtol.strtol_holds lib.Prog.__shlim.__shlim_holds
    (lib.Prog.__intscan.__intscan_holds lib.Prog.__errno_location.__errno_location_holds
      lib.Prog.__shlim.__shlim_holds))).
Qed.

Lemma strtok_r_ok : strtok_r_contract.
Proof. exact (lib.Prog.strtok_r.strtok_r_holds lib.Prog.strspn.strspn_holds strcspn_ok). Qed.

Lemma verb_is_ok : verb_is_c.verb_is_contract.
Proof. exact (lib.Prog.verb_is.verb_is_holds strcspn_ok lib.Prog.strncmp.strncmp_holds). Qed.

Lemma is_instance_verb_ok : is_instance_verb_c.is_instance_verb_contract.
Proof. exact (lib.Prog.is_instance_verb.is_instance_verb_holds strcspn_ok lib.Prog.strncmp.strncmp_holds). Qed.

Lemma vl_frame : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState),
  errno_addr B = 0x3413c /\
  (forall a, in_globals frame_G a -> ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall a, lib.Prog.RecKindB.rec_area a -> in_img B a /\ ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall L A mem md a, aa_MR (API rc) L A mem md -> lib.Prog.RecKindB.rec_area a -> ~ owned B L A a) /\
  (forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_RELRO a -> in_img B a /\ ~ owned B L A a).
Proof.
  intros B API LS SH SK ra empty FG rc fx. cl_setup FG B API rc fx.
  split; [unfold errno_addr; lia|].
  split; [intros a Ha; exact (proj2 (proj2 (proj2 (F26 a Ha))))|].
  split; [intros a Ha; destruct (F26 a (lib.Prog.reply.rec_area_G a Ha)) as (I1 & _ & _ & I4); exact (conj I1 I4)|].
  split; [intros L A mem md a HM Ha; exact (GNO L A mem md a HM (lib.Prog.reply.rec_area_G a Ha))|].
  intros L A mem md a HM Ha. exact (conj (proj1 (F27 a Ha)) (RNO L A mem md a HM Ha)).
Qed.

Ltac vl_setup FG B API rc fx :=
  cl_setup FG B API rc fx;
  destruct (vl_frame _ _ _ _ _ _ _ FG rc fx) as (ERRNO & GERR & RECI & RECO & RELI);
  pose proof strnlen_ok as K_SNL;
  pose proof rec_shape_of_ok as K_RSO;
  pose proof sup_reply_code_ok as K_RC;
  pose proof mix_call_ok as K_MIX;
  pose proof number_ok as K_NUM;
  pose proof strtok_r_ok as K_STOK;
  pose proof verb_is_ok as K_VIS;
  pose proof is_instance_verb_ok as K_IIV.

Ltac dep T FG rc fx :=
  pose proof (fun f : FPState => T _ _ _ _ _ _ _ FG rc f); pose proof (T _ _ _ _ _ _ _ FG rc fx).

Lemma xstrdup_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @xstrdup_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.xstrdup.xstrdup_holds; eassumption.
Qed.

Lemma rec_canonical_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @rec_canonical_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.rec_canonical.rec_canonical_holds; eassumption.
Qed.

Lemma arg_line_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @arg_line_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_canonical_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.arg_line.arg_line_holds; eassumption.
Qed.

Lemma arg_i_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @arg_i_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.arg_i.arg_i_holds; eassumption.
Qed.

Lemma hand_back_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @hand_back_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.hand_back.hand_back_holds; eassumption.
Qed.

Lemma answer_code_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @answer_code_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep hand_back_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.answer_code.answer_code_holds; eassumption.
Qed.

Lemma answer_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @answer_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep hand_back_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.answer.answer_holds; eassumption.
Qed.

Lemma socket_send_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @socket_send_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.socket_send.socket_send_holds; eassumption.
Qed.

Lemma reply_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @reply_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep socket_send_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.reply.reply_holds; eassumption.
Qed.

Lemma strndup_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @strndup_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.strndup.strndup_holds; eassumption.
Qed.

Lemma sup_resp_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_resp_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_resp.sup_resp_holds; eassumption.
Qed.

Lemma sup_after_reply_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_after_reply_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep xstrdup_of_given FG rc fx.
  dep arg_i_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_after_reply.sup_after_reply_holds; eassumption.
Qed.

Lemma pins_clear_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @pins_clear_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep xstrdup_of_given FG rc fx.
  dep answer_code_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.pins_clear.pins_clear_holds; eassumption.
Qed.

Lemma lv2_refusals_forget_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @lv2_refusals_forget_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep xstrdup_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply lib.Prog.lv2_refusals_forget.lv2_refusals_forget_holds; eassumption.
Qed.

Lemma descriptors_add_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @descriptors_add_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep xstrdup_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply lib.Prog.descriptors_add.descriptors_add_holds; eassumption.
Qed.

Lemma pins_set_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @pins_set_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep xstrdup_of_given FG rc fx.
  dep answer_code_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.pins_set.pins_set_holds; eassumption.
Qed.

Lemma pin_set_words_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @pin_set_words_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep pins_set_of_given FG rc fx. dep lv2_refusals_forget_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply lib.Prog.pin_set_words.pin_set_words_holds; eassumption.
Qed.

Lemma sup_broadcast_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_broadcast_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep arg_line_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_broadcast.sup_broadcast_holds; eassumption.
Qed.

Lemma sup_connect_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_connect_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. dep arg_line_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_connect.sup_connect_holds; eassumption.
Qed.

Lemma descriptors_get_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @descriptors_get_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.descriptors_get.descriptors_get_holds; eassumption.
Qed.

Lemma sup_worker_env_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_worker_env_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_worker_env.sup_worker_env_holds; eassumption.
Qed.

Lemma sup_instance_info_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_instance_info_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep arg_i_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_instance_info.sup_instance_info_holds; eassumption.
Qed.

Lemma sup_call_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_call_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep arg_i_of_given FG rc fx. dep arg_line_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_call.sup_call_holds; eassumption.
Qed.

Lemma sup_instance_verb_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_instance_verb_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep arg_i_of_given FG rc fx. dep arg_line_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_instance_verb.sup_instance_verb_holds; eassumption.
Qed.

Lemma sup_lv2_worker_set_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_lv2_worker_set_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_lv2_worker_set.sup_lv2_worker_set_holds; eassumption.
Qed.

Lemma descriptors_panel_get_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @descriptors_panel_get_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.descriptors_panel_get.descriptors_panel_get_holds; eassumption.
Qed.

Lemma sup_pin_accept_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_pin_accept_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_pin_accept.sup_pin_accept_holds; eassumption.
Qed.

Lemma sup_policy_set_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_policy_set_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_policy_set.sup_policy_set_holds; eassumption.
Qed.

Lemma sup_pool_config_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_pool_config_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. dep arg_i_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_pool_config.sup_pool_config_holds; eassumption.
Qed.

Lemma sup_quarantine_clear_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_quarantine_clear_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_quarantine_clear.sup_quarantine_clear_holds; eassumption.
Qed.

Lemma sup_remove_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_remove_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep arg_i_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_remove.sup_remove_holds; eassumption.
Qed.

Lemma sup_remove_all_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_remove_all_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply lib.Prog.sup_remove_all.sup_remove_all_holds; eassumption.
Qed.

Lemma sup_reset_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_reset_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_reset.sup_reset_holds; eassumption.
Qed.

Lemma sup_worker_list_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_worker_list_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply lib.Prog.sup_worker_list.sup_worker_list_holds; eassumption.
Qed.

Lemma sup_chain_clear_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_chain_clear_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep answer_of_given FG rc fx.
  dep arg_i_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.sup_chain_clear.sup_chain_clear_holds; eassumption.
Qed.

Lemma sup_add_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_add_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep xstrdup_of_given FG rc fx.
  dep arg_i_of_given FG rc fx. dep hand_back_of_given FG rc fx. dep answer_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply lib.Prog.sup_add.sup_add_holds; eassumption.
Qed.

Lemma sup_host_setting_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_host_setting_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep arg_line_of_given FG rc fx.
  dep arg_i_of_given FG rc fx. dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  pose proof (fun f : FPState => proj1 (F31 rc f)) as MALA.
  pose proof (lib.Prog.strcat.strcat_holds lib.Prog.strlen.strlen_holds
    (lib.Prog.strcpy.strcpy_holds lib.Prog.stpcpy.stpcpy_holds)) as K_SCAT.
  eapply lib.Prog.sup_host_setting.sup_host_setting_holds; eassumption.
Qed.

Lemma sup_chain_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_chain_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep rec_calls_free_of_given FG rc fx. dep arg_i_of_given FG rc fx.
  dep xstrdup_of_given FG rc fx. dep answer_of_given FG rc fx. vl_setup FG B API rc fx.
  pose proof lib.Prog.sprintf.sprintf_holds as K_SPR.
  eapply lib.Prog.sup_chain.sup_chain_holds; eassumption.
Qed.

Lemma chain_words_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @chain_words_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep sup_chain_of_given FG rc fx. dep sup_resp_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply lib.Prog.chain_words.chain_words_holds; eassumption.
Qed.

Lemma verbs_receive_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @verbs_receive_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx.
  dep strndup_of_given FG rc fx. dep strdup_of_given FG rc fx. dep sup_resp_of_given FG rc fx.
  dep reply_of_given FG rc fx. dep sup_after_reply_of_given FG rc fx. dep sup_broadcast_of_given FG rc fx.
  dep sup_host_setting_of_given FG rc fx. dep chain_words_of_given FG rc fx. dep sup_connect_of_given FG rc fx.
  dep descriptors_get_of_given FG rc fx. dep sup_worker_env_of_given FG rc fx.
  dep sup_instance_info_of_given FG rc fx. dep sup_call_of_given FG rc fx.
  dep sup_instance_verb_of_given FG rc fx. dep sup_lv2_worker_set_of_given FG rc fx.
  dep descriptors_panel_get_of_given FG rc fx. dep sup_pin_accept_of_given FG rc fx.
  dep pins_clear_of_given FG rc fx. dep lv2_refusals_forget_of_given FG rc fx.
  dep sup_policy_set_of_given FG rc fx. dep sup_pool_config_of_given FG rc fx.
  dep sup_quarantine_clear_of_given FG rc fx. dep sup_remove_of_given FG rc fx.
  dep sup_remove_all_of_given FG rc fx. dep sup_reset_of_given FG rc fx. dep sup_worker_list_of_given FG rc fx.
  dep sup_chain_clear_of_given FG rc fx. dep pin_set_words_of_given FG rc fx.
  dep descriptors_add_of_given FG rc fx. dep sup_add_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply lib.Prog.verbs_receive.verbs_receive_holds; eassumption.
Qed.
