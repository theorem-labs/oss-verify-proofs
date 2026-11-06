From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL0g YL01 YI14 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import Slot verbs_receive_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strndup_c strdup_c strlen_c strtok_r_c
  reply_c sup_resp_c sup_after_reply_c strcspn_c strncmp_c sup_broadcast_c sup_host_setting_c chain_words_c sup_connect_c
  descriptors_get_c sup_worker_env_c sup_instance_info_c sup_call_c sup_instance_verb_c sup_lv2_worker_set_c
  descriptors_panel_get_c sup_pin_accept_c pins_clear_c lv2_refusals_forget_c sup_policy_set_c sup_pool_config_c
  sup_quarantine_clear_c sup_remove_c sup_remove_all_c sup_reset_c sup_worker_list_c sup_chain_clear_c pin_set_words_c
  sup_add_c descriptors_add_c xmalloc_c socket_send_c sup_chain_c pins_set_c memcpy_c snprintf_c strspn_c strnlen_c
  memchr_c memset_c strchrnul_c strtol_c __shlim_c __intscan_c __errno_location_c record_c rec_calls_free_c
  rec_canonical_c arg_line_c arg_s_c hand_back_c answer_c answer_code_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require strcmp_c verb_is_c is_instance_verb_c atoi_c
  number_c sup_reply_code_c mix_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive strndup strdup sup_resp reply
  chain_words pin_set_words xmalloc socket_send strlen strtok_r strcmp strcspn strncmp verb_is is_instance_verb atoi
  number sup_reply_code memcpy snprintf strspn strnlen memchr memset strchrnul strtol __shlim __intscan
  __errno_location bcmp mix_call rec_shape_of RecKindB rec_calls_free record rec_canonical arg_line arg_s hand_back
  answer answer_code sup_after_reply sup_broadcast sup_connect descriptors_get sup_worker_env sup_instance_info
  sup_call sup_lv2_worker_set descriptors_panel_get sup_pin_accept pins_clear lv2_refusals_forget sup_policy_set
  sup_pool_config sup_quarantine_clear sup_remove sup_remove_all sup_reset sup_worker_list sup_chain_clear
  descriptors_add pins_set.
Import ListNotations.
Local Open Scope Z_scope.

(** * Kind A callees *)

Lemma vl_strcspn : strcspn_contract.
Proof. exact (U.Prog.strcspn.strcspn_holds U.Prog.memset.memset_holds U.Prog.strchrnul.strchrnul_holds). Qed.

Lemma vl_strnlen : strnlen_contract.
Proof. exact (U.Prog.strnlen.strnlen_holds U.Prog.memchr.memchr_holds). Qed.

Lemma vl_strtok_r : strtok_r_contract.
Proof. exact (U.Prog.strtok_r.strtok_r_holds U.Prog.strspn.strspn_holds vl_strcspn). Qed.

Lemma vl_verb_is : verb_is_c.verb_is_contract.
Proof. exact (U.Prog.verb_is.verb_is_holds vl_strcspn U.Prog.strncmp.strncmp_holds). Qed.

Lemma vl_is_instance_verb : is_instance_verb_c.is_instance_verb_contract.
Proof. exact (U.Prog.is_instance_verb.is_instance_verb_holds vl_strcspn U.Prog.strncmp.strncmp_holds). Qed.

Lemma vl_sup_reply_code : sup_reply_code_c.sup_reply_code_contract.
Proof. exact (U.Prog.sup_reply_code.sup_reply_code_holds U.Prog.strncmp.strncmp_holds U.Prog.atoi.atoi_holds). Qed.

Lemma vl_strtol : strtol_contract.
Proof.
  exact (U.Prog.strtol.strtol_holds U.Prog.__shlim.__shlim_holds
    (U.Prog.__intscan.__intscan_holds U.Prog.__errno_location.__errno_location_holds U.Prog.__shlim.__shlim_holds)).
Qed.

Lemma vl_number : number_c.number_contract.
Proof. exact (U.Prog.number.number_holds vl_strtol). Qed.

Lemma vl_mix_call : mix_call_c.mix_call_contract.
Proof. exact (U.Prog.mix_call.mix_call_holds U.Prog.strlen.strlen_holds). Qed.

Lemma vl_rec_shape_of : rec_shape_of_contract.
Proof. exact (U.Prog.rec_shape_of.rec_shape_of_holds U.Prog.strlen.strlen_holds U.Prog.bcmp.bcmp_holds). Qed.

(** * Frame facts *)

(* The frame facts of frame_given_u at run ceiling rc and float state fx, in the forms of the callee Sections'
   hypotheses, and the Kind A contracts. *)
Ltac vl_setup FG B API rc fx :=
  let H := fresh "FG" in pose proof FG as H;
  destruct H as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 &
    F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31);
  destruct (F31 rc fx) as (MAL & FRE & FNU & REA & CAL & SLK & CTXO & BLO & BND & BWR & EUN & GRW & LNL & AX &
    GNO & RNO);
  pose proof (F6 rc) as ELOW;
  pose proof (fun fx' : FPState => proj1 (proj2 (F31 rc fx'))) as FREEA;
  assert (ERRNO : errno_addr B = 0x3441c) by (unfold errno_addr; rewrite F16, F17; reflexivity);
  assert (RELF : forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_RELRO a ->
      in_img B a /\ ~ owned B L A a)
    by (intros L A mem md a HM Ha; exact (conj (proj1 (F27 a Ha)) (RNO L A mem md a HM Ha)));
  assert (RECI : forall a, U.Prog.RecKindB.rec_area a -> in_img B a /\ ~ (errno_addr B <= a < errno_addr B + 4))
    by (intros a Ha; destruct (F26 a (U.Prog.reply.rec_area_G a Ha)) as (I1 & _ & _ & I4); exact (conj I1 I4));
  assert (RECO : forall L A mem md a, aa_MR (API rc) L A mem md -> U.Prog.RecKindB.rec_area a -> ~ owned B L A a)
    by (intros L A mem md a HM Ha; exact (GNO L A mem md a HM (U.Prog.reply.rec_area_G a Ha)));
  pose proof U.Prog.strcmp.strcmp_holds as K_SC;
  pose proof U.Prog.strncmp.strncmp_holds as K_SNC;
  pose proof U.Prog.atoi.atoi_holds as K_ATOI;
  pose proof U.Prog.snprintf.snprintf_holds as K_SNP;
  pose proof U.Prog.strlen.strlen_holds as K_SLEN;
  pose proof U.Prog.memcpy.memcpy_holds as K_MCPY;
  pose proof vl_strcspn as K_SCS;
  pose proof vl_strnlen as K_SNL;
  pose proof vl_strtok_r as K_STOK;
  pose proof vl_verb_is as K_VIS;
  pose proof vl_is_instance_verb as K_IIV;
  pose proof vl_sup_reply_code as K_RC;
  pose proof vl_number as K_NUM;
  pose proof vl_mix_call as K_MIX;
  pose proof vl_rec_shape_of as K_RSO.

Ltac vl_dep T FG rc fx :=
  pose proof (fun f : FPState => T _ _ _ _ _ _ _ FG rc f); pose proof (T _ _ _ _ _ _ _ FG rc fx).

(** * Kind B callees without open premises *)

Lemma vl_xmalloc_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @xmalloc_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.xmalloc.xmalloc_holds; eassumption.
Qed.

Lemma vl_socket_send_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @socket_send_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. pose proof (vl_xmalloc_of_given _ _ _ _ _ _ _ FG rc fx) as XM.
  vl_setup FG B API rc fx.
  eapply U.Prog.socket_send.socket_send_holds; eassumption.
Qed.

Lemma vl_strndup_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @strndup_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.strndup.strndup_holds; eassumption.
Qed.

Lemma vl_strdup_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @strdup_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.strdup.strdup_holds; eassumption.
Qed.

Lemma vl_sup_resp_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_resp_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx.
  pose proof (fun fx' : FPState => vl_xmalloc_of_given _ _ _ _ _ _ _ FG rc fx') as XM.
  vl_setup FG B API rc fx.
  eapply U.Prog.sup_resp.sup_resp_holds; eassumption.
Qed.

Lemma vl_reply_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @reply_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. pose proof (vl_socket_send_of_given _ _ _ _ _ _ _ FG rc fx) as SSEND.
  vl_setup FG B API rc fx.
  eapply U.Prog.reply.reply_holds; eassumption.
Qed.

Lemma vl_rec_calls_free_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @rec_calls_free_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.rec_calls_free.rec_calls_free_holds; eassumption.
Qed.

Lemma vl_record_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @record_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_rec_calls_free_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.record.record_holds; eassumption.
Qed.

Lemma vl_rec_canonical_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @rec_canonical_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_xmalloc_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.rec_canonical.rec_canonical_holds; eassumption.
Qed.

Lemma vl_arg_line_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @arg_line_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_rec_canonical_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.arg_line.arg_line_holds; eassumption.
Qed.

Lemma vl_arg_s_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @arg_s_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_xmalloc_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.arg_s.arg_s_holds; eassumption.
Qed.

Lemma vl_hand_back_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @hand_back_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_xmalloc_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.hand_back.hand_back_holds; eassumption.
Qed.

Lemma vl_answer_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @answer_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_hand_back_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.answer.answer_holds; eassumption.
Qed.

Lemma vl_answer_code_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @answer_code_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_hand_back_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.answer_code.answer_code_holds; eassumption.
Qed.

Lemma vl_sup_after_reply_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_after_reply_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply U.Prog.sup_after_reply.sup_after_reply_holds; eassumption.
Qed.

Lemma vl_sup_broadcast_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_broadcast_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_line_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_broadcast.sup_broadcast_holds; eassumption.
Qed.

Lemma vl_sup_connect_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_connect_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_arg_line_of_given FG rc fx. vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_connect.sup_connect_holds; eassumption.
Qed.

Lemma vl_descriptors_get_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @descriptors_get_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.descriptors_get.descriptors_get_holds; eassumption.
Qed.

Lemma vl_sup_worker_env_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_worker_env_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_worker_env.sup_worker_env_holds; eassumption.
Qed.

Lemma vl_sup_instance_info_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_instance_info_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_instance_info.sup_instance_info_holds; eassumption.
Qed.

Lemma vl_sup_call_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_call_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_arg_line_of_given FG rc fx. vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_call.sup_call_holds; eassumption.
Qed.

Lemma vl_sup_lv2_worker_set_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_lv2_worker_set_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_lv2_worker_set.sup_lv2_worker_set_holds; eassumption.
Qed.

Lemma vl_descriptors_panel_get_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @descriptors_panel_get_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.descriptors_panel_get.descriptors_panel_get_holds; eassumption.
Qed.

Lemma vl_sup_pin_accept_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_pin_accept_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_pin_accept.sup_pin_accept_holds; eassumption.
Qed.

Lemma vl_pins_clear_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @pins_clear_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_code_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.pins_clear.pins_clear_holds; eassumption.
Qed.

Lemma vl_lv2_refusals_forget_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @lv2_refusals_forget_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply U.Prog.lv2_refusals_forget.lv2_refusals_forget_holds; eassumption.
Qed.

Lemma vl_sup_policy_set_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_policy_set_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_policy_set.sup_policy_set_holds; eassumption.
Qed.

Lemma vl_sup_pool_config_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_pool_config_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_pool_config.sup_pool_config_holds; eassumption.
Qed.

Lemma vl_sup_quarantine_clear_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_quarantine_clear_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_quarantine_clear.sup_quarantine_clear_holds; eassumption.
Qed.

Lemma vl_sup_remove_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_remove_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_remove.sup_remove_holds; eassumption.
Qed.

Lemma vl_sup_remove_all_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_remove_all_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_answer_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply U.Prog.sup_remove_all.sup_remove_all_holds; eassumption.
Qed.

Lemma vl_sup_reset_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_reset_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_reset.sup_reset_holds; eassumption.
Qed.

Lemma vl_sup_worker_list_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_worker_list_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_answer_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply U.Prog.sup_worker_list.sup_worker_list_holds; eassumption.
Qed.

Lemma vl_sup_chain_clear_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_chain_clear_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.sup_chain_clear.sup_chain_clear_holds; eassumption.
Qed.

Lemma vl_descriptors_add_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @descriptors_add_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_setup FG B API rc fx.
  eapply U.Prog.descriptors_add.descriptors_add_holds; eassumption.
Qed.

Lemma vl_pins_set_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @pins_set_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. vl_dep vl_record_of_given FG rc fx. vl_dep vl_arg_s_of_given FG rc fx.
  vl_dep vl_answer_code_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply U.Prog.pins_set.pins_set_holds; eassumption.
Qed.

(** * The callees whose own proofs are not done in the ubsan build *)

Section VLink.

(* The supervisor calls that verbs_receive and chain_words reach, at their ubsan contracts, for every frame of
   frame_given_u, run ceiling and float state. *)
Hypothesis H_sup_host_setting : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_host_setting_contract fx rc B (API rc).
Hypothesis H_sup_instance_verb : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_instance_verb_contract fx rc B (API rc).
Hypothesis H_sup_add : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_add_contract fx rc B (API rc).
Hypothesis H_sup_chain : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @sup_chain_contract fx rc B (API rc).

Lemma vl_chain_words_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @chain_words_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx.
  pose proof (H_sup_chain _ _ _ _ _ _ _ FG rc fx) as SCH.
  pose proof (vl_sup_resp_of_given _ _ _ _ _ _ _ FG rc fx) as SRESP.
  vl_setup FG B API rc fx.
  eapply U.Prog.chain_words.chain_words_holds; eassumption.
Qed.

Lemma vl_pin_set_words_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @pin_set_words_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx.
  pose proof (vl_pins_set_of_given _ _ _ _ _ _ _ FG rc fx) as PSET.
  pose proof (fun fx' : FPState => vl_lv2_refusals_forget_of_given _ _ _ _ _ _ _ FG rc fx') as LV2.
  vl_setup FG B API rc fx.
  eapply U.Prog.pin_set_words.pin_set_words_holds; eassumption.
Qed.

Theorem verbs_receive_of_given : forall B API LS SH SK ra empty, frame_given_u B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @verbs_receive_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx.
  pose proof (fun f : FPState => vl_strndup_of_given _ _ _ _ _ _ _ FG rc f) as SNDUP.
  pose proof (fun f : FPState => vl_strdup_of_given _ _ _ _ _ _ _ FG rc f) as SDUP.
  pose proof (fun f : FPState => vl_sup_resp_of_given _ _ _ _ _ _ _ FG rc f) as SRESP.
  pose proof (fun f : FPState => vl_reply_of_given _ _ _ _ _ _ _ FG rc f) as RP.
  pose proof (fun f : FPState => vl_sup_after_reply_of_given _ _ _ _ _ _ _ FG rc f) as SAR.
  pose proof (fun f : FPState => vl_sup_broadcast_of_given _ _ _ _ _ _ _ FG rc f) as DB.
  pose proof (fun f : FPState => H_sup_host_setting _ _ _ _ _ _ _ FG rc f) as DH.
  pose proof (fun f : FPState => vl_chain_words_of_given _ _ _ _ _ _ _ FG rc f) as CW.
  pose proof (fun f : FPState => vl_sup_connect_of_given _ _ _ _ _ _ _ FG rc f) as DCONN.
  pose proof (fun f : FPState => vl_descriptors_get_of_given _ _ _ _ _ _ _ FG rc f) as DDG.
  pose proof (fun f : FPState => vl_sup_worker_env_of_given _ _ _ _ _ _ _ FG rc f) as DENV.
  pose proof (fun f : FPState => vl_sup_instance_info_of_given _ _ _ _ _ _ _ FG rc f) as DII.
  pose proof (fun f : FPState => vl_sup_call_of_given _ _ _ _ _ _ _ FG rc f) as DCALL.
  pose proof (fun f : FPState => H_sup_instance_verb _ _ _ _ _ _ _ FG rc f) as DIV.
  pose proof (fun f : FPState => vl_sup_lv2_worker_set_of_given _ _ _ _ _ _ _ FG rc f) as DLV2.
  pose proof (fun f : FPState => vl_descriptors_panel_get_of_given _ _ _ _ _ _ _ FG rc f) as DPG.
  pose proof (fun f : FPState => vl_sup_pin_accept_of_given _ _ _ _ _ _ _ FG rc f) as DPA.
  pose proof (fun f : FPState => vl_pins_clear_of_given _ _ _ _ _ _ _ FG rc f) as DPC.
  pose proof (fun f : FPState => vl_lv2_refusals_forget_of_given _ _ _ _ _ _ _ FG rc f) as DLRF.
  pose proof (fun f : FPState => vl_sup_policy_set_of_given _ _ _ _ _ _ _ FG rc f) as DPOL.
  pose proof (fun f : FPState => vl_sup_pool_config_of_given _ _ _ _ _ _ _ FG rc f) as DPOOL.
  pose proof (fun f : FPState => vl_sup_quarantine_clear_of_given _ _ _ _ _ _ _ FG rc f) as DQC.
  pose proof (fun f : FPState => vl_sup_remove_of_given _ _ _ _ _ _ _ FG rc f) as DREM.
  pose proof (fun f : FPState => vl_sup_remove_all_of_given _ _ _ _ _ _ _ FG rc f) as DRALL.
  pose proof (fun f : FPState => vl_sup_reset_of_given _ _ _ _ _ _ _ FG rc f) as DRST.
  pose proof (fun f : FPState => vl_sup_worker_list_of_given _ _ _ _ _ _ _ FG rc f) as DWL.
  pose proof (fun f : FPState => vl_sup_chain_clear_of_given _ _ _ _ _ _ _ FG rc f) as DCC.
  pose proof (fun f : FPState => vl_pin_set_words_of_given _ _ _ _ _ _ _ FG rc f) as PSW.
  pose proof (fun f : FPState => H_sup_add _ _ _ _ _ _ _ FG rc f) as SA.
  pose proof (fun f : FPState => vl_descriptors_add_of_given _ _ _ _ _ _ _ FG rc f) as DA.
  vl_setup FG B API rc fx.
  eapply U.Prog.verbs_receive.verbs_receive_holds; eassumption.
Qed.

End VLink.
