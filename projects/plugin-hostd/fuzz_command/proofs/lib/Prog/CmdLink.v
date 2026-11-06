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
  VerbsB CommandB verbs_receive_c send_message_c check_words_c check_round_trip_c rec_clear_c
  check_reply_c check_arity_c check_refusal_c strnlen_c memcpy_c strspn_c strcspn_c HarnessProps Slot SlotCallees
  rec_calls_copy_c rec_calls_free_c rec_calls_equal_c joined_c strdup_c strcmp_c strncmp_c bcmp_c atoi_c
  snprintf_c strlen_c memchr_c memset_c strchrnul_c check_words_add_c check_words_chain_c check_words_pin_set_c
  sup_reply_code_c check_reply_answer_c rec_shape_of_c rec_code_declared_c syntax_reply_matches_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require
  send_message check_words check_round_trip check_reply check_arity check_refusal strnlen memcpy strspn strcspn
  strcmp strncmp bcmp atoi snprintf strlen memchr memset strchrnul strdup joined rec_calls_free rec_calls_equal
  check_words_add check_words_chain check_words_pin_set sup_reply_code check_reply_answer rec_shape_of
  rec_code_declared syntax_reply_matches SlotIter SlotProof HarnessPropsProof rec_calls_free_g rec_clear.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require FrameProof.
From OSSVerify.plugin_hostd.fuzz_command Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

(* The link of LLVMFuzzerTestOneInput (plain 0x14048): the callee contracts of SlotCallees.cmd_callees from the
   callee theorems, their frame facts from Slot.frame_given, and plain_halts from the frame, the slot and the
   harness properties. *)

(** * Kind A callees *)

Lemma strcspn_ok : strcspn_contract.
Proof. exact (lib.Prog.strcspn.strcspn_holds lib.Prog.memset.memset_holds lib.Prog.strchrnul.strchrnul_holds). Qed.

Lemma strnlen_ok : strnlen_contract.
Proof. exact (lib.Prog.strnlen.strnlen_holds lib.Prog.memchr.memchr_holds). Qed.

Lemma sup_reply_code_ok : sup_reply_code_contract.
Proof. exact (lib.Prog.sup_reply_code.sup_reply_code_holds lib.Prog.strncmp.strncmp_holds lib.Prog.atoi.atoi_holds). Qed.

Lemma check_refusal_ok : check_refusal_contract.
Proof. exact (lib.Prog.check_refusal.check_refusal_holds sup_reply_code_ok). Qed.

Lemma check_arity_ok : check_arity_contract.
Proof.
  exact (lib.Prog.check_arity.check_arity_holds lib.Prog.strcmp.strcmp_holds strcspn_ok
    lib.Prog.strncmp.strncmp_holds lib.Prog.bcmp.bcmp_holds).
Qed.

Lemma check_reply_answer_ok : check_reply_answer_contract.
Proof.
  exact (lib.Prog.check_reply_answer.check_reply_answer_holds lib.Prog.strcmp.strcmp_holds sup_reply_code_ok
    strcspn_ok lib.Prog.strncmp.strncmp_holds).
Qed.

Lemma rec_shape_of_ok : rec_shape_of_contract.
Proof. exact (lib.Prog.rec_shape_of.rec_shape_of_holds lib.Prog.strlen.strlen_holds lib.Prog.bcmp.bcmp_holds). Qed.

Lemma syntax_reply_matches_ok : syntax_reply_matches_contract.
Proof. exact (lib.Prog.syntax_reply_matches.syntax_reply_matches_holds strcspn_ok lib.Prog.bcmp.bcmp_holds). Qed.

Lemma check_reply_ok : check_reply_contract.
Proof.
  exact (lib.Prog.check_reply.check_reply_holds lib.Prog.memchr.memchr_holds check_reply_answer_ok sup_reply_code_ok
    lib.Prog.strlen.strlen_holds rec_shape_of_ok lib.Prog.snprintf.snprintf_holds
    lib.Prog.rec_code_declared.rec_code_declared_holds lib.Prog.strcmp.strcmp_holds syntax_reply_matches_ok).
Qed.

Lemma check_words_add_ok : check_words_add_contract.
Proof. exact (lib.Prog.check_words_add.check_words_add_holds lib.Prog.strcmp.strcmp_holds lib.Prog.strncmp.strncmp_holds). Qed.

Lemma check_words_chain_ok : check_words_chain_contract.
Proof.
  exact (lib.Prog.check_words_chain.check_words_chain_holds lib.Prog.atoi.atoi_holds lib.Prog.snprintf.snprintf_holds
    lib.Prog.strcmp.strcmp_holds).
Qed.

Lemma check_words_pin_set_ok : check_words_pin_set_contract.
Proof.
  exact (lib.Prog.check_words_pin_set.check_words_pin_set_holds lib.Prog.strncmp.strncmp_holds
    lib.Prog.strcmp.strcmp_holds).
Qed.

Lemma rec_calls_equal_ok : rec_calls_equal_contract.
Proof. exact (lib.Prog.rec_calls_equal.rec_calls_equal_holds lib.Prog.strcmp.strcmp_holds). Qed.

(** * Frame facts *)

Lemma errno_img : forall B, ms_segs B = rsegs -> ms_tp B = 0x341e0 -> ms_errno_off B = -164 ->
  in_img B (errno_addr B).
Proof.
  intros B S T E. unfold in_img, errno_addr. rewrite S, T, E.
  assert (NE : match rsegs with [] => false | _ :: _ => true end = true) by (vm_compute; reflexivity).
  assert (H : existsb (fun s => (bv_unsigned (fst s) <=? 0x341e0 + -164) &&
      (0x341e0 + -164 <? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in H as (s & Hs & Hb). cbv beta in Hb. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  split; [intros N; rewrite N in NE; discriminate NE | exists s; split; [exact Hs | lia]].
Qed.

(* The frame facts of frame_given at run ceiling rc and float state fx, in the forms of the callee Sections'
   hypotheses, and the Kind A contracts. *)
Ltac cl_setup FG B API rc fx :=
  let H := fresh "FG" in pose proof FG as H;
  destruct H as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 &
    F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31);
  destruct (F31 rc fx) as (MAL & FRE & FNU & REA & CAL & SLK & CTXO & BLO & BND & BWR & EUN & GRW & LNL & AX &
    GNO & RNO);
  pose proof (F6 rc) as ELOW;
  pose proof (fun fx' : FPState => proj1 (proj2 (F31 rc fx'))) as FREEA;
  pose proof (errno_img _ F0 F16 F17) as EIMG;
  assert (EGRD : errno_addr B + 4 <= SSP_GUARD_B \/ SSP_GUARD_B + 8 <= errno_addr B)
    by (left; unfold errno_addr, SSP_GUARD_B; rewrite F16, F17; lia);
  assert (RELF : forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_RELRO a ->
      ~ (ms_got_guard B <= a < ms_got_guard B + 8) -> ~ owned B L A a /\ ~ (errno_addr B <= a < errno_addr B + 4))
    by (intros L A mem md a HM Ha _; exact (conj (RNO L A mem md a HM Ha) (proj2 (proj2 (proj2 (F27 a Ha))))));
  pose proof lib.Prog.strcmp.strcmp_holds as K_SC;
  pose proof lib.Prog.strncmp.strncmp_holds as K_SNC;
  pose proof lib.Prog.atoi.atoi_holds as K_ATOI;
  pose proof lib.Prog.snprintf.snprintf_holds as K_SNP;
  pose proof lib.Prog.strlen.strlen_holds as K_SLEN;
  pose proof lib.Prog.memcpy.memcpy_holds as K_MCPY;
  pose proof lib.Prog.strspn.strspn_holds as K_SSP;
  pose proof strcspn_ok as K_SCS;
  pose proof check_words_add_ok as K_ADD;
  pose proof check_words_chain_ok as K_CHAIN;
  pose proof check_words_pin_set_ok as K_PIN;
  pose proof rec_calls_equal_ok as K_RCE.

(** * Kind B callees without open premises *)

Lemma strdup_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @strdup_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. cl_setup FG B API rc fx.
  eapply lib.Prog.strdup.strdup_holds; eassumption.
Qed.

Lemma joined_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @joined_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. cl_setup FG B API rc fx.
  eapply lib.Prog.joined.joined_holds; eassumption.
Qed.

Lemma rec_calls_free_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @rec_calls_free_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. cl_setup FG B API rc fx.
  eapply lib.Prog.rec_calls_free.rec_calls_free_holds; eassumption.
Qed.

Lemma check_words_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @check_words_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. pose proof (joined_of_given _ _ _ _ _ _ _ FG rc fx) as JOIN.
  cl_setup FG B API rc fx.
  eapply lib.Prog.check_words.check_words_holds; eassumption.
Qed.

Lemma rec_clear_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @rec_clear_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx.
  pose proof (lib.Prog.rec_calls_free_g.rec_calls_free_g_holds (fx := fx) (rc := rc) B (API rc)
    (rec_calls_free_of_given _ _ _ _ _ _ _ FG rc fx)) as RCFG.
  cl_setup FG B API rc fx.
  eapply lib.Prog.rec_clear.rec_clear_holds; eassumption.
Qed.

(** * The callees whose own callees are not proved here *)

Section Link.

Hypothesis ITER : SlotIter.iter_spec.

(* verbs_receive (verbs_receive_c.v) and rec_calls_copy (rec_calls_copy_c.v) at their contracts, for every frame
   of frame_given, run ceiling and float state. *)
Hypothesis HVRECV : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @verbs_receive_contract fx rc B (API rc).
Hypothesis HRCC : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @rec_calls_copy_contract fx rc B (API rc).

Lemma send_message_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @send_message_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx.
  pose proof (rec_clear_of_given _ _ _ _ _ _ _ FG rc fx) as RCLEAR. pose proof (HVRECV _ _ _ _ _ _ _ FG rc fx) as VRECV.
  cl_setup FG B API rc fx.
  eapply lib.Prog.send_message.send_message_holds; eassumption.
Qed.

Lemma check_round_trip_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @check_round_trip_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx.
  pose proof (HRCC _ _ _ _ _ _ _ FG rc fx) as RCC.
  pose proof (strdup_of_given _ _ _ _ _ _ _ FG rc fx) as SDUP.
  pose proof (joined_of_given _ _ _ _ _ _ _ FG rc fx) as JOIN.
  pose proof (send_message_of_given _ _ _ _ _ _ _ FG rc fx) as SEND.
  pose proof (rec_calls_free_of_given _ _ _ _ _ _ _ FG rc) as RCF.
  cl_setup FG B API rc fx.
  eapply lib.Prog.check_round_trip.check_round_trip_holds; eassumption.
Qed.

Lemma cmd_callees_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty -> cmd_callees B API.
Proof.
  intros B API LS SH SK ra empty FG. unfold cmd_callees.
  split; [exact (send_message_of_given _ _ _ _ _ _ _ FG)|].
  split; [exact (check_words_of_given _ _ _ _ _ _ _ FG)|].
  split; [exact (check_round_trip_of_given _ _ _ _ _ _ _ FG)|].
  split; [exact (rec_clear_of_given _ _ _ _ _ _ _ FG)|].
  split; [exact check_reply_ok|]. split; [exact check_arity_ok|]. split; [exact check_refusal_ok|].
  split; [exact strnlen_ok|]. split; [exact lib.Prog.memcpy.memcpy_holds|].
  split; [exact lib.Prog.strspn.strspn_holds | exact strcspn_ok].
Qed.

Theorem plain_halts_of_parts : Statements.plain_halts.
Proof.
  apply Slot.plain_halts_of_frame; [exact FrameProof.frame_plain_holds|].
  exact (SlotProof.fuzz_command_slot_holds ITER cmd_callees_of_given HarnessPropsProof.harness_props_holds).
Qed.

End Link.
