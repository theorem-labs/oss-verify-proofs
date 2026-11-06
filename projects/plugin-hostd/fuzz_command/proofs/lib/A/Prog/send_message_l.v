(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lemmas of send_message's own walk on plugin-hostd/fuzz_command's ASan image,
   ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v and A/ACk5.v at c8557374ad2e (cgif_close's frame-chain
   step and ng_chain): verbs_receive's allocator-event count is a count, the frame chain at the realigned stack
   pointer, and the stack bytes kept across the walk. The call rule for a callee that writes a program static and the
   transport lemmas its callers need (cl_callS_pg, ajournal_fp_widen, rec_repA_kept, aval_mem_kept_r ...) are the
   kit's, lib/A/Prog/PaCallPg.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaJournal CmdPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_clear_c verbs_receive_c send_message_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import send_message_k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
xstrdup_c hand_back_c answer_c answer_code_c arg_i_c arg_line_c rec_canonical_c pins_set_c socket_send_c
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c lv2_refusals_forget_c
pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* every allocator-event count of verbs_receive's routes is a count *)
Lemma rec_spill_frees_nonneg : forall R, 0 <= rec_spill_frees R.
Proof. intros R. unfold rec_spill_frees. destruct (Nat.ltb _ _); lia. Qed.
Ltac ev_unfold :=
unfold EV_SUP_ADD, EV_DESCRIPTORS_GET, EV_DESCRIPTORS_PANEL_GET, EV_SUP_REMOVE, EV_SUP_REMOVE_ALL,
EV_SUP_WORKER_LIST, EV_SUP_INSTANCE_INFO, EV_SUP_RESET, EV_SUP_QUARANTINE_CLEAR, EV_SUP_POLICY_SET,
EV_SUP_LV2_WORKER_SET, EV_SUP_POOL_CONFIG, EV_SUP_WORKER_ENV, EV_SUP_CHAIN, EV_SUP_CHAIN_CLEAR, EV_SUP_PIN_ACCEPT,
EV_SUP_INSTANCE_VERB, EV_SUP_CALL, EV_SUP_CONNECT, EV_SUP_RESP, EV_SUP_REPLY_CODE, EV_DESCRIPTORS_ADD, EV_PINS_CLEAR,
EV_LV2_REFUSALS_FORGET, EV_SUP_BROADCAST, EV_SUP_HOST_SETTING, EV_CHAIN_WORDS, EV_PIN_SET_WORDS, EV_REPLY,
EV_SUP_AFTER_REPLY, EV_PINS_SET, EV_ANSWER_CODE, EV_ANSWER, EV_HAND_BACK, EV_ARG_I, EV_ARG_LINE, EV_REC_CANONICAL,
EV_SOCKET_SEND, EV_XSTRDUP.
Ltac ev_spill_facts :=
repeat match goal with |- context [rec_spill_frees ?r] =>
lazymatch goal with _ : 0 <= rec_spill_frees r |- _ => fail | _ => pose proof (rec_spill_frees_nonneg r) end end.
Lemma ev_vr_nonneg : forall R D, 0 <= ev_vr R D.
Proof.
intros R D. unfold ev_vr.
destruct (Verbs.receive atoi_a D) as [st af].
destruct (VerbsRun.run_step reply_code_a R st) as [[R1 x] q].
unfold ev_route, ev_step, ev_call, ev_after.
ev_unfold; ev_unfold; ev_unfold.
repeat match goal with |- context [match ?e with _ => _ end] => destruct e end;
ev_spill_facts; lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* the frame chain at the realigned stack pointer, with the entry stack pointer in s0 (cgif A/ACk5.v ng_chain) *)
Lemma sm_achain : forall FP ly S W regs mem md ch fpos lyc Sc Wc memc mdc k,
afn_pre SEGS B SEND_MESSAGE_STK ly S W regs mem md ch ->
sm_jr B FP ly S W regs mem md fpos lyc Sc Wc memc mdc k ->
(forall a, alloc_ceiling <= a -> ~ inFP FP a) ->
sm_saved regs (mrestrict (w_H Wc) memc) ->
exists ch1, achain lyc (aview SEGS (w_H Wc) memc) (sm_sp1 (spZ regs)) (spZ regs) ch1.
Proof.
intros FP ly S W regs mem md ch fpos lyc Sc Wc memc mdc k HPRE (HJ & Hfrs) HFP HSV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : 112 <= SEND_MESSAGE_STK) by (vm_compute; discriminate).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
assert (Etop : ly_top lyc = ly_top ly).
{ pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _). exact E. }
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply F1; [lia | lia | apply HFP; lia]. }
destruct (Z_lt_ge_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
  unfold achain. rewrite Etop. fold (achain ly (aview SEGS (w_H Wc) memc) (sm_sp1 (spZ regs)) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch)).
  assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
  assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
  pose proof (HSV (-8) 1 ltac:(cbn; tauto)) as Vra. pose proof (HSV (-16) 8 ltac:(cbn; tauto)) as Vs0.
  replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia. replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia.
  assert (Qal8 : spZ regs mod 8 = 0).
  { pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
    replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia. apply Z_mod_mult. }
  assert (Qsp1 : sm_sp1 (spZ regs) + 16 <= spZ regs).
  { unfold sm_sp1. pose proof (Z.mul_div_le (spZ regs - 96) 32 ltac:(lia)). lia. }
  exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) ch (sm_sp1 (spZ regs)) Hch ltac:(lia) HUP
  (rdword_of_val_mem _ _ _ _ _ Vra Qra) (rdword_of_val_mem _ _ _ _ _ Vs0 Qs0) Hra4 ltac:(lia) Qal8 Hlt Qsp1).
- exists []. unfold achain. left. split; [|reflexivity]. right; left. rewrite Etop. lia.
Qed.
End e.
End f.
End d.
