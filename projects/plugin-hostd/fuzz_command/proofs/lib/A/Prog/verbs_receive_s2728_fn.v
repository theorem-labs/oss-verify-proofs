(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the functional facts the walk of segments S27 (INST) and S28 (CONNBROAD) of
   verbs_receive uses. Nothing here mentions a machine state: it is the model only (lib/Spec/Verbs.v,
   lib/Spec/VerbsRun.v, lib/Prog/RecModel.v, lib/Prog/verbs_receive_route.v) and the event and length constants of
   the ASan contracts. The proofs of vr_toks_inst / vr_toks_conn / vr_text_len are the plain proof's
   (lib/Prog/verbs_receive_br_inst.v:40-56, verbs_receive_br_conn.v:26-45), and the five length lemmas are
   lib/Prog/verbs_receive_br_broad.v:36-68 over hs_words_len; they are repeated here so that this file does not
   pull in the plain proof's machine-state files. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require CommandTac.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module VR2 := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* ------------------------------------------------------------------------------------------------------------
   The three routes behind the scan: the shape of their word list *)
Lemma vr_toks_inst : forall tk, VR2.route tk = VR2.RInst -> exists v a rest, tk = v :: a :: rest.
Proof.
intros [|v [|a rest]] H; [discriminate H| |exists v, a, rest; reflexivity].
exfalso. unfold VR2.route, VR2.route_mid, VR2.route_tail, VR2.route_conn in H.
repeat match type of H with context [if ?b then _ else _] => destruct b end; try discriminate H.
destruct (Verbs.ledger_of v Verbs.Lit.instance_info_verbs); discriminate H.
Qed.

Lemma vr_toks_conn : forall tk, VR2.route tk = VR2.RConn -> exists v a b, tk = [v; a; b].
Proof.
intros [|v args] H; [discriminate H|].
unfold VR2.route, VR2.route_mid, VR2.route_tail, VR2.route_conn, VR2.route_cd in H.
destruct (Verbs.ledger_of v Verbs.Lit.instance_info_verbs);
  [repeat match type of H with context [if ?b then _ else _] => destruct b end; discriminate H|].
destruct args as [|a [|b [|e r]]];
  repeat match type of H with context [if ?b then _ else _] => destruct b end; try discriminate H.
exists v, a, b. reflexivity.
Qed.

Lemma vr_toks_nonnil : forall tk, VR2.route tk = VR2.RBroad -> tk <> [] -> exists v args, tk = v :: args.
Proof. intros [|v args] _ H; [contradiction | exists v, args; reflexivity]. Qed.

(* the three tail routes are reached only when the first word is neither `chain` nor `pin_set`: the dispatch tests
   those before it scans (verbs_receive_route.v:38-40) *)
Lemma vr_tail_not_cp : forall v args,
VR2.route (v :: args) = VR2.RInst \/ VR2.route (v :: args) = VR2.RConn \/ VR2.route (v :: args) = VR2.RBroad ->
Verbs.list_eqb v Verbs.Lit.verb_chain = false /\ Verbs.list_eqb v Verbs.Lit.verb_pin_set = false.
Proof.
intros v args H. unfold VR2.route, VR2.route_mid in H.
repeat match type of H with context [if ?b then _ else _] => destruct b eqn:?; cbv iota in H end;
  try (exfalso; destruct H as [H|[H|H]]; discriminate H).
all: split; first [reflexivity | assumption].
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The step the dispatch takes on each of the three routes *)
Lemma vr_receive_at : forall D v args, Verbs.toks D = v :: args ->
Verbs.receive atoi_a D =
(VR2.plan_at (VR2.route (v :: args)) atoi_a (Verbs.line D) (v :: args), Verbs.after atoi_a (v :: args)).
Proof.
intros D v args HT. unfold Verbs.receive. rewrite HT.
rewrite (VR2.plan_route atoi_a (Verbs.line D) (v :: args) ltac:(discriminate)). reflexivity.
Qed.

Lemma vr_st_inst : forall D v a rest, Verbs.toks D = v :: a :: rest -> VR2.route (v :: a :: rest) = VR2.RInst ->
vr_st D = Verbs.SCall (Verbs.sup_call (atoi_a a) (Verbs.line D)).
Proof.
intros D v a rest HT HR. unfold vr_st. rewrite (vr_receive_at D v (a :: rest) HT). cbn [fst].
rewrite HR. reflexivity.
Qed.

Lemma vr_st_conn : forall D v a b, Verbs.toks D = [v; a; b] -> VR2.route [v; a; b] = VR2.RConn ->
vr_st D = Verbs.SCall (Verbs.sup_connect v (Verbs.line D) a b).
Proof.
intros D v a b HT HR. unfold vr_st. rewrite (vr_receive_at D v [a; b] HT). cbn [fst].
rewrite HR. reflexivity.
Qed.

Lemma vr_st_broad : forall D v args, Verbs.toks D = v :: args -> VR2.route (v :: args) = VR2.RBroad ->
vr_st D = Verbs.SBroadcast (Verbs.line D) (v :: args).
Proof.
intros D v args HT HR. unfold vr_st. rewrite (vr_receive_at D v args HT). cbn [fst].
rewrite HR. reflexivity.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The handler on a step: the recorder it leaves, the text and the quit flag *)
Lemma vr_h_call : forall R D c, vr_st D = Verbs.SCall c -> vr_h R D = (VerbsRun.run_call R c, false).
Proof. intros R D c H. unfold vr_h. rewrite H. reflexivity. Qed.

Lemma vr_R1_call : forall R D c, vr_st D = Verbs.SCall c -> vr_R1 R D = fst (VerbsRun.run_call R c).
Proof. intros R D c H. unfold vr_R1. rewrite (vr_h_call R D c H). reflexivity. Qed.

Lemma vr_x_call : forall R D c, vr_st D = Verbs.SCall c -> vr_x R D = snd (VerbsRun.run_call R c).
Proof. intros R D c H. unfold vr_x. rewrite (vr_h_call R D c H). reflexivity. Qed.

Lemma vr_quit_call : forall R D c, vr_st D = Verbs.SCall c -> vr_quit R D = false.
Proof. intros R D c H. unfold vr_quit. rewrite (vr_h_call R D c H). reflexivity. Qed.

Lemma vr_h_broad : forall R D ln tk, vr_st D = Verbs.SBroadcast ln tk ->
vr_h R D = (sup_host_setting_m (fst (sup_broadcast_m R ln)) ln tk, snd (sup_broadcast_m R ln), false).
Proof.
intros R D ln tk H. unfold vr_h. rewrite H. cbn [VerbsRun.run_step].
destruct (sup_broadcast_m R ln) as [R1 x]. reflexivity.
Qed.

Lemma vr_R1_broad : forall R D ln tk, vr_st D = Verbs.SBroadcast ln tk ->
vr_R1 R D = sup_host_setting_m (fst (sup_broadcast_m R ln)) ln tk.
Proof. intros R D ln tk H. unfold vr_R1. rewrite (vr_h_broad R D ln tk H). reflexivity. Qed.

Lemma vr_x_broad : forall R D ln tk, vr_st D = Verbs.SBroadcast ln tk ->
vr_x R D = snd (sup_broadcast_m R ln).
Proof. intros R D ln tk H. unfold vr_x. rewrite (vr_h_broad R D ln tk H). reflexivity. Qed.

Lemma vr_quit_broad : forall R D ln tk, vr_st D = Verbs.SBroadcast ln tk -> vr_quit R D = false.
Proof. intros R D ln tk H. unfold vr_quit. rewrite (vr_h_broad R D ln tk H). reflexivity. Qed.

(* ------------------------------------------------------------------------------------------------------------
   The events each of the three routes spends *)
Lemma vr_k1_at : forall R D v args, Verbs.toks D = v :: args ->
VR2.route (v :: args) = VR2.RInst \/ VR2.route (v :: args) = VR2.RConn \/ VR2.route (v :: args) = VR2.RBroad ->
vr_k1 R D = 2 + ev_step R (vr_st D).
Proof.
intros R D v args HT HR. unfold vr_k1, ev_route. rewrite HT.
destruct (vr_tail_not_cp v args HR) as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

Lemma vr_k1_inst : forall R D v a rest, Verbs.toks D = v :: a :: rest -> VR2.route (v :: a :: rest) = VR2.RInst ->
vr_k1 R D = 2 + EV_SUP_CALL R.
Proof.
intros R D v a rest HT HR. rewrite (vr_k1_at R D v (a :: rest) HT (or_introl HR)).
rewrite (vr_st_inst D v a rest HT HR). reflexivity.
Qed.

Lemma vr_k1_conn : forall R D v a b, Verbs.toks D = [v; a; b] -> VR2.route [v; a; b] = VR2.RConn ->
vr_k1 R D = 2 + EV_SUP_CONNECT R.
Proof.
intros R D v a b HT HR. rewrite (vr_k1_at R D v [a; b] HT (or_intror (or_introl HR))).
rewrite (vr_st_conn D v a b HT HR). reflexivity.
Qed.

Lemma vr_k1_broad : forall R D v args, Verbs.toks D = v :: args -> VR2.route (v :: args) = VR2.RBroad ->
vr_k1 R D = 2 + (EV_SUP_BROADCAST R + EV_SUP_HOST_SETTING (fst (sup_broadcast_m R (Verbs.line D)))).
Proof.
intros R D v args HT HR. rewrite (vr_k1_at R D v args HT (or_intror (or_intror HR))).
rewrite (vr_st_broad D v args HT HR). reflexivity.
Qed.

(* the routes behind route_conn are the three tail routes *)
Lemma vr_tail3 : forall v args, VR2.route (v :: args) = VR2.route_conn v args ->
VR2.route (v :: args) = VR2.RInst \/ VR2.route (v :: args) = VR2.RConn \/ VR2.route (v :: args) = VR2.RBroad.
Proof.
intros v args H. rewrite H. unfold VR2.route_conn, VR2.route_cd.
destruct args as [|a [|b [|d r]]]; try (right; right; reflexivity);
  repeat match goal with |- context [if ?x then _ else _] => destruct x end;
  first [left; reflexivity | right; left; reflexivity | right; right; reflexivity].
Qed.

Lemma vr_k1_ge2 : forall R D v args, Verbs.toks D = v :: args -> VR2.route (v :: args) = VR2.route_conn v args ->
2 <= vr_k1 R D.
Proof.
intros R D v args HT HR.
assert (Hs : forall R0, 0 <= rec_spill_frees R0) by (intros R0; unfold rec_spill_frees; destruct (Nat.ltb _ _); lia).
destruct (vr_tail3 v args HR) as [H | [H | H]].
- destruct (vr_toks_inst (v :: args) H) as (v' & a & rest & E). injection E as <- ->.
  rewrite (vr_k1_inst R D v a rest HT H). unfold EV_SUP_CALL, arg_i_c.EV_ARG_I, arg_line_c.EV_ARG_LINE,
    answer_c.EV_ANSWER, hand_back_c.EV_HAND_BACK, rec_canonical_c.EV_REC_CANONICAL, xstrdup_c.EV_XSTRDUP.
  pose proof (Hs R). lia.
- destruct (vr_toks_conn (v :: args) H) as (v' & a & b & E). injection E as <- ->.
  rewrite (vr_k1_conn R D v a b HT H). unfold EV_SUP_CONNECT, arg_line_c.EV_ARG_LINE,
    answer_c.EV_ANSWER, hand_back_c.EV_HAND_BACK, rec_canonical_c.EV_REC_CANONICAL, xstrdup_c.EV_XSTRDUP.
  pose proof (Hs R). lia.
- rewrite (vr_k1_broad R D v args HT H). unfold EV_SUP_BROADCAST, EV_SUP_HOST_SETTING, arg_i_c.EV_ARG_I,
    arg_line_c.EV_ARG_LINE, answer_c.EV_ANSWER, hand_back_c.EV_HAND_BACK, rec_canonical_c.EV_REC_CANONICAL,
    xstrdup_c.EV_XSTRDUP.
  pose proof (Hs R). pose proof (Hs (fst (sup_broadcast_m R (Verbs.line D)))). lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   Lengths: the wrapper's value is a 32-bit integer, a recorder answer is short, and the words of a line fit the
   line *)
Lemma vr_atoi_range : forall s, -2 ^ 31 <= atoi_a s < 2 ^ 31.
Proof.
intros s. unfold atoi_a, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
pose proof (Z.mod_pos_bound (__intscan_c.s10_val s + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma vr_text_len : forall R fn As ch, -2 ^ 31 <= r_code R < 2 ^ 31 ->
(length (snd (rec_stub R fn As REC_MOD_HOST_SHAPE ch)) <= 28)%nat.
Proof.
intros R fn As ch HC. unfold rec_stub. rewrite rec_answer_text.
assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
destruct (r_refuse (rec_record R fn As) =? 0).
- apply Nat.leb_le. vm_compute. reflexivity.
- rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.

Lemma vr_hs_cons : forall w ws, hs_words_len (w :: ws) = Z.of_nat (length w) + 1 + hs_words_len ws.
Proof. reflexivity. Qed.

Lemma vr_hs_nonneg : forall ws, 0 <= hs_words_len ws.
Proof. induction ws as [|w ws IH]; [cbv; discriminate|]. rewrite vr_hs_cons. lia. Qed.

Lemma vr_hs_words : forall l cur,
hs_words_len (Verbs.words_acc cur l) <= Z.of_nat (length cur) + Z.of_nat (length l) + 1.
Proof.
induction l as [|b l IH]; intros cur; cbn [Verbs.words_acc].
- destruct cur as [|x cur]; [cbv; discriminate|]. rewrite vr_hs_cons.
  change (hs_words_len []) with 0. cbn [length]. lia.
- destruct (Verbs.is_sep b); cbv iota.
  + destruct cur as [|x cur]; cbv iota.
    * pose proof (IH []) as H. cbn [length] in *. lia.
    * rewrite vr_hs_cons. pose proof (IH []) as H. cbn [length] in *. lia.
  + pose proof (IH (cur ++ [b])) as H. rewrite length_app in H. cbn [length] in *. lia.
Qed.

Lemma vr_hs_firstn : forall n ws, hs_words_len (firstn n ws) <= hs_words_len ws.
Proof.
induction n as [|n IH]; intros [|w ws]; cbn [firstn].
- lia.
- change (hs_words_len []) with 0. exact (vr_hs_nonneg (w :: ws)).
- lia.
- rewrite !vr_hs_cons. pose proof (IH ws). lia.
Qed.

Lemma vr_hs_toks : forall D, hs_words_len (Verbs.toks D) <= Z.of_nat (length (Verbs.line D)) + 1.
Proof.
intros D. unfold Verbs.toks, Verbs.words.
pose proof (vr_hs_firstn Verbs.line_words_max (Verbs.words_acc [] (Verbs.line D))) as H1.
pose proof (vr_hs_words (Verbs.line D) []) as H2. cbn [length] in *. lia.
Qed.

Lemma vr_join_len : forall ws, Z.of_nat (length (join_sp ws)) <= hs_words_len ws.
Proof.
induction ws as [|w ws IH]; [cbv; discriminate|]. rewrite vr_hs_cons.
destruct ws as [|w2 ws'].
- change (join_sp [w]) with w. change (hs_words_len []) with 0. lia.
- change (join_sp (w :: w2 :: ws')) with (w ++ SPACE :: join_sp (w2 :: ws')).
  rewrite length_app. cbn [length]. lia.
Qed.

(* every word of a line is at most as long as the line *)
Lemma vr_tok_len : forall D w, In w (Verbs.toks D) -> (length w <= length (Verbs.line D))%nat.
Proof.
intros D w H. apply Verbs.toks_in in H. unfold Verbs.words in H.
pose proof (VR2.words_acc_len (Verbs.line D) [] w H) as L. cbn [length] in L. lia.
Qed.

(* the trimmed line fits the bytes strndup copied: |line D| <= strnlen_res |D| D (the proof of find_byte_upto0 is
   the plain proof's, lib/Prog/verbs_receive_pre.v:61-66) *)
Lemma vr_find_byte_upto0 : forall D,
match StrFun.find_byte 0 D with Some i => firstn i D | None => D end = Verbs.upto0 D.
Proof.
unfold Verbs.upto0. induction D as [|x D IH]; [reflexivity|]. cbn [StrFun.find_byte Verbs.upto].
destruct (bv_unsigned x =? 0); [reflexivity|].
destruct (StrFun.find_byte 0 D) as [i|]; cbn [firstn]; f_equal; exact IH.
Qed.

Lemma vr_l_ge_upto0 : forall D, Z.of_nat (length (Verbs.upto0 D)) <= StrFun.strnlen_res (Z.of_nat (length D)) D.
Proof.
intros D. pose proof (vr_find_byte_upto0 D) as E. unfold StrFun.strnlen_res. rewrite Nat2Z.id, firstn_all.
destruct (StrFun.find_byte 0 D) as [i|]; rewrite <- E; [rewrite length_firstn; lia | lia].
Qed.

Lemma vr_line_le_l : forall n D, Z.of_nat (length D) = n -> Z.of_nat (length (Verbs.line D)) <= vr_l n D.
Proof.
intros n D Hn. unfold vr_l. subst n. pose proof (vr_l_ge_upto0 D) as H1.
unfold Verbs.line, Verbs.trim. rewrite length_rev.
pose proof (VR2.dropw_len Verbs.is_trail (rev (Verbs.upto0 D))) as H2. rewrite length_rev in H2. lia.
Qed.
