(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: lemmas the segments of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B) share, the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s01.v: the live bytes the recorder owns, the payload bytes and the read-only bytes kept along the walk's journal, the events and meter left (non-negative; each callee's meter at most its events times one unit), the joined size of a message's words (words_acc_need copied from fuzz_command's plain lib/Prog/SlotRec.v); in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh7.v and ACh8.v (the keep lemmas of cgif_close's segments). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdPaLib
  CmdBase CmdRep CmdObj CmdRo CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import HarnessArgs HarnessArgsEv
chain_words_c descriptors_add_c lv2_refusals_forget_c pin_set_words_c pins_clear_c pins_set_c reply_c socket_send_c
sup_add_c sup_after_reply_c sup_broadcast_c sup_host_setting_c sup_reply_code_c sup_resp_c xmalloc_c joined_c
rec_calls_copy_c rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---- the events left are never negative (the same unfolding as HarnessArgsEv.v's upper bounds) ---- *)
Lemma ev_args_nonneg : forall R, 0 <= ev_args R.
Proof. intros R. unfold ev_args. induction (r_calls R) as [|c cs IH]; cbn [fold_right]; lia. Qed.
Lemma ev_step_ge0 : forall R s, 0 <= ev_step (RecModel.rec_clear R) s.
Proof.
  intros R s. destruct s as [c0|c|u i p q|u f l v|u| |ln tk]; [|destruct c|..];
    ev_unfold; rec_unfold; cbn; ifs; lia.
Qed.
Lemma ev_route_ge0 : forall R ln tk s, 0 <= ev_route (RecModel.rec_clear R) ln tk s.
Proof.
  intros R ln tk s. pose proof (ev_step_ge0 R s) as Hs. unfold ev_route.
  destruct tk as [|v args]; [ev_unfold; lia|].
  match goal with |- context [if Verbs.list_eqb v ?w then _ else _] => destruct (Verbs.list_eqb v w) end;
    [ev_unfold; cbn; lia|].
  match goal with |- context [if Verbs.list_eqb v ?w then _ else _] => destruct (Verbs.list_eqb v w) end;
    [|lia].
  unfold EV_PIN_SET_WORDS. destruct (Verbs.pin_set_words_m ln args); try (ev_unfold; lia).
  ev_unfold; rec_unfold; cbn; ifs; lia.
Qed.
Lemma ev_after_ge0 : forall R2 af, 0 <= ev_after R2 af.
Proof.
  intros R2 af. destruct af as [p|]; ev_unfold; [|lia].
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.
Lemma ev_vr_ge0 : forall R D, 0 <= ev_vr (RecModel.rec_clear R) D.
Proof.
  intros R D. unfold ev_vr. destruct (Verbs.receive _ D) as [st af].
  pose proof (ev_route_ge0 R (Verbs.line D) (Verbs.toks D) st) as Hr.
  destruct (VerbsRun.run_step _ (RecModel.rec_clear R) st) as [[R1 x] q].
  match goal with |- context [ev_after ?R2 af] => pose proof (ev_after_ge0 R2 af) end.
  unfold EV_REPLY, EV_SOCKET_SEND, EV_XMALLOC. lia.
Qed.
Lemma EV_SEND_MESSAGE_ge0 : forall R D, 0 <= EV_SEND_MESSAGE R D.
Proof. intros R D. unfold EV_SEND_MESSAGE, EV_REC_CLEAR. pose proof (ev_args_nonneg R). pose proof (ev_vr_ge0 R D). lia. Qed.
Lemma EV_REC_CLEAR_ge0 : forall R, 0 <= EV_REC_CLEAR R.
Proof. intros R. unfold EV_REC_CLEAR. pose proof (ev_args_nonneg R). lia. Qed.
Lemma EV_CHECK_ROUND_TRIP_ge0 : forall R ws, 0 <= EV_CHECK_ROUND_TRIP R ws.
Proof.
  intros R ws. unfold EV_CHECK_ROUND_TRIP.
  match goal with |- context [EV_SEND_MESSAGE R ?D] => pose proof (EV_SEND_MESSAGE_ge0 R D) end.
  unfold EV_REC_CALLS_COPY, EV_XMALLOC, EV_JOINED. pose proof (ev_args_nonneg R). lia.
Qed.
Lemma lt_cost_ge0 : forall R0 D R1 ws, 0 <= lt_cost R0 D R1 ws.
Proof.
  intros R0 D R1 ws. unfold lt_cost. pose proof (EV_SEND_MESSAGE_ge0 R0 D). pose proof (EV_CHECK_ROUND_TRIP_ge0 R1 ws).
  unfold EV_CHECK_REPLY, EV_CHECK_ARITY, EV_CHECK_WORDS, EV_CHECK_REFUSAL, EV_JOINED, EV_SUP_REPLY_CODE. lia.
Qed.
Lemma ev_msgs_ge0 : forall f R l, 0 <= fst (ev_msgs f R l).
Proof.
  induction f as [|f IH]; intros R l; [cbn; lia|]. destruct l as [|b l]; [cbn; lia|]. cbn [ev_msgs].
  match goal with |- context [ev_msgs f ?R1 ?l1] => pose proof (IH R1 l1) as Hk; destruct (ev_msgs f R1 l1) as [k Rf] end.
  cbn [fst] in *.
  match goal with |- context [EV_SEND_MESSAGE ?a ?b] => pose proof (EV_SEND_MESSAGE_ge0 a b) end.
  match goal with |- context [EV_CHECK_ROUND_TRIP ?a ?b] => pose proof (EV_CHECK_ROUND_TRIP_ge0 a b) end.
  unfold EV_CHECK_REPLY, EV_CHECK_ARITY, EV_CHECK_WORDS, EV_CHECK_REFUSAL, EV_JOINED, EV_SUP_REPLY_CODE. lia.
Qed.
Lemma ev_from_nonneg : forall f R l, 0 <= ev_from f R l.
Proof. intros f R l. unfold ev_from. pose proof (ev_msgs_ge0 f R l). pose proof (EV_REC_CLEAR_ge0 (snd (ev_msgs f R l))). lia. Qed.
Lemma join_need_ge0 : forall ws, 0 <= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.joined_c.join_need ws.
Proof.
  intros ws. unfold OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.joined_c.join_need.
  induction ws as [|w ws IH]; cbn [fold_right]; lia.
Qed.
Local Notation JN := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.joined_c.join_need.
Local Notation RCC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_copy_c.rcc_args.
(* the arguments rec_calls_copy copies are ev_args many *)
Lemma rcc_len : forall R, Z.of_nat (length (RCC (r_calls R))) = ev_args R.
Proof.
  intros R. unfold ev_args, OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_copy_c.rcc_args.
  induction (r_calls R) as [|c cs IH]; cbn [concat map fold_right length]; [reflexivity|].
  rewrite length_app, Nat2Z.inj_add, IH. reflexivity.
Qed.
(* the words of a message need at most 8193 bytes once joined (fuzz_command's plain lib/Prog/SlotRec.v:600-615,
   words_acc_need / join_need_words, and the line is no longer than the message) *)
Lemma words_acc_need_loc : forall l cur,
  JN (Verbs.words_acc cur l) <= Z.of_nat (length l) + 1 + Z.of_nat (length cur).
Proof.
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.joined_c.join_need.
  induction l as [|b l IH]; intros cur.
  - destruct cur as [|c cur]; cbn [Verbs.words_acc fold_right]; lia.
  - cbn [Verbs.words_acc]. destruct (Verbs.is_sep b).
    + specialize (IH []). destruct cur as [|c cur]; cbn [fold_right length] in IH |- *; lia.
    + specialize (IH (cur ++ [b])). rewrite length_app in IH. cbn [length] in IH |- *. lia.
Qed.
Lemma upto_len : forall p l, (length (Verbs.upto p l) <= length l)%nat.
Proof. intros p. induction l as [|b l IH]; cbn [Verbs.upto length]; [lia|]. destruct (p b); cbn [length]; lia. Qed.
Lemma dropw_len : forall p l, (length (Verbs.dropw p l) <= length l)%nat.
Proof. intros p. induction l as [|b l IH]; cbn [Verbs.dropw length]; [lia|]. destruct (p b); cbn [length]; lia. Qed.
Lemma line_len_loc : forall D, (length (Verbs.line D) <= length D)%nat.
Proof.
  intros D. unfold Verbs.line, Verbs.trim, Verbs.upto0. rewrite length_rev.
  pose proof (dropw_len Verbs.is_trail (rev (Verbs.upto (fun b => bv_unsigned b =? 0) D))) as H1.
  rewrite length_rev in H1. pose proof (upto_len (fun b => bv_unsigned b =? 0) D) as H2. lia.
Qed.
Lemma lt_ws_join_need : forall pl n r, 0 < r -> JN (lt_ws pl n r) + 1 <= 32784.
Proof.
  intros pl n r Hr. unfold lt_ws, HarnessProps.hwords, Verbs.words.
  pose proof (words_acc_need_loc (Verbs.line (lt_D pl n r)) []) as H. cbn [length] in H.
  pose proof (line_len_loc (lt_D pl n r)) as H1.
  assert (H2 : (length (lt_D pl n r) <= Z.to_nat (lt_len pl n r))%nat) by (unfold lt_D; rewrite length_firstn; lia).
  pose proof (lt_len_range pl n r Hr) as H3.
  assert (H4 : lt_len pl n r <= 8192) by (unfold lt_len, SlotSpec.msg_len; lia).
  lia.
Qed.

(* ---- sums of block sizes ---- *)
Lemma bsum_le : forall l, (forall x, In x l -> snd x <= LMAX + 2) -> bsum l <= Z.of_nat (length l) * (LMAX + 2).
Proof.
induction l as [|x l IH]; intros H; cbn [bsum length]; [unfold LMAX; lia|].
pose proof (H x (or_introl eq_refl)) as Hx. pose proof (IH (fun y Hy => H y (or_intror Hy))) as Hl.
rewrite Nat2Z.inj_succ. unfold LMAX in *. lia.
Qed.
Lemma bsum_nonneg : forall l, (forall x, In x l -> 0 <= snd x) -> 0 <= bsum l.
Proof.
induction l as [|x l IH]; intros H; cbn [bsum]; [lia|].
pose proof (H x (or_introl eq_refl)). pose proof (IH (fun y Hy => H y (or_intror Hy))). lia.
Qed.
Lemma length_concat_le : forall (L : list (list (Z * Z))) k,
  (forall P, In P L -> (length P <= k)%nat) -> (length (concat L) <= length L * k)%nat.
Proof.
induction L as [|P L IH]; intros k H; cbn [concat length]; [lia|].
rewrite length_app. pose proof (H P (or_introl eq_refl)). pose proof (IH k (fun Q HQ => H Q (or_intror HQ))). lia.
Qed.

(* ---- a list of pairwise disjoint non-empty ranges has no repetition ---- *)
Lemma pairwise_zdisjoint_NoDup : forall l, (forall x, In x l -> 0 < snd x) -> pairwise zdisjoint l -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hd; [constructor|]. destruct Hd as [Hx Hl]. constructor.
- intros Hin. rewrite Forall_forall in Hx. specialize (Hx x Hin). pose proof (Hp x (or_introl eq_refl)).
  unfold zdisjoint in Hx. lia.
- apply IH; [intros y Hy; exact (Hp y (or_intror Hy)) | exact Hl].
Qed.

(* ---- the recorder's own blocks: at most 14 (2 calls of 6 arguments, the answer, the reply), each at most LMAX + 2
   bytes (RecInv.v's bound, through CmdRep.v's arep_at) ---- *)
Lemma lt_lay_facts : forall bl rd gr sc R Q,
  arep_at bl rd gr sc R Q -> (length (r_calls R) <= 2)%nat -> r_spill R = (0, []) ->
  (length (lay_blocks Q) <= 14)%nat /\ (forall pn, In pn (lay_blocks Q) -> 1 <= snd pn <= LMAX + 2).
Proof.
intros bl rd gr sc R Q HA H2 Hsp.
destruct HA as (_ & _ & _ & (_ & Hlen & _ & Hcalls & Hspill & _) & Hans & Hrep & _ & _).
assert (Hsp0 : l_spill Q = []).
{ destruct Hspill as (_ & _ & HL & _). rewrite Hsp in HL. cbn in HL. destruct (l_spill Q); [reflexivity | discriminate]. }
assert (HC : forall P, In P (l_calls Q) ->
  (length P <= 6)%nat /\ forall pn, In pn P -> 1 <= snd pn <= LMAX + 2).
{ intros P HP. apply In_nth_error in HP as (i & Hi).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
  2: { apply nth_error_None in Hc. assert (i < length (l_calls Q))%nat by (apply nth_error_Some; congruence). lia. }
  destruct (Hcalls i c P Hc Hi) as [(_ & H6 & HPl & _ & _ & _ & HK) _].
  split; [lia|]. intros pn Hpn. apply In_nth_error in Hpn as (k & Hk).
  destruct (nth_error (snd c) k) as [s|] eqn:Hs.
  2: { apply nth_error_None in Hs. assert (k < length P)%nat by (apply nth_error_Some; congruence). lia. }
  destruct (HK k s pn Hs Hk) as (_ & _ & _ & Hb & _). lia. }
split.
- unfold lay_blocks. rewrite Hsp0. rewrite !length_app. cbn [length].
  pose proof (length_concat_le (l_calls Q) 6 (fun P HP => proj1 (HC P HP))) as Hcc.
  assert (Ha : (length (oblk (l_answer Q)) <= 1)%nat) by (destruct (l_answer Q); cbn; lia).
  assert (Hr : (length (oblk (l_reply Q)) <= 1)%nat) by (destruct (l_reply Q); cbn; lia).
  lia.
- intros pn Hpn. unfold lay_blocks in Hpn. rewrite Hsp0 in Hpn.
  apply in_app_or in Hpn as [Hpn | Hpn].
  + apply in_concat in Hpn as (P & HP & Hin). exact (proj2 (HC P HP) pn Hin).
  + cbn [app] in Hpn. apply in_app_or in Hpn as [Hpn | Hpn].
    * unfold aanswer_at in Hans. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [pa|]; try contradiction;
        cbn [oblk In] in Hpn; try (destruct Hpn; fail).
      destruct Hpn as [<- | []]. destruct Hans as (_ & _ & _ & Hb & _). lia.
    * unfold areply_at in Hrep. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [pa|]; try contradiction;
        cbn [oblk In] in Hpn; try (destruct Hpn; fail).
      destruct Hpn as [<- | []]. destruct Hrep as (_ & _ & _ & Hne & _ & Hb & _).
      destruct x as [|b x]; [congruence|]. cbn [length] in Hb. lia.
Qed.

Lemma lt_rec_bsum : forall B ly S rd R O,
  rec_repA B ly S rd R O -> (length (r_calls R) <= 2)%nat -> r_spill R = (0, []) -> List.NoDup O ->
  0 <= bsum O <= LT_RECB.
Proof.
intros B ly S rd R O (Q & HA & HO) H2 Hsp HND.
destruct (lt_lay_facts _ _ _ _ _ _ HA H2 Hsp) as [HL HB].
assert (Hin : forall pn, In pn O -> 1 <= snd pn <= LMAX + 2) by (intros pn Hpn; exact (HB pn (proj1 (HO pn) Hpn))).
assert (Hinc : (length O <= length (lay_blocks Q))%nat).
{ apply NoDup_incl_length; [exact HND|]. intros pn Hpn. exact (proj1 (HO pn) Hpn). }
assert (Hlen : (length O <= 14)%nat) by lia.
split; [apply bsum_nonneg; intros x Hx; pose proof (Hin x Hx); lia|].
pose proof (bsum_le O (fun x Hx => proj2 (Hin x Hx))) as Hs. unfold LT_RECB, LMAX in *. lia.
Qed.

Lemma NoDup_app_l_loc : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 H; [constructor|].
cbn [app] in H. apply NoDup_cons_iff in H as [Hn Hd]. constructor.
- intros Hin. apply Hn, in_or_app. left. exact Hin.
- exact (IH l2 Hd).
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.

(* ---- each callee's meter is at most its events times LT_U (pass 3's per-event meter): the meter step of a call ---- *)
Lemma mo_malloc_le_U : forall a, 0 <= a <= 32784 -> 0 <= mo_malloc MT a <= mo_malloc MT 32784.
Proof. intros a Ha. split; [apply (mo_malloc_nonneg MT MTL); lia | apply (mo_malloc_mono MT MTL); lia]. Qed.
Lemma LT_U_nonneg : 0 <= LT_U MT.
Proof. unfold LT_U. pose proof (mo_malloc_le_U 32784 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. Qed.
Lemma xm_rec_clear_le : forall R, XM_REC_CLEAR MT R <= EV_REC_CLEAR R * LT_U MT.
Proof.
intros R. unfold XM_REC_CLEAR, EV_REC_CLEAR, LT_U. pose proof (ev_args_nonneg R).
pose proof (mo_free_nonneg MT MTL). pose proof (mo_malloc_le_U 32784 ltac:(lia)).
apply Z.mul_le_mono_nonneg_l; lia.
Qed.
Lemma xm_verbs_receive_le : forall R D,
  XM_VERBS_RECEIVE MT (RecModel.rec_clear R) D <= ev_vr (RecModel.rec_clear R) D * LT_U MT.
Proof.
intros R D. unfold XM_VERBS_RECEIVE, LT_U, VERBS_RECEIVE_REQ. pose proof (ev_vr_ge0 R D).
pose proof (mo_malloc_le_U 8194 ltac:(lia)). apply Z.mul_le_mono_nonneg_l; lia.
Qed.
Lemma xm_send_message_le : forall R D, XM_SEND_MESSAGE MT R D <= EV_SEND_MESSAGE R D * LT_U MT.
Proof.
intros R D. unfold XM_SEND_MESSAGE, EV_SEND_MESSAGE.
pose proof (xm_rec_clear_le R) as H1. pose proof (xm_verbs_receive_le R D) as H2.
assert (H3 : mo_malloc MT 8192 + mo_free MT <= 2 * LT_U MT).
{ unfold LT_U. pose proof (mo_malloc_le_U 8192 ltac:(lia)). pose proof (mo_malloc_le_U 32784 ltac:(lia)).
  pose proof (mo_free_nonneg MT MTL). lia. }
rewrite !Z.mul_add_distr_r.
set (a := EV_REC_CLEAR R * LT_U MT) in *. set (b := ev_vr (RecModel.rec_clear R) D * LT_U MT) in *. lia.
Qed.
Lemma xm_check_words_le : forall ws, JN ws + 1 <= 32784 -> XM_CHECK_WORDS MT ws <= EV_CHECK_WORDS * LT_U MT.
Proof.
intros ws Hj. unfold XM_CHECK_WORDS, XM_JOINED, EV_CHECK_WORDS, EV_JOINED, LT_U.
pose proof (join_need_ge0 ws). pose proof (mo_malloc_le_U (JN ws + 1) ltac:(lia)).
pose proof (mo_malloc_le_U 32784 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia.
Qed.
(* B's rec_calls_copy copies each argument by xmalloc (malloc(n ? n : 1), lib/B/Prog/xmalloc_c.v) *)
Lemma xm_xmallocs_le : forall xs : list (list byte), Forall (fun x => Z.of_nat (length x) + 1 <= 32784) xs ->
  fold_right (fun x acc => XM_XMALLOC MT (Z.of_nat (length x) + 1) + acc) 0 xs <=
  Z.of_nat (length xs) * mo_malloc MT 32784.
Proof.
induction xs as [|x xs IH]; intros H; cbn [fold_right length]; [lia|].
apply Forall_cons_iff in H as [Hx Hxs]. cbv beta in Hx. pose proof (IH Hxs). unfold XM_XMALLOC, LIVE_XMALLOC in *.
pose proof (mo_malloc_le_U (Z.max (Z.of_nat (length x) + 1) 1) ltac:(lia)). rewrite Nat2Z.inj_succ, Z.mul_succ_l.
set (t := Z.of_nat (length xs) * mo_malloc MT 32784) in *. lia.
Qed.
Lemma xm_check_round_trip_le : forall R ws, JN ws + 1 <= 32784 ->
  Forall (fun x => Z.of_nat (length x) + 1 <= 32784) (RCC (r_calls R)) ->
  XM_CHECK_ROUND_TRIP MT R ws <= EV_CHECK_ROUND_TRIP R ws * LT_U MT.
Proof.
intros R ws Hj Ha. unfold XM_CHECK_ROUND_TRIP, EV_CHECK_ROUND_TRIP.
match goal with |- context [XM_SEND_MESSAGE MT R ?D] => pose proof (xm_send_message_le R D) as H4 end.
pose proof LT_U_nonneg as HU. pose proof (ev_args_nonneg R) as Hea.
assert (HF : mo_free MT <= LT_U MT) by (unfold LT_U; pose proof (mo_malloc_le_U 32784 ltac:(lia)); lia).
assert (HA : XM_REC_CALLS_COPY MT R <= EV_REC_CALLS_COPY R * LT_U MT).
{ unfold XM_REC_CALLS_COPY, EV_REC_CALLS_COPY, EV_XMALLOC. pose proof (xm_xmallocs_le _ Ha) as H1. rewrite rcc_len in H1.
  assert (H2 : ev_args R * mo_malloc MT 32784 <= ev_args R * LT_U MT).
  { apply Z.mul_le_mono_nonneg_l; [exact Hea|]. unfold LT_U. pose proof (mo_free_nonneg MT MTL). lia. }
  rewrite Z.mul_1_l. set (t1 := ev_args R * mo_malloc MT 32784) in *. set (t2 := ev_args R * LT_U MT) in *. lia. }
assert (HJ : XM_JOINED MT ws <= LT_U MT).
{ unfold XM_JOINED, LT_U. pose proof (join_need_ge0 ws). pose proof (mo_malloc_le_U (JN ws + 1) ltac:(lia)).
  pose proof (mo_malloc_le_U 32784 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
assert (HL : mo_malloc MT (LMAX + 2) <= LT_U MT).
{ unfold LT_U. pose proof (mo_malloc_le_U (LMAX + 2) ltac:(unfold LMAX; lia)). pose proof (mo_malloc_le_U 32784 ltac:(lia)).
  pose proof (mo_free_nonneg MT MTL). lia. }
assert (HE : ev_args R * mo_free MT <= ev_args R * LT_U MT) by (apply Z.mul_le_mono_nonneg_l; [exact Hea | exact HF]).
unfold EV_JOINED. rewrite !Z.mul_add_distr_r.
set (u := LT_U MT) in *. set (a1 := EV_REC_CALLS_COPY R * u) in *.
match goal with H : XM_SEND_MESSAGE MT R ?D <= ?e * u |- _ => set (a2 := e * u) in * end.
set (a3 := ev_args R * u) in *. set (a4 := ev_args R * mo_free MT) in *.
lia.
Qed.

(* the live blocks never repeat *)
Lemma lt_ablocks_NoDup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p0 n0] bl] eqn:Eb; [constructor|].
assert (Hin0 : In (p0, n0) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite <- Eb. apply (NoDup_map_inv (fun b : Z * Z => (fst b, req_size (snd b)))).
apply pairwise_zdisjoint_NoDup; [|exact Hpw].
intros [a q] Hx. apply in_map_iff in Hx as ([pb nb] & Hq & Hpb). cbn in Hq. injection Hq as <- <-.
destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hpb) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. pose proof (req_size_pos nb ltac:(lia)). lia.
Qed.

(* the live bytes at a point of the top loop: the entry's, the recorder's (at most LT_RECB) and the extra blocks *)
Lemma lt_rec_live : forall cx ly S (W : world SEGS) mem md R O q extra,
  AR SEGS B ly S W mem md -> lt_rec B cx ly S W mem R O q extra ->
  blocks_bytes S <= blocks_bytes (x_S cx) + LT_RECB + bsum extra.
Proof.
intros cx ly S W mem md R O q extra HAR (HR & Hsp & H2 & _ & _ & HP).
pose proof (lt_ablocks_NoDup ly S W mem md HAR) as HND.
pose proof (Permutation_NoDup HP HND) as HND2. apply NoDup_app_l_loc in HND2.
destruct (lt_rec_bsum B ly S _ R O HR H2 Hsp HND2) as [_ HO].
rewrite (blocks_bytes_ablocks B ly S), (blocks_bytes_ablocks B (x_ly cx) (x_S cx)), (bsum_perm _ _ HP).
unfold x_bl0. rewrite !bsum_app. lia.
Qed.

(* the payload's bytes are kept along the journal from the entry while its block is live: its block is off the
   image (CmdPaLib.v blk_off_imgP), cmd_PG is inside it *)
Lemma lt_payload_kept : forall cx ly S (W : world SEGS) mem md own k,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) own ly S W mem md k ->
  (0 < x_n cx -> In (x_p cx, x_n cx) (ablocks B ly S)) ->
  forall i, 0 <= i < x_n cx -> rdW W mem (x_p cx + i) = rdW (x_W cx) (x_mem cx) (x_p cx + i).
Proof.
intros cx ly S W mem md own k HB HJ Hin i Hi.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & Hpn & _).
destruct Hpn as [[Hn0 _] | [Hn Hin0]]; [lia|].
pose proof (Hin ltac:(lia)) as Hin1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hrq].
apply (F2 (x_p cx) (x_n cx) i Hin0 Hin1); [lia|].
pose proof (blk_off_imgP B _ _ _ _ _ _ _ (proj1 HPRE) Hin0) as Hoff.
intros (r & Hr & Hlo & Hhi). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. unfold off_img in Hoff.
cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi; lia.
Qed.

(* ---- the read-only bytes at a later point: the journal from the entry keeps every image byte outside cmd_PG that
   is not owned and not the errno cell (its image clause), and read-only bytes are such bytes ---- *)
Section ro.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Lemma cmd_PG_no_sink : ~ YI16.sink_open_fp cmd_PG.
Proof.
intros (r & Hr & Hlo & Hhi). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi; lia.
Qed.
Lemma lt_arodata_kept : forall cx ly S (W : world SEGS) mem md own k,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) own ly S W mem md k ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem).
Proof.
intros cx ly S W mem md own k HB0 HJ a Hro Ho He.
pose proof HB0 as (_ & HR0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img SEGS a).
{ destruct Hro as [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (RRO SEGS B LAWS HB IMG a Hg)]. }
rewrite (F3 a Himg Ho He); [exact (HR0 a Hro Ho He)|].
apply fp_spares_closed; [exact cmd_PG_no_sink|]. intros Hin. exact (RPG SEGS B LAWS HB IMG a Hin Hro).
Qed.
Lemma lt_ro_kept : forall cx ly S (W : world SEGS) mem md own k,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) own ly S W mem md k ->
  cmd_ro_ok (rdW W mem).
Proof.
intros cx ly S W mem md own k HB0 HJ.
exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly S W mem md (proj1 HJ) (lt_arodata_kept cx ly S W mem md own k HB0 HJ)).
Qed.
End ro.

End e.
End f.
End d.
