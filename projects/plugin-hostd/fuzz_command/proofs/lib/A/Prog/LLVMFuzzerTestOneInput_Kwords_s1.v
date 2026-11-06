(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the local facts of the check_words step of segment K of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86950 .. jal check_words at 0x86954): the event counts the budget's rest holds are counts (from the send_message walk, ev_vr_nonneg), distinct live blocks (nodup_blocks), the recorder's blocks between two messages are at most 14 of at most LMAX + 2 bytes (LT_RECB), a frame word read as an 8-byte field, and the symbolic state at 0x86950 with no region (cgif A/ACh6.v cl_seedX's form). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
xstrdup_c hand_back_c answer_c answer_code_c arg_i_c arg_line_c rec_canonical_c pins_set_c socket_send_c
rec_calls_copy_c chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c lv2_refusals_forget_c
pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c
sup_lv2_worker_set_c sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c
sup_remove_all_c sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the event counts are counts (the send_message walk, earlier versions of send_message_l.v / send_message_s1.v:
   rec_spill_frees_nonneg, ev_vr_nonneg, ev_args_nonneg) ---- *)
Lemma rec_spill_frees_nonneg_loc : forall R, 0 <= rec_spill_frees R.
Proof. intros R. unfold rec_spill_frees. destruct (Nat.ltb _ _); lia. Qed.
Lemma ev_args_nonneg_loc : forall R, 0 <= ev_args R.
Proof. intros R. unfold ev_args. induction (r_calls R) as [|c l IH]; cbn [fold_right]; lia. Qed.
Ltac kw_ev_unfold :=
unfold EV_SUP_ADD, EV_DESCRIPTORS_GET, EV_DESCRIPTORS_PANEL_GET, EV_SUP_REMOVE, EV_SUP_REMOVE_ALL,
EV_SUP_WORKER_LIST, EV_SUP_INSTANCE_INFO, EV_SUP_RESET, EV_SUP_QUARANTINE_CLEAR, EV_SUP_POLICY_SET,
EV_SUP_LV2_WORKER_SET, EV_SUP_POOL_CONFIG, EV_SUP_WORKER_ENV, EV_SUP_CHAIN, EV_SUP_CHAIN_CLEAR, EV_SUP_PIN_ACCEPT,
EV_SUP_INSTANCE_VERB, EV_SUP_CALL, EV_SUP_CONNECT, EV_SUP_RESP, EV_SUP_REPLY_CODE, EV_DESCRIPTORS_ADD, EV_PINS_CLEAR,
EV_LV2_REFUSALS_FORGET, EV_SUP_BROADCAST, EV_SUP_HOST_SETTING, EV_CHAIN_WORDS, EV_PIN_SET_WORDS, EV_REPLY,
EV_SUP_AFTER_REPLY, EV_PINS_SET, EV_ANSWER_CODE, EV_ANSWER, EV_HAND_BACK, EV_ARG_I, EV_ARG_LINE, EV_REC_CANONICAL,
EV_SOCKET_SEND, EV_XSTRDUP.
Ltac kw_ev_spill_facts :=
repeat match goal with |- context [rec_spill_frees ?r] =>
lazymatch goal with _ : 0 <= rec_spill_frees r |- _ => fail | _ => pose proof (rec_spill_frees_nonneg_loc r) end end.
Lemma ev_vr_nonneg_loc : forall R D, 0 <= ev_vr R D.
Proof.
intros R D. unfold ev_vr.
destruct (Verbs.receive atoi_a D) as [st af].
destruct (VerbsRun.run_step reply_code_a R st) as [[R1 x] q].
unfold ev_route, ev_step, ev_call, ev_after.
kw_ev_unfold; kw_ev_unfold; kw_ev_unfold.
repeat match goal with |- context [match ?e with _ => _ end] => destruct e end;
kw_ev_spill_facts; lia.
Qed.
Lemma ev_send_nonneg_loc : forall R D, 0 <= EV_SEND_MESSAGE R D.
Proof.
intros R D. unfold EV_SEND_MESSAGE, EV_REC_CLEAR.
pose proof (ev_args_nonneg_loc R). pose proof (ev_vr_nonneg_loc (RecModel.rec_clear R) D). lia.
Qed.
Lemma ev_rt_nonneg_loc : forall R ws, 0 <= EV_CHECK_ROUND_TRIP R ws.
Proof.
intros R ws. unfold EV_CHECK_ROUND_TRIP, EV_REC_CALLS_COPY, EV_XSTRDUP, EV_JOINED.
pose proof (ev_args_nonneg_loc R). pose proof (ev_send_nonneg_loc R (join_sp ws)). lia.
Qed.
Lemma ev_msgs_nonneg_loc : forall f R l, 0 <= fst (ev_msgs f R l).
Proof.
induction f as [|f IH]; intros R l; [cbn; lia|].
destruct l as [|b l]; [cbn; lia|]. cbn [ev_msgs].
match goal with |- context [ev_msgs f ?R1 ?l1] => pose proof (IH R1 l1) as Hk; destruct (ev_msgs f R1 l1) as [k Rf] end.
cbn [fst] in Hk |- *.
match goal with |- context [EV_SEND_MESSAGE ?a ?b] => pose proof (ev_send_nonneg_loc a b) end.
match goal with |- context [EV_CHECK_ROUND_TRIP ?a ?b] => pose proof (ev_rt_nonneg_loc a b) end.
unfold EV_CHECK_REPLY, EV_CHECK_ARITY, EV_CHECK_WORDS, EV_JOINED, EV_CHECK_REFUSAL, EV_SUP_REPLY_CODE.
lia.
Qed.
Lemma ev_from_nonneg_loc : forall f R l, 0 <= ev_from f R l.
Proof.
intros f R l. unfold ev_from, EV_REC_CLEAR. pose proof (ev_msgs_nonneg_loc f R l).
pose proof (ev_args_nonneg_loc (snd (ev_msgs f R l))). lia.
Qed.
(* the rest of the budget after check_words: check_refusal's, check_round_trip's and the passes left *)
Lemma kw_rest_nonneg_loc : forall R ws f l,
  0 <= EV_CHECK_REFUSAL + EV_CHECK_ROUND_TRIP R ws + ev_from f R l.
Proof.
intros R ws f l. pose proof (ev_rt_nonneg_loc R ws). pose proof (ev_from_nonneg_loc f R l).
unfold EV_CHECK_REFUSAL, EV_SUP_REPLY_CODE. lia.
Qed.

(* the joined line's length is a length *)
Lemma join_need_nonneg_loc : forall ws, 0 <= join_need ws.
Proof. induction ws as [|w ws IH]; cbn [join_need fold_right]; [lia|]. unfold join_need in IH. lia. Qed.
(* check_words' meter: one malloc of at most 32,784 bytes and one free, so at most the walk's unit LT_U *)
Lemma kw_xm_le_loc : forall MT, ameter_laws MT -> forall ws, join_need ws + 1 <= 8194 ->
  0 <= XM_CHECK_WORDS MT ws <= LT_U MT.
Proof.
intros MT MTL ws Hj. pose proof (join_need_nonneg_loc ws) as H0.
pose proof (mo_malloc_nonneg MT MTL (join_need ws + 1) ltac:(lia)) as H1.
pose proof (mo_malloc_mono MT MTL (join_need ws + 1) 32784 ltac:(lia)) as H2.
pose proof (mo_free_nonneg MT MTL) as H3.
unfold XM_CHECK_WORDS, XM_JOINED, LT_U. lia.
Qed.

(* the three words blocks of a message of at most 8192 bytes sum to at most LT_WORDSB *)
Lemma kw_wblocks_bsum_loc : forall D text copy arr,
  0 <= StrFun.strnlen_res (Z.of_nat (length D)) D <= 8192 -> bsum (lt_wblocks D text copy arr) <= LT_WORDSB.
Proof.
intros D text copy arr. unfold lt_wblocks, LT_WORDSB, SlotSpec.arr_size. cbv zeta.
generalize (StrFun.strnlen_res (Z.of_nat (length D)) D). intros L0 HL. cbn [bsum snd].
pose proof (Z.div_mod L0 2 ltac:(lia)). pose proof (Z.mod_pos_bound L0 2 ltac:(lia)). lia.
Qed.

(* ---- live blocks ---- *)
(* distinct live blocks: the allocator's blocks are pairwise disjoint and each covers at least one byte
   (the send_message walk, send_message_s3.v nodup_blocks) *)
Lemma nodup_blocks_loc : forall l : list (Z * Z), Forall (fun b => 0 <= snd b) l ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x l IH]; cbn [map pairwise]; intros Hn Hp; [constructor|].
destruct Hp as [Hf Hp]. inversion Hn as [|? ? Hx Hl]; subst. constructor; [|exact (IH Hl Hp)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf _ (in_map (fun b => (fst b, req_size (snd b))) _ _ Hin)).
pose proof (req_size_pos (snd x) Hx) as [H1 _]. unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma bsum_le_loc : forall (M : Z) (l : list (Z * Z)), Forall (fun b => snd b <= M) l ->
  bsum l <= Z.of_nat (length l) * M.
Proof.
intros M. induction l as [|b l IH]; intros HF; cbn [bsum length]; [lia|].
inversion HF as [|? ? Hb Hl]; subst. pose proof (IH Hl) as H1. rewrite Nat2Z.inj_succ. nia.
Qed.
Lemma bsum_concat_le_loc : forall (M : Z) (Ls : list (list (Z * Z))), 0 <= M ->
  Forall (fun P => (length P <= 6)%nat /\ Forall (fun b => snd b <= M) P) Ls ->
  bsum (concat Ls) <= 6 * M * Z.of_nat (length Ls).
Proof.
intros M Ls HM. induction Ls as [|P Ls IH]; intros HF; cbn [concat bsum length]; [lia|].
inversion HF as [|? ? HPx Hl]; subst. destruct HPx as [HP6 HPM]. rewrite bsum_app.
pose proof (IH Hl) as H1. pose proof (bsum_le_loc M P HPM) as H2.
assert (H3 : Z.of_nat (length P) * M <= 6 * M) by (apply Z.mul_le_mono_nonneg_r; lia).
rewrite Nat2Z.inj_succ. nia.
Qed.
Lemma bsum_oblk_le_loc : forall (M : Z) (o : option (Z * Z)),
  (forall pn, o = Some pn -> snd pn <= M) -> 0 <= M -> bsum (oblk o) <= M.
Proof. intros M [pn|] H HM; cbn [oblk bsum]; [specialize (H pn eq_refl); lia | lia]. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a frame word read through the ASan view is the same 8-byte field *)
Lemma aval_of_rdword_loc : forall (segs : list Segment) H mem a v,
  rdword (aview segs H mem) a = Some v -> aval_mem (aview segs H mem) a 8 v.
Proof.
intros segs H mem a v Hw k Hk.
pose proof (val_mem_of_rdword segs H mem a v Hw k Hk) as Hb.
unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, YG0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* a callee-saved register a call keeps *)
Lemma aregs_pres_at_loc : forall (r1 r2 : bvmap 5 word) (x : bv 5), aregs_preserved r1 r2 ->
  acallee_saved (bv_unsigned x) -> getr r2 x = getr r1 x.
Proof.
intros r1 r2 x HP Hx. pose proof (HP (bv_unsigned x) Hx) as H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* the program statics are image bytes below the stack, and none is the sink token's byte 0 *)
Lemma kw_PG_range_loc : forall a, inFP cmd_PG a -> A_G_REC <= a < A_G_QUITTING + 4.
Proof.
intros a (r & Hr & Ha). unfold cmd_PG in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in *; lia.
Qed.
Lemma kw_PG_nosink_loc : ~ YI16.sink_open_fp cmd_PG.
Proof.
intros (r & Hr & Ha). unfold cmd_PG in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in *; lia.
Qed.

(* ---- the recorder's blocks between two messages: at most 2 calls of at most 6 arguments, the answer and the
   reply, each of at most LMAX + 2 bytes (lt_rec), so their sizes sum to at most LT_RECB ---- *)
Lemma lt_rec_bsum_loc : forall B ly S rd R O,
  rec_repA B ly S rd R O -> List.NoDup O -> (length (r_calls R) <= 2)%nat -> r_spill R = (0, []) ->
  bsum O <= LT_RECB.
Proof.
intros B ly S rd R O (Q & HREP & HO) HND Hlen Hsp.
destruct HREP as (_ & _ & _ & HCALLS & HANS & HREPL & _ & HOWN).
destruct HCALLS as (_ & HlenQ & _ & HC & HSP & _).
destruct HOWN as (HNDQ & _).
assert (HNDQ' : List.NoDup (lay_blocks Q))
  by exact (List.NoDup_map_inv fst _ (proj1 (stdpp.base.NoDup_ListNoDup _) HNDQ)).
assert (HPerm : Permutation O (lay_blocks Q))
  by (apply Permutation.NoDup_Permutation; [exact HND | exact HNDQ' | exact HO]).
rewrite (bsum_perm _ _ HPerm). unfold lay_blocks. rewrite !bsum_app.
assert (HM : 0 <= LMAX + 2) by (unfold LMAX; lia).
(* the calls *)
assert (HCF : Forall (fun P => (length P <= 6)%nat /\ Forall (fun b => snd b <= LMAX + 2) P) (l_calls Q)).
{ apply Forall_forall. intros P HP. apply In_nth_error in HP as (i & Hi).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- HlenQ; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
  destruct (HC i c P Ec Hi) as (HA & _). destruct HA as (_ & H6 & HlP & _ & _ & _ & HK).
  split; [lia|]. apply Forall_forall. intros pn Hpn. apply In_nth_error in Hpn as (kk & Hk).
  assert (Hk' : (kk < length (snd c))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd c) kk) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (HK kk s pn Es Hk) as (_ & _ & _ & HS & _). lia. }
pose proof (bsum_concat_le_loc (LMAX + 2) (l_calls Q) HM HCF) as Hcalls.
(* the spill holds no call *)
assert (Hspill : l_spill Q = []).
{ destruct HSP as (_ & _ & HlS & _). rewrite Hsp in HlS. cbn [snd length] in HlS. destruct (l_spill Q); [reflexivity | discriminate]. }
rewrite Hspill. cbn [bsum].
(* the answer and the reply *)
assert (Ha : bsum (oblk (l_answer Q)) <= LMAX + 2).
{ apply bsum_oblk_le_loc; [|exact HM]. intros pn Hpn. rewrite Hpn in HANS.
  destruct (r_answer R) as [x|]; [|destruct HANS]. destruct HANS as (_ & _ & _ & HS & _). lia. }
assert (Hr : bsum (oblk (l_reply Q)) <= LMAX + 2).
{ apply bsum_oblk_le_loc; [|exact HM]. intros pn Hpn. rewrite Hpn in HREPL.
  destruct (r_reply R) as [x|]; [|destruct HREPL]. destruct HREPL as (_ & _ & _ & _ & _ & HS & _). lia. }
rewrite HlenQ in Hcalls. unfold LT_RECB.
assert (HL : Z.of_nat (length (r_calls R)) <= 2) by lia.
revert Hcalls Ha Hr HL. generalize (Z.of_nat (length (r_calls R))). unfold LMAX. intros z Hcalls Ha Hr HL. nia.
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).

(* ---- the symbolic state at 0x86950 (LO_K2): every register its own atom, no memory region (the two
   instructions to the call, addi a0,sp,120 and jal check_words, read and write no memory), no fact ---- *)
Definition kw_ss : sstate := mkSS LO_K2 sr_atoms [] None (mkFacts [] [] []).
Definition kw_Bx : sv := SLit 0x7fff8000.
Definition kw_span : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
Lemma kw_seed_loc : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) kw_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K2)) mem (seg_rom SEGS))) /\
  sh_ok SEGS kw_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem. split; [|constructor].
unfold kw_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn. exact I.
- cbn. repeat split.
Qed.
End f.
End d.
